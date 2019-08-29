using import enum
using import struct
using import Array

spice const-char (c)
    `[(char (c as string))]

spice unique-type (T i)
    let T = (T as type)
    let i = (i as i32)
    `[('unique-type T i)]
run-stage;

inline char (c)
    static-if (constant? c)
        const-char c
    else
        char c

inline pointer* (T)
    mutable (pointer T)

fn print-double-column (left-str right-str)
    # each column is 40 chars wide, the separator occupies 3 chars
    fn make-column-line (str)
        #   returns a 40 character wide string + padding if necessary, and the rest of
            the original string.
        local line : (array i8 40)
        # space init
        for i in (range 40)
            (line @ i) = (char " ") 
            
        let rest =
            fold (rest counter = str 0) for c in str
                # we necessarily break on new line even if it's still too narrow
                if ((c == (char "\n")) or (counter == 40))
                    break rest counter
                else
                    (line @ counter) = c          
                    _ (rslice rest 1) (counter + 1)
        _ (string &line 40:usize) rest
            
    loop (leftL rightL = left-str right-str)
        let left-line left-remainder = (make-column-line leftL) 
        let right-line right-remainder = (make-column-line rightL)
        sc_write left-line
        sc_write "\t"
        sc_write right-line
        sc_write "\n"

        if (((countof left-remainder) == 0) and ((countof right-remainder) == 0)) 
            break;
        _ left-remainder right-remainder

# tag definitions for identifying the machine status
enum MatchStatus plain
    # used as program index if an instruction has failed
    Failure = -1
    # pushed on the stack to mark that we shouldn't backtrack if stepping out of a call
    PendingCall = -1

fn debug-print-stack (input input-position program program-index stack)
    #   debug printing:
        on the left column we'll print the stack, and on the right the program and a pointer to the current
        instruction.
    include (import C) "stdio.h"
    print "input position: "
    if ((countof input) <= 100)
        local input-indicator-display : (array i8 100)
        # space init
        for i in (range 100)
            (input-indicator-display @ i) = (char " ") 
        for i in (range (countof input))
            if (i == input-position)
                (input-indicator-display @ i) = (char "^")
                break;
        print input
        print (string &input-indicator-display 100)
    else 
        print "input too big to be displayed"
    print-double-column "STACK" "INSTRUCTIONS"
    # this ad-hoc line indicates whether we are in a fail state.
    let fail-prefix = 
        ? (program-index == MatchStatus.Failure) "--> " "    "
    print-double-column "" (.. fail-prefix ".x. FAIL")
    let inspector-display-size = (max (stack.stack-pointer as i32) ((countof program) as i32))
    for i in (range inspector-display-size)
        let stack-line =
            if (i <= stack.stack-pointer)
                let stack-value = (stack._data_ @ i)
                if (i % 2 == 0)
                    # even stack entries are instructions
                    let ins = (deref (program @ stack-value))
                    .. "[" (tostring stack-value) "] "(tostring ins) ", " ('value->string ins)
                else
                    # and odd are input positions
                    if (stack-value != MatchStatus.PendingCall)
                        .. "input [" (tostring stack-value) "] -> " ((input @ stack-value) as string)
                    else
                        "no backtrack - pending call"
            else
                ""
        let program-line =
            if (i < (countof program))
                let prefix = (? (i == program-index) "--> " "    ")
                let ins = (deref (program @ i))
                .. prefix "." (tostring i) ". "(tostring ins) ", " ('value->string ins)
            else
                ""
        print-double-column stack-line program-line
    # I decided to always pause on step through for simplicity
    C.getchar;

# a simple stack implementation to hold the choices from the matcher
struct Stack plain
    _data_ : (array i32 400)
    stack-pointer : i32 = -1

    inline empty? (self)
        self.stack-pointer == -1 

    fn push (self value)
        #TODO: what if the stack is full?
        imply value i32
        self.stack-pointer += 1
        (self._data_ @ self.stack-pointer) = value
        ;

    fn pop (self)
        if ('empty? self)
            hide-traceback;
            error "stack was empty but tried to pop"
        let elem = (self._data_ @ self.stack-pointer)
        self.stack-pointer -= 1
        elem

    inline... peek 
    case (self : this-type,)
        (self._data_ @ self.stack-pointer)
    case (self : this-type, index : i32)
        (self._data_ @ index)

    fn poke (self index new-value)
        (self._data_ @ index) = new-value
        ;

    fn swap-head (self new-value)
        'poke self self.stack-pointer new-value
        ;

enum CaptureType plain
    Text
    Position
    
# L versions of instructions have a Label operand, they are substituted by the
  builder with canonical relative addresses
enum Instruction
    Char : i8
    Jump : i32
    JumpL : string
    Choice : i32
    ChoiceL : string
    Call : i32
    CallL : string
    Commit : i32
    CommitL : string
    Label : string
    Capture : (tuple (position = i32) (capture-type = CaptureType))
    Return
    End
    Fail

    fn __tostring (self)
        dispatch self
        case Char (c)
            "Char"
        case Jump (pos)
            "Jump"
        case Choice (addr)
            "Choice"
        case Call (addr)
            "Call"
        case Commit (addr)
            "Commit"
        case Return ()
            "Return"
        case Capture ()
            "Capture"
        case End ()
            "End"
        case Fail ()
            "Fail"
        default
            "unknown"
    fn value->string (self)
        dispatch self
        case Char (c)
            (c as string)
        case Jump (pos)
            (tostring pos)
        case Choice (addr)
            (tostring addr)
        case Call (addr)
            (tostring addr)
        case Commit (addr)
            (tostring addr)
        case Capture (capture-info)
            .. "{" (repr capture-info.position) ", " (repr capture-info.capture-type) "}"
        default
            ""

# we generate an specialization here so debug stuff doesn't get 
    included if debug? is false
@@ memo
inline make-interpreter-function (debug?)
    fn (input program)
        struct PatternCapture
            # where in the input to start capturing
            capture-start : i32
            # index of the first instruction relevant to the capture.
              The 'program' will be played back to record the capture after the matching process,
              stopping where the corresponding end instruction is found.
            program-index : i32

        let CaptureList = (Array PatternCapture)
        enum ProcessedCapture
            Text : string
            Position : i32
        let ProcessedCaptureList = (Array ProcessedCapture)
            
        returning bool i32 (unique-type ProcessedCaptureList 0)

        let input-length = (countof input)
        let program-length = (countof program)
        local v-stack = (Stack)
            
        # LPEG parsing machine, as per Roberto's paper (A Text Pattern-Matching Tool based on Parsing Expression Grammars, 2008)
          Registers:
          current instruction:
                i32 meaning the index of the next instruction to be executed (or a special fail code, signaling the need to backtrack)
          current subject position:
                i32 keeps track of at which point of the input string we are looking for matches.
          stack index
                 
        inline not-implemented (instruction)
            hide-traceback;
            error ("Invalid or non implemented parsing instruction: " .. instruction)
            
        let suceeded? end-position =
            loop (
                    input-position match-start program-index = 
                    0              0           0
                )
                static-if debug?
                    debug-print-stack 
                        input 
                        input-position 
                        program 
                        program-index 
                        v-stack

                let fail-instruction = (view (Instruction.Fail))
                let instruction =
                    if (program-index >= 0) 
                        (deref (program @ program-index))
                    else 
                        fail-instruction

                # exit condition for complete failure
                if 
                    and
                        (input-position == input-length)
                        # this avoids mistakenly matching false when the end of the pattern coincides with the end of the input.
                          it's cheap because of the ordered `and` and the string comparison boils down to a hash comparison.
                        (tostring instruction) != (tostring (Instruction.End))
                    print "exiting"
                    break false 0

                inline save-state (input-position program-index)
                    input-position := input-position as i32
                    program-index := program-index as i32
                    'push v-stack program-index
                    'push v-stack input-position

                inline load-state ()
                    let saved-position saved-instruction =
                        (deref ('pop v-stack))
                        (deref ('pop v-stack))
                    _ saved-position saved-instruction

                dispatch instruction
                case Fail ()
                    loop ()
                        # if there aren't any choices left to pursue, advance input
                        if ('empty? v-stack)
                            break (match-start + 1) (match-start + 1) 0
                        else
                            let saved-position saved-instruction = (load-state)
                            # discard all pending calls - drops a call if there's no choice left in it
                            if (saved-position != MatchStatus.PendingCall)
                                break saved-position saved-position saved-instruction

                case Char (c)
                    # if the character match succeeds, we want to advance both the input and the program
                    let current-character = (input @ input-position)
                    if (c == current-character)
                        _ (input-position + 1) match-start (program-index + 1)
                    else
                        _ input-position match-start (MatchStatus.Failure as i32)

                case Call (relative-address)
                    # so when this returns, it goes to the next instruction
                    save-state MatchStatus.PendingCall (program-index + 1)
                    _ input-position match-start (program-index + (deref relative-address))

                case Jump (relative-address)
                    _ input-position match-start (program-index + (deref relative-address))

                case End ()
                    break true input-position

                case Choice (relative-address)
                    let addr = (deref relative-address)
                    save-state input-position (program-index + addr)
                    _ input-position match-start (program-index + 1)

                case Return ()
                    let _disc next-instruction = (load-state)
                    _ input-position match-start next-instruction

                case Commit (relative-address)
                    load-state; # discards the top entry on the stack
                    _ input-position match-start (program-index + relative-address)

                case Capture (capture-info)
                    let capture-type = capture-info.capture-type
                    # for now we'll only deal with position captures and simple string captures

                    not-implemented "Capture"


                default
                    not-implemented "Unknown"
        local processed-capture-list : ProcessedCaptureList
        _ suceeded? end-position (deref processed-capture-list)

# and then the actual call handles the debug param
inline... interpreted-match? 
case (input, program, debug? : bool)
    (make-interpreter-function debug?) input program
case (input, program,)
    (make-interpreter-function false) input program
    
fn link-pattern (instructions)
    # TODO:
        - error if you define the same label twice
    let LabelList =
        Array 
            tuple 
                name = string
                index = i32
    local labels = (LabelList)
    fold (program-index = 0) for instruction in instructions
        dispatch instruction
        case Label (name)
            'append labels (tupleof (name = name) (index = program-index))
            continue program-index
        default;
        program-index + 1

    inline retrieve-label-position (id)
        for label* in labels
            if ('match? label*.name id)
                return label*.index
        error "label not found"
        
    local pattern = ((Array Instruction))
    fold (program-index = 0) for instruction in instructions
        dispatch instruction
        case JumpL (label-id)
            let label-position = (retrieve-label-position label-id)
            let label-distance = (label-position - program-index)
            'append pattern (Instruction.Jump label-distance)
        case ChoiceL (label-id)
            let label-position = (retrieve-label-position label-id)
            let label-distance = (label-position - program-index)
            'append pattern (Instruction.Choice label-distance)
        case CallL (label-id)
            let label-position = (retrieve-label-position label-id)
            let label-distance = (label-position - program-index)
            'append pattern (Instruction.Call label-distance)
        case CommitL (label-id)
            let label-position = (retrieve-label-position label-id)
            let label-distance = (label-position - program-index)
            'append pattern (Instruction.Commit label-distance)
        case Label (name)
            continue program-index
        default
            'append pattern (dupe instruction)
        program-index + 1
    (deref pattern)


static-if main-module?
    using import testing
    inline test-match (input pattern expected...)
        let expect-match? expected-position = expected...
        let expected-position =
            static-if (none? expected-position) 
                0
            else
                expected-position
            
        let matches? position = (interpreted-match? input pattern)
        print 
            \ "input: " (repr input)
            \ " \texpected:" 
            \ (.. (repr expect-match?) ", " (repr expected-position))
            \ " \tresult:"
            \ (.. (repr matches?) ", " (repr position))
        test 
            and
                (expect-match? == matches?)
                (expected-position == position)

    # literal match
    sc_write 
        """"pattern: 
                S <- abc
    print "---------------------------------------------------"
    local abc-pattern =
        arrayof Instruction
            Instruction.Char (char "a")
            Instruction.Char (char "b")
            Instruction.Char (char "c")
            Instruction.End;
    test-match "aaaabcdef" abc-pattern true 6
    test-match "aaaacdef" abc-pattern false

    sc_write "\n\n\n"

    # ordered choice
    sc_write
        """"pattern: 
                S  <- p1 / p2
                p1 <- ab
                p2 <- cd
    print "---------------------------------------------------"
    let ab/cd-pattern =
        link-pattern
            local ins =
                arrayof Instruction                             
                    Instruction.ChoiceL     "L1"                # 0
                    Instruction.CallL       "p1"                # 1
                    Instruction.CommitL     "L2"                # 2

                    Instruction.Label       "L1"
                    Instruction.CallL       "p2"                # 3
                    Instruction.JumpL       "L2"                # 4

                    Instruction.Label       "p1"
                    Instruction.Char        (char "a")          # 5
                    Instruction.Char        (char "b")          # 6
                    Instruction.Return;                         # 7

                    Instruction.Label       "p2"
                    Instruction.Char        (char "c")          # 8
                    Instruction.Char        (char "d")          # 9
                    Instruction.Return;                         # 10

                    Instruction.Label       "L2"
                    Instruction.End;                            # 11


    for ins in ab/cd-pattern
        print ins ('value->string ins)
    sc_write "\n"
    test-match "aaaabcdef" ab/cd-pattern true 5
    test-match "aaaacdef" ab/cd-pattern true 6
    test-match "aaaacef" ab/cd-pattern false
    test-match "bbbbdef" ab/cd-pattern false
    test-match "bbcbdef" ab/cd-pattern false
