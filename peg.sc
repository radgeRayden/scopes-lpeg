spice const-char (c)
    `[(char (c as string))]
run-stage;

inline char (c)
    static-if (constant? c)
        const-char c
    else
        char c

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
            
    label print-line
        loop (leftL rightL = left-str right-str)
            let left-line left-remainder = (make-column-line leftL) 
            let right-line right-remainder = (make-column-line rightL)
            sc_write left-line
            sc_write "\t"
            sc_write right-line
            sc_write "\n"

            if (((countof left-remainder) == 0) and ((countof right-remainder) == 0)) 
                merge print-line
            _ left-remainder right-remainder

# tag definitions for identifying the machine status
let :no-backtrack = -1  
let :instruction-fail = -1

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
        ? (program-index == :instruction-fail) "--> " "    "
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
                    if (stack-value != :no-backtrack)
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

using import struct
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

                
using import enum

enum Instruction
    Char : i8
    Jump : i32
    Choice : i32
    Call : i32
    Commit : i32
    Return
    Capture
    End
    Fail

typedef+ Instruction
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
        default
            ""

#forward declaration because of overload with optional parameter
fn interpreted-match? (input program debug?)

fn... interpreted-match? 
case (input, program,)
    interpreted-match? input program false
case (input, program, debug? : bool,)
    returning bool i32

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
        
    label match?
        loop (
                input-position match-start program-index = 
                0              0           0
            )
            if debug?
                debug-print-stack input input-position program program-index v-stack

            # exit condition for complete failure
            if (input-position == input-length)
                merge match? false 0

            let current-character = (input @ input-position)
            let instruction =
                if (program-index >= 0) 
                    dupe (deref (program @ program-index))
                else 
                    dupe Instruction.Fail 
                    
            inline save-state (input-position program-index)
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
                        if (saved-position != :no-backtrack)
                            break saved-position saved-position saved-instruction

            case Char (c)
                # if the character match succeeds, we want to advance both the input and the program
                if (c == current-character)
                    _ (input-position + 1) match-start (program-index + 1)
                else
                    _ input-position match-start :instruction-fail

            case Call (relative-address)
                # so when this returns, it goes to the next instruction
                save-state :no-backtrack (program-index + 1)
                _ input-position match-start (program-index + (deref relative-address))

            case Jump (relative-address)
                _ input-position match-start (program-index + (deref relative-address))

            case End ()
                merge match? true input-position

            case Choice (relative-address)
                let addr = (deref relative-address)
                save-state input-position (program-index + addr)
                _ input-position match-start (program-index + 1)

            case Return ()
                let call-site next-instruction = (load-state)
                _ call-site match-start next-instruction

            case Commit (relative-address)
                #TODO: clean this; the paper also mentions an optimization to get rid of
                       the useless pop so maybe I'll just wait until I get there and do it
                       right.
                let original-input-position = ('pop v-stack)
                'pop v-stack
                'push v-stack (program-index + relative-address)
                'push v-stack original-input-position
                _ input-position match-start (program-index + 1)

            case Capture ()
                not-implemented "Capture"
                
            default
                not-implemented "Unknown"
    
fn compiled-match? (input size)
    let input-length = size
    label match?
        loop (input-position = 0)
            if (input-position == input-length) 
                merge match? false 0
            let ch = (input @ input-position)
            label start
                if (ch != (char "a"))
                    merge start
                let input-position = (input-position + 1)
                let ch = (input @ input-position)

                if (ch != (char "b"))
                    merge start
                let input-position = (input-position + 1)
                let ch = (input @ input-position)

                if (ch != (char "c"))
                    merge start
                let input-position = (input-position + 1)
                let ch = (input @ input-position)

                if (ch != (char "d"))
                    merge start
                let input-position = (input-position + 1)
                let ch = (input @ input-position)

                if (ch != (char "e"))
                    merge start
                let input-position = (input-position + 1)
                let ch = (input @ input-position)

                if (ch == (char "f"))
                    merge match? true (input-position + 1)
            _ (input-position + 1)

let ch-sequence =
    deref 
        @
            bitcast ("abcdef" as rawstring) (pointer u64)
run-stage;
    
fn compiled-matchv2? (input size) 
    let input-length = size
    let pattern-length = 6
    loop (match? input-position = false 0)
        # this both checks for total failure and ensures we don't read garbage
        if (input-position > (size - pattern-length)) 
            break false 0
        let ch-pointer = (& (input @ input-position))
        let chunk =
            deref 
                @
                    bitcast ch-pointer (pointer u64)
        
        let result = (chunk == ch-sequence)
        if result
            break true (input-position + 1)
        _ false (input-position + 1)


static-if main-module?
    using import testing
    inline test-match (input pattern expected)
        let result = (interpreted-match? input pattern)
        print "input: " input "expected: " expected ", result: " result
        test (result == expected )

    # literal match
    # S <- abc
    local abc-pattern =
        arrayof Instruction
            Instruction.Char (char "a")
            Instruction.Char (char "b")
            Instruction.Char (char "c")
            dupe Instruction.End 
    # print "pattern: `abc`"
    # test-match "aaaabcdef" abc-pattern true
    # test-match "aaaacdef" abc-pattern false
    # ordered choice
    # 
      S  <- p1 / p2
      p1 <- ab
      p2 <- cd
    local ab/cd-pattern =
        arrayof Instruction                             
            Instruction.Choice      3  #L1              # 0
            Instruction.Call        4  #p1              # 1
            Instruction.Commit      9  #L2              # 2
            # label: L1                                 
            Instruction.Call        5  #p2              # 3
            Instruction.Jump        7                   # 4
            # p1                             
            Instruction.Char        (char "a")          # 5
            Instruction.Char        (char "b")          # 6
            dupe Instruction.Return                     # 7
            # p2                             
            Instruction.Char        (char "c")          # 8
            Instruction.Char        (char "d")          # 9
            dupe Instruction.Return                     # 10
            # label: l2
            dupe Instruction.End                        # 11

    print "pattern: `ab / cd`"
    test-match "aaaabcdef" ab/cd-pattern true
    test-match "aaaacdef" ab/cd-pattern true
    test-match "aaaacef" ab/cd-pattern false
    test-match "bbbbdef" ab/cd-pattern false
    test-match "bbcbdef" ab/cd-pattern false
