# import .core.string
        
using import enum

enum Instruction
    Char : i8
    Jump : i32
    Choice : i32
    Call : i32
    Commit : i32
    # tags aren't movable so I did this to be able to put them into an array. Will probably fix it
        on the enum module side.
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

fn interpreted-match? (input program)
    returning bool i32

    let input-length = (countof input)
    let program-length = (countof program)

    using import struct
    struct OpStack plain
        _data_ : (array i32 400)
        stack-pointer : i32
        inline empty? (self)
            self.stack-pointer == 0 
        fn push (self value)
            #TODO: what if the stack is full?
            imply value i32
            self.stack-pointer += 1
            self._data_ @ self.stack-pointer = value
        fn pop (self)
            #TODO: what do we do if the stack is empty?
            if ('empty? self)
                error "stack was empty but tried to pop"
            let elem = (self._data_ @ self.stack-pointer)
            self.stack-pointer -= 1
            elem
        fn peek (self)
            (self._data_ @ self.stack-pointer)
    local v-stack = (OpStack)
    'push v-stack 0 # instruction
    'push v-stack 0 # input position
        
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
                input-position program-index = 
                0              0
            )
            if (input-position == input-length)
                merge match? false 0

            let current-character = (input @ input-position)
            let instruction =
                if (program-index >= 0) 
                    dupe (deref (program @ program-index))
                else 
                    dupe Instruction.Fail 
                    
            include (import C) "stdio.h"
            print "current input: " current-character
            print "stack: "
            for n in (range 0 v-stack.stack-pointer)
                if (n == (v-stack.stack-pointer - 1))
                    sc_write "--> " 
                else
                    sc_write "    "
                if (n % 2 == 0)
                    sc_write ((tostring (deref (program @ n))) .. "\n")
                else
                    sc_write (((input @ n) as string) .. "\n")
            C.getchar;

            dispatch instruction
            case Fail ()
                let initial-position = (deref ('pop v-stack))
                let return-address = (deref ('pop v-stack))
                if ('empty? v-stack)
                    # start of the pattern
                    'push v-stack 0
                    'push v-stack (initial-position + 1)
                    _ (initial-position + 1) 0
                else
                    _ initial-position return-address

            case Char (c)
                # if the character match succeeds, we want to advance both the input and the program
                if (c == current-character)
                    _ (input-position + 1) (program-index + 1)
                else
                    _ input-position -1
            case Call (relative-address)
                'push v-stack (program-index + 1)
                'push v-stack input-position
                _ input-position (program-index + (deref relative-address))
            case Jump (relative-address)
                _ input-position (program-index + (deref relative-address))
            case End ()
                merge match? true input-position
            case Choice (relative-address)
                let addr = (deref relative-address)
                'push v-stack (program-index + addr)
                'push v-stack input-position
                _ input-position (program-index + 1)
            case Return ()
                let original-input-position = (deref ('pop v-stack))
                let next-instruction = ((deref ('pop v-stack)) + 1)
                _ original-input-position next-instruction
            case Commit (relative-address)
                let original-input-position = ('pop v-stack)
                'pop v-stack
                'push v-stack (program-index + relative-address)
                'push v-stack original-input-position
                _ input-position (program-index + 1)
            case Capture ()
                not-implemented "Capture"
            default
                not-implemented "Unknown"

spice char (c)
    let c = (c as string)
    let c = (char c)
    `c
run-stage;
    
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
    # local abc-pattern =
    #     arrayof Instruction
    #         Instruction.Char (char "a")
    #         Instruction.Char (char "b")
    #         Instruction.Char (char "c")
    #         Instruction.End none
    # print "pattern: `abc`"
    # test-match "aaaabcdef" abc-pattern true
    # test-match "aaaacdef" abc-pattern false
    # ordered choice
    # S <- ab / cd
    local ab/cd-pattern =
        arrayof Instruction
            Instruction.Choice      3 #L1
            Instruction.Call        5 #p1
            Instruction.Commit      3 #L2
            # label: L1
            Instruction.Call        6 #p2
            dupe Instruction.End         
            # L2
            dupe Instruction.Fail
            # p1
            Instruction.Char        (char "a")
            Instruction.Char        (char "b")
            dupe Instruction.Return     
            # p2
            Instruction.Char        (char "c")
            Instruction.Char        (char "d")
            dupe Instruction.Return      
            # label: l2

    print "pattern: `ab / cd`"
    test-match "aaaabcdef" ab/cd-pattern true
    test-match "aaaacdef" ab/cd-pattern true
    test-match "aaaacef" ab/cd-pattern false
    test-match "bbbbdef" ab/cd-pattern false
    test-match "bbcbdef" ab/cd-pattern false
