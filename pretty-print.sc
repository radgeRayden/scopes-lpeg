fn find-first-printable (str start)
    local last-code-start = 0:usize
    loop (index escaping? last-code = start false "")
        let size = (countof str)
        label escape-check
            # first thing is avoiding we run past the EOS
            if (index >= size)
                break (_ size last-code)
            let current-char = (str @ index)
            # 1. find start of escape sequence (char "\x1b")
            if (not escaping?)
                if (current-char == 0x1b)
                    last-code-start = index
                    merge escape-check (_ (index + 1) true last-code)
            else
                # 2. skip as long as we don't find the escape code finalizer `m`
                let keep-escaping? = (not (current-char == (char "m")))
                if keep-escaping?
                    merge escape-check (_ (index + 1) true last-code)
                else
                    merge escape-check (_ (index + 1) false (slice str last-code-start (index + 1)))
            # 3. if we're not escaping and no escape initializer was found, break at current index
            break (_ index last-code)

""""Returns a generator that iterates over every printable character, keeping track of 'active' ANSI escape codes.
inline filter-visible (str)
    let size = (countof str)
    Generator
        inline "start" ()
            find-first-printable str 0:usize
        inline "valid?" (index)
            index < size
        inline "at" (index last-escape-code)
            _ index last-escape-code
        inline "next" (index last-escape-code)
            let index escape-code = (find-first-printable str (index + 1))
            if (escape-code == "")
                _ index last-escape-code
            else
                _ index escape-code

fn printable-countof (str)
    fold (counter = 0:usize) for c in (filter-visible str)
        counter + 1

fn split-styled (str split-after)
    # check if parameters are valid 
    (imply str string)
    if (split-after > (printable-countof str))
        error "Tried to split at a position that is higher than the size of printable input."
    let ANSI-reset-code = "\x1b[0m"
    for printable-index index last-code in (enumerate (filter-visible str))
        # -1 here because of the difference between count and index; function uses count to conform to `slice`
        if (printable-index == (split-after - 1))
            if ((last-code == ANSI-reset-code) or (last-code == ""))
                # then we add one to convert back from index to count, same thought process below
                return (_ (lslice str (index + 1)) (rslice str (index + 1)))
            else
                let lstr rstr = 
                    lslice str (index + 1)
                    rslice str (index + 1)
                # edge case 1: right after the last character of the lstr, there's a reset that we didn't see
                if ((lslice rstr (countof ANSI-reset-code)) == ANSI-reset-code)
                    return   
                        _ (lstr .. ANSI-reset-code) (rslice rstr (countof ANSI-reset-code))
                else
                    return   
                        _
                            lstr .. ANSI-reset-code
                            last-code .. rstr
    _ "" ""
        
fn repeat-char (c n)
    local buf = (alloca-array i8 n)
    for i in (range n)
        buf @ i = c 
    string buf n

fn print-row (total-width separator columns...)
    let column-count = (va-countof columns...)
    let column-width = ((total-width / column-count) as usize)
    let separator-width = (printable-countof separator)
    loop (remainder... = columns...)
        local has-remainder? = false
        io-write! separator
        let remainder... = 
            va-map 
                inline (column-text)
                    let text-width = (printable-countof column-text)
                    if (text-width < column-width)
                        io-write! column-text 
                        io-write! (repeat-char (char " ") (column-width - text-width - separator-width))
                        io-write! separator
                        ""
                    else
                        has-remainder? = true
                        let current-line remainder = (split-styled column-text (column-width - separator-width))
                        io-write! current-line
                        io-write! separator
                        remainder
                    
                remainder...
        io-write! "\n"
        if (not has-remainder?)
            break;
        remainder...

fn run-tests ()
    using import testing

    inline test-escape-filtering (str styled-str)
        for i filtered-index in (enumerate (filter-visible styled-str))
            test ((str @ i) == (styled-str @ filtered-index))

    # simple filtering
    test-escape-filtering "abcde" (default-styler 'style-number "abcde")
    # concatenated styled strings
    test-escape-filtering
        .. "abcde" "abcde"
        .. (default-styler 'style-number "abcde") (default-styler 'style-function "abcde")

    # printable countof, returns count of string as if ANSI codes were stripped out (for calculating width)
    test 
        (printable-countof (default-styler 'style-number "abcde")) == (countof "abcde")

    # styled string splitting, should preserve style between slices, without bleeding (ie. resets style if necessary)
    let lstr rstr = (split-styled (default-styler 'style-number "abcde") 2)
    test 
        (lstr == (default-styler 'style-number "ab"))
        .. "\nlstr is: " (repr lstr) ", but expected: " (repr (default-styler 'style-number "ab"))
    test 
        (rstr == (default-styler 'style-number "cde"))
        .. "\nrstr is: " (repr rstr) ", but expected: " (repr (default-styler 'style-number "cde"))
    let lstr rstr = 
        split-styled 
            ..
                default-styler 'style-number "abcde"
                default-styler 'style-function "abcde"
            (countof "abcde")
    test 
        (lstr == (default-styler 'style-number "abcde")) 
        .. "\nlstr is: " (repr lstr) ", but expected: " (repr (default-styler 'style-number "abcde"))
    test 
        (rstr == (default-styler 'style-function "abcde")) 
        .. "\nrstr is: " (repr rstr) ", but expected: " (repr (default-styler 'style-function "abcde"))
    # split at the end
    let lstr rstr =
        split-styled (default-styler 'style-function "abcde") (countof "abcde")
    test (lstr == (default-styler 'style-function "abcde"))
    test (rstr == "")

static-if main-module?
    run-tests;
    print ("  " .. (repeat-char (char "-") 119))
    print-row 120 " | " "HeaderA" "HeaderB" "HeaderC"
    io-write! " |"
    io-write! (repeat-char (char "-") 119)
    io-write! "| \n"
    print-row 120 " | " (default-styler 'style-number "PropertyAkashdklashdlaksjdhalskhdsalkdhalkjsdhakljdhakljdhaskljdhakjdhslakjdh") "PropertyB" "PropertyC"
    print-row 120 " | " "PropertyA" "PropertyB" "PropertyC"
    print-row 120 " | " "PropertyA" "PropertyB" "PropertyC"
    print-row 120 " | " "PropertyA" "PropertyB" "PropertyC"
    print-row 120 " | " "PropertyA" "PropertyB" "PropertyC"
    print-row 120 " | " "PropertyA" "PropertyB" "PropertyC"
else
    let
        filter-visible
        printable-countof
        split-styled
        print-row
        run-tests
    locals;
