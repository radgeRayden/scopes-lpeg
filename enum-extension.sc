using import enum

fn extract-payload (enum-value extractT)
    # don't bother if it's a unit tag
    if (extractT == Nothing)
        return (spice-quote none)

    let qcls = ('qualified-typeof enum-value)
    let cls = ('strip-qualifiers qcls)
    let payload-cls = ('element@ cls 1)
    let raw-payload = `(extractvalue enum-value 1)
    let refer = ('refer? qcls)
    let ptrT = ('refer->pointer-type qcls)
    # this bit was copied from enum.sc and I don't fully understand it
    let extracted =
        if refer
            let ptrET = ('change-element-type ptrT extractT)
            spice-quote
                let ptr = (reftoptr raw-payload)
                let ptr = (bitcast ptr ptrET)
                ptrtoref ptr
        else
            let ptrET = ('change-storage-class
                ('mutable (pointer.type extractT)) 'Function)
            spice-quote
                let ptr = (alloca payload-cls)
                store raw-payload ptr
                let ptr = (bitcast ptr ptrET)
                load ptr
    let ET = ('strip-qualifiers extractT)
    let extracted =
        if (ET < tuple)
            `(unpack extracted)
        else extracted

spice build-generic-dispatch (eT self f)
    eT as:= type
    let field-types-args = ('args eT.__fields__)
    let tag-index = `(extractvalue self 0)
    let sw = (sc_switch_new tag-index)
    for ft in field-types-args
        let ft = (ft as type)
        let index = ('@ ft 'Literal)
        let tag = (('@ ft 'Name) as Symbol)
        let payload-type = (('@ ft 'Type) as type)
        let payload = (extract-payload self payload-type)
        sc_switch_append_case 
            sw 
            index
            `(f index tag payload)
    sc_switch_append_default sw `(f -1 'invalid none)
    sw

spice enum-equals? (eA eB)
    let aT bT = ('typeof eA) ('typeof eB)
    if (aT != bT)
        return (spice-quote false)
    # because checking if it's a unit tag wouldn't work without the compiler,
      I'm gonna refrain from looking it up and just compare the payload
      regardless, it's gonna be the same in that case.
    let qcls = ('qualified-typeof eA)
    let cls = ('strip-qualifiers qcls)
    # gets 'largest' type in the enum, useful for getting the size of the payload part
    let payload-cls = ('element@ cls 1)
    # TODO: ask feedback on this
    let payload-cls = ('element@ ('element@ payload-cls 0) 0)
    let tagA tagB = 
        `(extractvalue eA 0)    
        `(extractvalue eB 0)
    let payloadA payloadB = 
        extract-payload eA payload-cls
        extract-payload eB payload-cls
    spice-quote
        dupe
            and
                tagA     == tagB
                payloadA == payloadB

run-stage;

typedef+ Enum
    fn tag-repr (self)
        let eT = (typeof self)
        build-generic-dispatch
            eT
            self
            fn (index tag payload)
                default-styler 'style-sfxfunction (tag as string)

    fn payload-repr (self)
        let eT = (typeof self)
        build-generic-dispatch
            eT
            self
            fn (index tag payload)
                repr payload 

'set-symbol Enum
    __== = (box-pointer (simple-binary-op enum-equals?))

run-stage;
            
##### TESTS #####
fn run-tests ()
    using import testing
    enum A
        a
        b : i32
        c : i16
        d : u64
        e
    enum B
        a : (tuple i32 string)
        b : i8
        c : (vector f64 8) 

    local en = (A.b 10)
    ;
    # 1. equality
    do
        # reference vs non-reference
        test (en == (A.b 10))
        # unit tag
        test ((A.a) == (A.a))
        test ((A.a) != (A.e))
        # unit vs payload
        test ((A.a) != (A.b))
        # payload
        test ((A.b 10) != (A.b 11))
        #TODO: ask lritter why this doesn't work
        # test ((B.a (tupleof 5 "abcde")) == (B.a (tupleof 5 "abcde")))
    
    # 2. generic-dispatch
    print ('tag-repr en)
    print ('tag-repr (B.a (tupleof 5 "abcde")))
    print ('tag-repr (A.a))

static-if main-module?
    run-tests;
else
    let
        build-generic-dispatch
        run-tests
    locals;
    
