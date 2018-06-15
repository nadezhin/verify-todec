#|
(include-book "rtl/rel11/portcullis" :dir :system)
(defpkg "LABEL" '(nil t))
(defpkg "JVM" '(nil t))
(DEFPKG "M5"
  (set-difference-equal
   (union-eq '(JVM::SCHEDULED
               JVM::UNSCHEDULED
               JVM::REF
               JVM::LOCKED
               JVM::S_LOCKED
               JVM::UNLOCKED
               JVM::AALOAD
               JVM::AASTORE
               JVM::ACONST_NULL
               JVM::ALOAD
               JVM::ALOAD_0
               JVM::ALOAD_1
               JVM::ALOAD_2
               JVM::ALOAD_3
               JVM::ANEWARRAY
               JVM::ARETURN
               JVM::ARRAYLENGTH
               JVM::ASTORE
               JVM::ASTORE_0
               JVM::ASTORE_1
               JVM::ASTORE_2
               JVM::ASTORE_3
               JVM::BALOAD
               JVM::BASTORE
               JVM::BIPUSH
               JVM::CALOAD
               JVM::CASTORE
               JVM::DUP
               JVM::DUP_X1
               JVM::DUP_X2
               JVM::DUP2
               JVM::DUP2_X1
               JVM::DUP2_X2
               JVM::GETFIELD
               JVM::GETSTATIC
               JVM::GOTO
               JVM::GOTO_W
               JVM::I2B
               JVM::I2C
               JVM::I2L
               JVM::I2S
               JVM::IADD
               JVM::IALOAD
               JVM::IAND
               JVM::IASTORE
               JVM::ICONST_M1
               JVM::ICONST_0
               JVM::ICONST_1
               JVM::ICONST_2
               JVM::ICONST_3
               JVM::ICONST_4
               JVM::ICONST_5
               JVM::IDIV
               JVM::IF_ACMPEQ
               JVM::IF_ACMPNE
               JVM::IF_ICMPEQ
               JVM::IF_ICMPGE
               JVM::IF_ICMPGT
               JVM::IF_ICMPLE
               JVM::IF_ICMPLT
               JVM::IF_ICMPNE
               JVM::IFEQ
               JVM::IFGE
               JVM::IFGT
               JVM::IFLE
               JVM::IFLT
               JVM::IFNE
               JVM::IFNONNULL
               JVM::IFNULL
               JVM::IINC
               JVM::ILOAD
               JVM::ILOAD_0
               JVM::ILOAD_1
               JVM::ILOAD_2
               JVM::ILOAD_3
               JVM::IMUL
               JVM::INEG
               JVM::INSTANCEOF
               JVM::INVOKESPECIAL
               JVM::INVOKESTATIC
               JVM::INVOKEVIRTUAL
               JVM::IOR
               JVM::IREM
               JVM::IRETURN
               JVM::ISHL
               JVM::ISHR
               JVM::ISTORE
               JVM::ISTORE_0
               JVM::ISTORE_1
               JVM::ISTORE_2
               JVM::ISTORE_3
               JVM::ISUB
               JVM::IUSHR
               JVM::IXOR
               JVM::JSR
               JVM::JSR_W
               JVM::L2I
               JVM::LADD
               JVM::LALOAD
               JVM::LAND
               JVM::LASTORE
               JVM::LCMP
               JVM::LCONST_0
               JVM::LCONST_1
               JVM::LDC
               JVM::LDC_W
               JVM::LDC2_W
               JVM::LDIV
               JVM::LLOAD
               JVM::LLOAD_0
               JVM::LLOAD_1
               JVM::LLOAD_2
               JVM::LLOAD_3
               JVM::LMUL
               JVM::LNEG
               JVM::LOR
               JVM::LREM
               JVM::LRETURN
               JVM::LSHL
               JVM::LSHR
               JVM::LSTORE
               JVM::LSTORE_0
               JVM::LSTORE_1
               JVM::LSTORE_2
               JVM::LSTORE_3
               JVM::LSUB
               JVM::LUSHR
               JVM::LXOR
               JVM::MONITORENTER
               JVM::MONITOREXIT
               JVM::MULTIANEWARRAY
               JVM::NEW
               JVM::NEWARRAY
               JVM::NOP
               JVM::POP
               JVM::POP2
               JVM::PUTFIELD
               JVM::PUTSTATIC
               JVM::RET
               JVM::RETURN
               JVM::SALOAD
               JVM::SASTORE
               JVM::SIPUSH
               JVM::SWAP
               ASSOC-EQUAL LEN NTH ZP SYNTAXP
               QUOTEP FIX NFIX E0-ORDINALP E0-ORD-<)
             (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
   '(PC PROGRAM PUSH POP RETURN REVERSE STEP ++)))
|#
(in-package "M5")
(include-book "std/util/defredundant" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "kestrel/utilities/fixbytes/instances" :dir :system)
(include-book "rtl/rel11/support/excps" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))

(acl2::define heap-ref-p (x)
  :returns (yes booleanp :rule-classes ())
  (and (consp x)
       (equal (car x) 'ref)
       (consp (cdr x))
       (integerp (cadr x))
       (<= -1 (cadr x))
       (null (cddr x))))

(acl2::define heap-ref-fix
  ((x heap-ref-p))
  :returns (x heap-ref-p)
  (mbe :logic (if (heap-ref-p x) x (list 'ref -1))
       :exec x)
  ///
  (acl2::defrule heap-ref-fix-when-heap-ref-p
    (implies (heap-ref-p x)
             (equal (heap-ref-fix x) x)))
  (fty::deffixtype heap-ref
    :pred heap-ref-p
    :fix heap-ref-fix
    :equiv heap-ref-equiv
    :define t))

(fty::defflexsum math.DoubleToDecimal
  (:flds
   :shape (and (true-listp x)
               (equal (len x) 2)
               (true-listp (car x))
               (equal (len (car x)) 8)
               (equal (car (car x)) "math.DoubleToDecimal")
               (consp (cadr (car x)))
               (equal (car (cadr (car x))) "e")
               (consp (caddr (car x)))
               (equal (car (caddr (car x))) "q")
               (consp (cadddr (car x)))
               (equal (car (cadddr (car x))) "c")
               (consp (car (cddddr (car x))))
               (equal (car (car (cddddr (car x)))) "lout")
               (consp (cadr (cddddr (car x))))
               (equal (car (cadr (cddddr (car x)))) "rout")
               (consp (caddr (cddddr (car x))))
               (equal (car (caddr (cddddr (car x)))) "buf")
               (consp (cadddr (cddddr (car x))))
               (equal (car (cadddr (cddddr (car x)))) "index")
               (equal (cadr x)
                      '("java.lang.Object" ("monitor" . 0)
                        ("mcount" . 0)
                        ("wait-set" . 0))))
   :fields
   ((e :type acl2::sbyte32 :acc-body (cdr (cadr (car x))))
    (q :type acl2::sbyte32 :acc-body (cdr (caddr (car x))))
    (c :type acl2::sbyte64 :acc-body (cdr (cadddr (car x))))
    (lout :type acl2::sbyte32 :acc-body (cdr (car (cddddr (car x)))))
    (rout :type acl2::sbyte32 :acc-body (cdr (cadr (cddddr (car x)))))
    (buf :type heap-ref :acc-body (cdr (caddr (cddddr (car x)))))
    (index :type acl2::sbyte32 :acc-body (cdr (cadddr (cddddr (car x))))))
   :ctor-body (list
               (list
                "math.DoubleToDecimal"
                (cons "e" e)
                (cons "q" q)
                (cons "c" c)
                (cons "lout" lout)
                (cons "rout" rout)
                (cons "buf" buf)
                (cons "index" index))
               '("java.lang.Object" ("monitor" . 0)
                 ("mcount" . 0)
                 ("wait-set" . 0)))))

(acl2::rule
 (equal (math.DoubleToDecimal-kind x) :flds))

(encapsulate ()
  (local (include-book "models/jvm/m5/m5" :dir :system))

  (verify-guards acl2::limitpart)
  (verify-guards acl2::count2)
  (verify-guards acl2::padd)
  (verify-guards acl2::pmult)
  (verify-guards acl2::ob*)
  (verify-guards acl2::o-)
  (verify-guards acl2::o^1)
  (verify-guards acl2::o^2)
  (verify-guards acl2::o^3h)
  (verify-guards acl2::o^3)
  (verify-guards acl2::o^4)
  (verify-guards acl2::ob^)
  (std::defredundant
   :names (acl2::ob*
           acl2::ob^
           acl2::d<
           acl2::lexp
           acl2::l<
           acl2::lsttoo
           acl2::ltoo
           acl2::well-founded-l<

           push
           top
           pop
           popn
           bound?
           bind
           binding
           op-code
           arg1
           arg2
           arg3
           nullrefp
           reverse
           *largest-integer-value*
           *largest-long-value*
           *most-negative-integer*
           *most-negative-long*
           u-fix
           s-fix
           byte-fix
           ubyte-fix
           short-fix
           int-fix
           uint-fix
           long-fix
           ulong-fix
           char-fix
           6-bit-fix
           5-bit-fix
           expt2
           shl
           shr
           *mxcsr*
           int2fp
           fp2fp
           fp2int
           fpcmp
           fp-binary
           fpadd
           fpsub
           fpmul
           fpdiv
           fprem
           fpneg
           fpsqrt
           bits2fp
           make-state
           thread-table
           heap
           class-table
           make-thread
           call-stack
           status
           rref
           make-class-decl
           class-decl-name
           class-decl-superclasses
           class-decl-fields
           class-decl-sfields
           class-decl-cp
           class-decl-methods
           class-decl-heapref
           base-class-def
           make-class-def
           cp-make-double-entry
           cp-make-float-entry
           cp-make-int-entry
           cp-make-long-entry
           cp-string-resolved?
           retrieve-cp
           update-ct-string-ref
           make-tt
           addto-tt
           mod-thread-scheduling
           schedule-thread
           unschedule-thread
           rrefToThread
           in-list
           isThreadObject?
           lock-object
           unlock-object
           objectlockable?
           objectUnLockable?
           make-frame
           top-frame
           pc
           locals
           stack
           program
           sync-flg
           cur-class
           method-name
           method-formals
           method-sync
           method-program
           method-isNative?
           suppliedp
           actual
           modify
           deref
           field-value
           build-class-field-bindings
           build-class-object-field-bindings
           build-immediate-instance-data
           build-an-instance
           build-class-data
           build-a-class-instance
           value-of
           superclasses-of
           array-content
           array-type
           array-bound
           array-data
           element-at
           makearray
           set-element-at
           primitive-type
           atype-to-identifier
           identifier-to-atype
           default-value1
           init-array
           natural-sum
           makemultiarray2
           makemultiarray
           inst-length
           execute-AALOAD
           execute-AASTORE
           execute-ACONST_NULL
           execute-ALOAD
           execute-ALOAD_X
           execute-ANEWARRAY
           execute-ARETURN
           execute-ARRAYLENGTH
           execute-ASTORE
           execute-ASTORE_X
           execute-BALOAD
           execute-BASTORE
           execute-BIPUSH
           execute-CALOAD
           execute-CASTORE
           execute-D2F
           execute-D2I
           execute-D2L
           execute-DADD
           execute-DALOAD
           execute-DASTORE
           execute-DCMPG
           execute-DCMPL
           execute-DCONST_0
           execute-DCONST_1
           execute-DDIV
           execute-DLOAD
           execute-DLOAD_X
           execute-DMUL
           execute-DNEG
           execute-DREM
           execute-DRETURN
           execute-DSTORE
           execute-DSTORE_X
           execute-DSUB
           execute-DUP
           execute-DUP_X1
           execute-DUP_X2
           execute-DUP2
           execute-DUP2_X1
           execute-DUP2_X2
           execute-F2D
           execute-F2I
           execute-F2L
           execute-FADD
           execute-FALOAD
           execute-FASTORE
           execute-FCMPG
           execute-FCMPL
           execute-FCONST_0
           execute-FCONST_1
           execute-FCONST_2
           execute-FDIV
           execute-FLOAD
           execute-FLOAD_X
           execute-FMUL
           execute-FNEG
           execute-FREM
           execute-FRETURN
           execute-FSTORE
           execute-FSTORE_X
           execute-FSUB
           execute-GETFIELD
           static-field-value
           execute-GETSTATIC
           execute-GOTO
           execute-GOTO_W
           execute-I2B
           execute-I2C
           execute-I2D
           execute-I2F
           execute-I2L
           execute-I2S
           execute-IADD
           execute-IALOAD
           execute-IAND
           execute-IASTORE
           execute-ICONST_X
           execute-IDIV
           execute-IF_ACMPEQ
           execute-IF_ACMPNE
           execute-IF_ICMPEQ
           execute-IF_ICMPGE
           execute-IF_ICMPGT
           execute-IF_ICMPLT
           execute-IF_ICMPLE
           execute-IF_ICMPNE
           execute-IFEQ
           execute-IFGE
           execute-IFGT
           execute-IFLE
           execute-IFLT
           execute-IFNE
           execute-IFNONNULL
           execute-IFNULL
           execute-IINC
           execute-ILOAD
           execute-ILOAD_X
           execute-IMUL
           execute-INEG
           execute-INSTANCEOF
           execute-IOR
           execute-IREM
           execute-IRETURN
           execute-ISHL
           execute-ISHR
           execute-ISTORE
           execute-ISTORE_X
           execute-ISUB
           iushr
           execute-IUSHR
           execute-IXOR
           execute-JSR
           execute-JSR_W
           class-name-of-ref
           bind-formals
           lookup-method-in-superclasses
           lookup-method
           execute-INVOKESPECIAL
           execute-INVOKESTATIC
           execute-INVOKEVIRTUAL
           execute-L2D
           execute-L2F
           execute-L2I
           execute-LADD
           execute-LALOAD
           execute-LAND
           execute-LASTORE
           execute-LCMP
           execute-LCONST_X
           set-instance-field
           execute-LDC
           execute-LDC2_W
           execute-LDIV
           execute-LLOAD
           execute-LLOAD_X
           execute-LMUL
           execute-LNEG
           execute-LOR
           execute-LREM
           execute-LRETURN
           execute-LSHL
           execute-LSHR
           execute-LSTORE
           execute-LSTORE_X
           execute-LSUB
           lushr
           execute-LUSHR
           execute-LXOR
           execute-MONITORENTER
           execute-MONITOREXIT
           execute-MULTIANEWARRAY
           execute-NEW
           execute-NEWARRAY
           execute-NOP
           execute-POP
           execute-POP2
           execute-PUTFIELD
           execute-PUTSTATIC
           execute-RET
           execute-RETURN
           execute-SALOAD
           execute-SASTORE
           execute-SIPUSH
           execute-SWAP
           do-inst)))

(acl2::defruled field-value-math.DoubleToDecimal
 (acl2::b*
  (((math.DoubleToDecimal-flds instance) instance))
  (implies
   (math.DoubleToDecimal-p instance)
   (and
    (equal (field-value "java.lang.Object" "monitor" instance)
           0)
    (equal (field-value "java.lang.Object" "mcount" instance)
           0)
    (equal (field-value "java.lang.Object" "wait-set" instance)
           0)
    (equal (field-value "math.DoubleToDecimal" "e" instance)
           instance.e)
    (equal (field-value "math.DoubleToDecimal" "q" instance)
           instance.q)
    (equal (field-value "math.DoubleToDecimal" "c" instance)
           instance.c)
    (equal (field-value "math.DoubleToDecimal" "lout" instance)
           instance.lout)
    (equal (field-value "math.DoubleToDecimal" "rout" instance)
           instance.rout)
    (equal (field-value "math.DoubleToDecimal" "buf" instance)
           instance.buf)
    (equal (field-value "math.DoubleToDecimal" "index" instance)
           instance.index))))
 :enable (math.DoubleToDecimal-p
          math.DoubleToDecimal-flds->e
          math.DoubleToDecimal-flds->q
          math.DoubleToDecimal-flds->c
          math.DoubleToDecimal-flds->lout
          math.DoubleToDecimal-flds->rout
          math.DoubleToDecimal-flds->buf
          math.DoubleToDecimal-flds->index))

(acl2::rule
 (acl2::b*
  ((top-frame (top-frame th s))
   ((math.DoubleToDecimal-flds instance)
    (deref (top (stack top-frame)) (heap s)))
   (new-pc (+ 3 (pc top-frame)))
   (stack (pop (stack top-frame))))
  (implies
   (and (math.DoubleToDecimal-p instance))
   (and
    (equal
     (do-inst (list 'GETFIELD "java.lang.Object" "monitor" nil) th s)
     (modify th s :pc new-pc
             :stack (push 0 stack)))
    (equal
     (do-inst (list 'GETFIELD "java.lang.Object" "mcount" nil) th s)
     (modify th s :pc new-pc
             :stack (push 0 stack)))
    (equal
     (do-inst (list 'GETFIELD "java.lang.Object" "wait-set" nil) th s)
     (modify th s :pc new-pc
             :stack (push 0 stack)))
    (equal
     (do-inst (list 'GETFIELD "math.DoubleToDecimal" "e" nil) th s)
     (modify th s :pc new-pc
             :stack (push instance.e stack)))
    (equal
     (do-inst (list 'GETFIELD "math.DoubleToDecimal" "q" nil) th s)
     (modify th s :pc new-pc
             :stack (push instance.q stack)))
    (equal
     (do-inst (list 'GETFIELD "math.DoubleToDecimal" "c" t) th s)
     (modify th s :pc new-pc
             :stack (push 0 (push instance.c stack))))
    (equal
     (do-inst (list 'GETFIELD "math.DoubleToDecimal" "lout" nil) th s)
     (modify th s :pc new-pc
             :stack (push instance.lout stack)))
    (equal
     (do-inst (list 'GETFIELD "math.DoubleToDecimal" "rout" nil) th s)
     (modify th s :pc new-pc
             :stack (push instance.rout stack)))
    (equal
     (do-inst (list 'GETFIELD "math.DoubleToDecimal" "buf" t) th s)
     (modify th s :pc new-pc
             :stack (push 0 (push instance.buf stack))))
    (equal
     (do-inst (list 'GETFIELD "math.DoubleToDecimal" "index" nil) th s)
     (modify th s :pc new-pc
             :stack (push instance.index stack))))))
 :enable field-value-math.DoubleToDecimal
 :disable field-value)

(acl2::defruled set-instance-field-math.DoubleToDecimal
 (acl2::b*
  (((math.DoubleToDecimal-flds i) instance))
  (implies
   (math.DoubleToDecimal-p instance)
   (and
    (implies
     (acl2::sbyte32p e)
     (equal (set-instance-field "math.DoubleToDecimal" "e" e instance)
            (math.DoubleToDecimal-flds
             e i.q i.c i.lout i.rout i.buf i.index)))
    (implies
     (acl2::sbyte32p q)
     (equal (set-instance-field "math.DoubleToDecimal" "q" q instance)
            (math.DoubleToDecimal-flds
             i.e q i.c i.lout i.rout i.buf i.index)))
    (implies
     (acl2::sbyte64p c)
     (equal (set-instance-field "math.DoubleToDecimal" "c" c instance)
            (math.DoubleToDecimal-flds
             i.e i.q c i.lout i.rout i.buf i.index)))
    (implies
     (acl2::sbyte32p lout)
     (equal (set-instance-field "math.DoubleToDecimal" "lout" lout instance)
            (math.DoubleToDecimal-flds
             i.e i.q i.c lout i.rout i.buf i.index)))
    (implies
     (acl2::sbyte32p rout)
     (equal (set-instance-field "math.DoubleToDecimal" "rout" rout instance)
            (math.DoubleToDecimal-flds
             i.e i.q i.c i.lout rout i.buf i.index)))
    (implies
     (heap-ref-p buf)
     (equal (set-instance-field "math.DoubleToDecimal" "buf" buf instance)
            (math.DoubleToDecimal-flds
             i.e i.q i.c i.lout i.rout buf i.index)))
    (implies
     (acl2::sbyte32p index)
     (equal (set-instance-field "math.DoubleToDecimal" "index" index instance)
            (math.DoubleToDecimal-flds
             i.e i.q i.c i.lout i.rout i.buf index))))))
 :enable (math.DoubleToDecimal-p
          math.DoubleToDecimal-flds->e
          math.DoubleToDecimal-flds->q
          math.DoubleToDecimal-flds->c
          math.DoubleToDecimal-flds->lout
          math.DoubleToDecimal-flds->rout
          math.DoubleToDecimal-flds->buf
          math.DoubleToDecimal-flds->index))

(acl2::rule
 (acl2::b*
  ((top-frame (top-frame th s))
   (stack (stack top-frame))
   (heap (heap s))
   (new-pc (+ 3 (pc top-frame))))
  (and
   (acl2::b*
    ((e (top stack))
     (ref (top (pop stack)))
     (stack (pop (pop stack)))
     (address (cadr ref))
     ((math.DoubleToDecimal-flds i) (deref ref heap)))
    (implies
     (and (math.DoubleToDecimal-p i)
          (acl2::sbyte32p e))
     (and
      (equal
       (do-inst (list 'PUTFIELD "math.DoubleToDecimal" "e" nil) th s)
       (modify th s :pc new-pc :stack stack
               :heap (bind address
                           (math.DoubleToDecimal-flds
                            e i.q i.c i.lout i.rout i.buf i.index)
                           heap))))))
   (acl2::b*
    ((q (top stack))
     (ref (top (pop stack)))
     (stack (pop (pop stack)))
     (address (cadr ref))
     ((math.DoubleToDecimal-flds i) (deref ref heap)))
    (implies
     (and (math.DoubleToDecimal-p i)
          (acl2::sbyte32p q))
     (and
      (equal
       (do-inst (list 'PUTFIELD "math.DoubleToDecimal" "q" nil) th s)
       (modify th s :pc new-pc :stack stack
               :heap (bind address
                           (math.DoubleToDecimal-flds
                            i.e q i.c i.lout i.rout i.buf i.index)
                           heap))))))
   (acl2::b*
    ((c (top (pop stack)))
     (ref (top (pop (pop stack))))
     (stack (pop (pop (pop stack))))
     (address (cadr ref))
     ((math.DoubleToDecimal-flds i) (deref ref heap)))
    (implies
     (and (math.DoubleToDecimal-p i)
          (acl2::sbyte64p c))
     (and
      (equal
       (do-inst (list 'PUTFIELD "math.DoubleToDecimal" "c" t) th s)
       (modify th s :pc new-pc :stack stack
               :heap (bind address
                           (math.DoubleToDecimal-flds
                            i.e i.q c i.lout i.rout i.buf i.index)
                           heap))))))
   (acl2::b*
    ((lout (top stack))
     (ref (top (pop stack)))
     (stack (pop (pop stack)))
     (address (cadr ref))
     ((math.DoubleToDecimal-flds i) (deref ref heap)))
    (implies
     (and (math.DoubleToDecimal-p i)
          (acl2::sbyte32p lout))
     (and
      (equal
       (do-inst (list 'PUTFIELD "math.DoubleToDecimal" "lout" nil) th s)
       (modify th s :pc new-pc :stack stack
               :heap (bind address
                           (math.DoubleToDecimal-flds
                            i.e i.q i.c lout i.rout i.buf i.index)
                           heap))))))
   (acl2::b*
    ((rout (top stack))
     (ref (top (pop stack)))
     (stack (pop (pop stack)))
     (address (cadr ref))
     ((math.DoubleToDecimal-flds i) (deref ref heap)))
    (implies
     (and (math.DoubleToDecimal-p i)
          (acl2::sbyte32p rout))
     (and
      (equal
       (do-inst (list 'PUTFIELD "math.DoubleToDecimal" "rout" nil) th s)
       (modify th s :pc new-pc :stack stack
               :heap (bind address
                           (math.DoubleToDecimal-flds
                            i.e i.q i.c i.lout rout i.buf i.index)
                           heap))))))
   (acl2::b*
    ((buf (top (pop stack)))
     (ref (top (pop (pop stack))))
     (stack (pop (pop (pop stack))))
     (address (cadr ref))
     ((math.DoubleToDecimal-flds i) (deref ref heap)))
    (implies
     (and (math.DoubleToDecimal-p i)
          (heap-ref-p buf))
     (and
      (equal
       (do-inst (list 'PUTFIELD "math.DoubleToDecimal" "buf" t) th s)
       (modify th s :pc new-pc :stack stack
               :heap (bind address
                           (math.DoubleToDecimal-flds
                            i.e i.q i.c i.lout i.rout buf i.index)
                           heap))))))
   (acl2::b*
    ((index (top stack))
     (ref (top (pop stack)))
     (stack (pop (pop stack)))
     (address (cadr ref))
     ((math.DoubleToDecimal-flds i) (deref ref heap)))
    (implies
     (and (math.DoubleToDecimal-p i)
          (acl2::sbyte32p index))
     (and
      (equal
       (do-inst (list 'PUTFIELD "math.DoubleToDecimal" "index" nil) th s)
       (modify th s :pc new-pc :stack stack
               :heap (bind address
                           (math.DoubleToDecimal-flds
                            i.e i.q i.c i.lout i.rout i.buf index)
                           heap))))))))
 :enable set-instance-field-math.DoubleToDecimal
 :disable set-instance-field
 :prep-lemmas
 ((acl2::defrule popn-2
    (equal (popn 2 stack)
           (cddr stack)))))

(defconst *math.DoubleToDecimal-class-stub*
   (make-class-decl
    "math.DoubleToDecimal"
    '("java.lang.Object")
    '("e" "q" "c" "lout" "rout" "buf" "index")
    '("LTR" "MASK_LTR" "MASK_SIGNIFICAND" "D" "threadLocal")
    ()
    ()
    '(REF -1)))
