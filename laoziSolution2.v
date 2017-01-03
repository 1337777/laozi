(**#+TITLE: laoziSolution.v

Proph

https://github.com/1337777/laozi/blob/master/laoziSolution2.v

solves some question of LAOZI [fn:1] which is how to program polymorph coparametrism
functors ( "comonad" ) ... Whatever is discovered, its format, its communication is
simultaneously some predictable logical discovery and some random dia-para-logical
discovery.

In particular this text programs the grammatical / inductive (therefore free) 
description of polymorph coparametrism functor and the conversion 
relations over the generated morphisms. This text is based on earlier texts which 
describe functional-monoidal logic and the decidable coherence of this logic.

Next this text programs the iterated comultiplication (DeClassifying) and the
corresponding deduced conversion relations over the morphisms. Then the reduction
relation and degradation lemmas are programmed and deduced.

Finally the solution morphisms are programmed with their (dependent-)destruction
lemmas such to inner-instantiate the object-indices. And the (non-congruent)
resolution by cut elimination / desintegration technique is programmed and deduced :
this deduction is mostly-automated.

For instant first impression, the common saying that the counit inner-cancels the
comultiplication is written as :

#+BEGIN_EXAMPLE
| IterCancelInner :
    forall {trf : obV log -> obV log}
      (Vb Vb' : obV log) (vb : V(0 Vb' |- Vb )0)
      (W W_dft : obV log) (V0Vb' : obV log) (Vs : list (obV log))
      (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
      (va : V(0 trf(last W_dft Vs) |- W )0)
      (v0b : V(0 V0Vb' |- (0 trf(head W_dft Vs) & Vb' )0 )0)
      (B : obMod) (A : obMod) (b : 'D(0 Vb |- [0 B ~> A ]0 )0)
      (A' : obMod)(a : 'D(0 W |- [0 A ~> A' ]0 )0),
      ( v0b o>| ( vb o>' b)  o>D (iterDeClassifying (V_dft := W_dft) vs ( va o>' a)) )
        <~~ ( v0b o>| (vb o>| b o>Mod 'declfy )
                o>D (iterDeClassifying (V_dft := W_dft) vs (va o>| 'clfy o>Mod a) )
            : 'D(0 V0Vb' |- [0 B ~> 'D0| (iterDeClass0 (length Vs).-1 A') ]0)0 )
#+END_EXAMPLE

Outline :

  * Grammatical description of polymorph coparametrism functor
  ** Importing the functional-monoidal logic
  ** Base generating graph
  ** Grammatical generation of the morhisms
  ** Decoding into the common sense : grammatical is indeed free
  ** Some notations
  ** More functional-monoidal logic
  ** The generated conversion relations over the morphisms

  * Iterated constructors
  ** Indexed list, lemmas
  ** Chained lists, lemmas
  ** Iterated constructors

  * Grade

  * Reduction
  ** Grammatical generation of the reduction relation
  ** Degradation lemmas

  * Solution
  ** Grammatical generation of the solution morphisms
  ** Containment of the solution morphisms into all the morphisms
  ** Destruction of morphisms with inner-instantiation of object-indices
  ** Iterated =DeClassifying= prefix

  * Resolution

Reviews :

[fn:1] ~1337777.OOO~ [[https://github.com/1337777/laozi/blob/master/laoziSolution2.v]]

-----

May some additional empty-rooms in the public UBC campus have their doors unlocked during July 15 
for the public 1337777 School ?

The public 1337777 School is seeking ministerial-review-and-payments as school for the public, 
comparable to https://team.inria.fr/marelle/coq-winter-school-2017/ . Such 1337777 School shall
truly hold the motivation of maximizing the mathematical memory and sensibility of each
 and all of the public, contrary to the common falsification of the other 
ministerial-reports which in reality have none such motivation and even may sans-detours
 elect-by-random ...

paypal 1337777.OOO@gmail.com , wechatpay 2796386464@qq.com , irc #OOO1337777


* Grammatical description of polymorph coparametrism functor

** Importing the functional-monoidal logic

Importing the functional-monoidal logic, the ssreflect grammar and deduction tactics
and math definitions, the congruent rewriting tactics, and the linear arithmetic
decidability-solver. (Memo that ~COQ~ --version > 8.5)

#+BEGIN_SRC coq :exports both :results silent **)

Require Import borceuxSolution_half_old.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq.
Require Import Setoid.
Require Omega.

Set Implicit Arguments.
Unset Strict Implicits.
Unset Printing Implicit Defensive.

(**#+END_SRC

** Base generating graph

#+BEGIN_SRC coq :exports both :results silent **)

Module COPARAM.

  Import LOGIC.
  Import LOGIC.Ex_Notations3.

  Parameter obMod_gen : Set.
  Parameter Mod_gen : forall {log : logic}, obV log -> obMod_gen -> obMod_gen -> Set.
  
  Inductive obMod : Set :=
  | GenObMod : forall A : obMod_gen, obMod
  | DeClass0 : forall A : obMod, obMod.

  Notation "#0| A" := (GenObMod A) (at level 4, right associativity).
  Notation "'D0| A" := (DeClass0 A) (at level 4, right associativity).

(**#+END_SRC

** Grammatical generation of the morphisms

The grammatical description of polymorph coparametrism functor, primo the morphisms :

#+BEGIN_SRC coq :exports both :results silent **)
  
  Reserved Notation "''Mod' (0 V |- [0 A1 ~> A2 ]0 )0"
           (at level 25, format "''Mod' (0  V  |-  [0  A1  ~>  A2  ]0 )0").
  Reserved Notation "''D' (0 V |- [0 A1 ~> A2 ]0 )0"
           (at level 25, format "''D' (0  V  |-  [0  A1  ~>  A2  ]0 )0").

  Inductive Mod00 {log : logic} : obV log -> obMod -> obMod -> Type :=

  | PolyV_Mod : forall (V V' : obV log),
      V(0 V' |- V )0 -> forall (A1 A2 : obMod), 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 ->
                                         'Mod(0 V' |- [0 A1 ~> A2 ]0 )0

  | GenArrowsMod : forall (V V' : obV log), forall A1 A2 : obMod_gen
      , Mod_gen V A1 A2 -> V(0 V' |- V )0 -> 
        'Mod(0 V' |- [0 (#0| A1) ~> (#0| A2) ]0 )0

  | UnitMod : forall (V : obV log), forall {A : obMod}
      ,  V(0 V |- log.-I )0 -> 'Mod(0 V |- [0 A ~> A ]0 )0

  | PolyMod : forall (V : obV log) (A2 : obMod) (A1 : obMod)
    , 'Mod(0 V |- [0 A2 ~> A1 ]0 )0 -> forall A1' : obMod, forall (W WV : obV log),
          V(0 WV |- (0 W & V )0 )0 ->
          'Mod(0 W |- [0 A1 ~> A1' ]0 )0 -> 'Mod(0 WV |- [0 A2 ~> A1' ]0 )0

  | UnitDeClass : forall (A : obMod) (A' : obMod) (W W' : obV log)
    , V(0 W' |- (0 W & log.-I)0 )0 ->
      'Mod(0 W |- [0 A ~> A' ]0 )0 -> 'D(0 W' |- [0 'D0| A ~> A' ]0 )0

  | PolyDeClass : forall (V : obV log) (B : obMod) (A : obMod),
      'D(0 V |- [0 B ~> A ]0 )0 -> forall A' : obMod, forall (W WV : obV log),
          V(0 WV |- (0 W & V )0 )0 ->
          'Mod(0 W |- [0 A ~> A' ]0 )0 -> 'D(0 WV |- [0 B ~> A' ]0 )0

  (* common CoUnit, errata: Unit *)
  | Classifying : forall (V V' : obV log), forall (A1 A2 : obMod),
        V(0 V' |- V )0 ->
        'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'Mod(0 V' |- [0 ('D0| A1) ~> A2 ]0 )0

  | DeClassifying : forall (V V' : obV log), forall (A1 A2 : obMod),
        V(0 V' |- V )0 -> 
        'D(0 V |- [0 A1 ~> A2 ]0 )0 -> 'D(0 V' |- [0 A1 ~> ('D0| A2) ]0 )0

  where
  "''Mod' (0 V |- [0 A1 ~> A2 ]0 )0"
    := (@Mod00 _ V A1 A2) and "''D' (0 V |- [0 A1 ~> A2 ]0 )0"
         := (@Mod00 _ V A1 ('D0| A2)).
    
(**#+END_SRC

** Decoding into the common sense : grammatical is indeed free

How to decode from the grammatical description to the non-grammatical description such
to deduce that it is indeed some instance of polymorph coparametrism functor, in the
common sense :

#+BEGIN_SRC coq :exports both :results silent **)
  
  Parameter Mod'00 : forall {log : logic}, obMod -> obMod -> obV log.
  Parameter decode : forall {log : logic}, forall {A1 A2 : obMod},
      forall {V : obV log}, 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> V(0 V |- Mod'00 A1 A2 )0 .
  Parameter encode : forall {log : logic}, forall {A1 A2 : obMod},
      forall {V : obV log}, V(0 V |- Mod'00 A1 A2 )0 -> 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 .
  Axiom decodeK : forall {log : logic}, forall (A1 A2 : obMod) (V : obV log),
        cancel (@decode _ A1 A2 V) (@encode _ A1 A2 V).
  Axiom encodeK : forall {log : logic}, forall (A1 A2 : obMod) (V : obV log),
        cancel (@encode _ A1 A2 V) (@decode _ A1 A2 V).

  Axiom decode_metaPoly : forall {log : logic}, forall (A1 A2 : obMod),
      forall (V V' : obV log) (v : V(0 V' |- V )0), forall f : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0,
          ( v o> (decode f) )
            ~~ ( decode (PolyV_Mod v f)
                 : log.-V(0 V' |- Mod'00 A1 A2 )0 ) .
(**#+END_SRC

** Some notations

#+BEGIN_SRC coq :exports both :results silent **)
  
  Definition PolyV_Mod_rewrite log V V' A1 A2 v a :=
    (@PolyV_Mod log V V' v A1 A2 a).
  Notation "v o>' a" := (@PolyV_Mod_rewrite _ _ _ _ _ v a)
                          (at level 25, right associativity, format "v  o>'  a").
  Notation "v o>| #1| a" :=
    (@GenArrowsMod _ _ _ _ _ a v) (at level 25, right associativity).
  Notation "v o>| 'uMod'" := (@UnitMod _ _ _ v)(at level 25).
  Notation "v o>| @ 'uMod' A" :=
    (@UnitMod _ _ A v) (at level 25, only parsing).
  Definition PolyMod_rewrite log V A2 A1 A1' W WV wv a_ a' :=
    (@PolyMod log V A2 A1 a_ A1' W WV wv a').
  Notation "v o>| a_ o>Mod a'" :=
    (@PolyMod_rewrite _ _ _ _ _ _ _ v a_ a')
      (at level 25, right associativity, a_ at next level, format "v  o>|  a_  o>Mod  a'").
  Notation "v o>| ''D1|' a" := (@UnitDeClass _ _ _ _ _ v a)
                                 (at level 25, right associativity).
  Definition PolyDeClass_rewrite log V B A A' W WV wv b a :=
    (@PolyDeClass log V B A b A' W WV wv a).
  Notation "v o>| b o>D a" :=
    (@PolyDeClass_rewrite _ _ _ _ _ _ _ v b a)
      (at level 25, right associativity, b at next level, format "v  o>|  b  o>D  a").
  Notation "v o>| 'clfy o>Mod a'" :=
    (@Classifying _ _ _ _ _ v a') (at level 25, right associativity).
  Notation "v o>| a_ o>Mod 'declfy" :=
    (@DeClassifying _ _ _ _ _ v a_) (at level 25, a_ at next level, right associativity).

(**#+END_SRC

** More functional-monoidal logic

More description of the functional-monoidal logic which is assumed. These equations
are decidable by coherence lemmas ...

#+BEGIN_SRC coq :exports both :results silent **)
  
  Parameter PolyV_unitPre :
    forall {log : logic} {V V' : obV log} (v : log.-V(0 V |- V')0), log.-1 o> v ~~ v.
  Parameter PolyV_unitPost :
    forall {log : logic} {V V' : obV log} (v : log.-V(0 V |- V')0), v o> log.-1 ~~ v.

  Definition desIdenObLK :
    forall {log : logic} {V : obV log}, log.-V(0 log.-(0 log.-I & V )0 |- V )0
    := fun log V => Des (log.-uV) .
  Parameter desIdenObLKV :
    forall {log : logic} {V : obV log}, log.-V(0 V |- log.-(0 log.-I & V )0 )0 .

  Axiom desIdenObLK_K : forall {log : logic} {V : obV log},
      log.-1 ~~ (@desIdenObLK log V) o> (@desIdenObLKV log V).

  Axiom desIdenObLKV_K : forall {log : logic} {V : obV log},
      log.-1 ~~ (@desIdenObLKV log V) o> (@desIdenObLK log V).

  Axiom desIdenObLKV_Assoc_Rev_desIdenObLK : forall {log : logic} (V W : obV log),
      log.-1 ~~ ( ( log.-(1 desIdenObLKV & V )0 o> Assoc_Rev ) o> desIdenObLK
                  : log.-V(0 log.-(0 W & V )0 |- log.-(0 W & V )0 )0 ).
  
  Parameter desIdenObRK :
    forall {log : logic} {V : obV log}, log.-V(0 log.-(0 V & log.-I )0 |- V )0.

  Parameter desIdenObRKV :
    forall {log : logic} {V : obV log}, log.-V(0 V |- log.-(0 V & log.-I )0 )0. 
  
  Parameter desV01 : forall {log : logic} {V2 V2' V1 : obV log},
      log.-V(0 V2 |- V2' )0 -> log.-V(0 log.-(0 V1 & V2 )0 |- log.-(0 V1 & V2' )0 )0.
  Notation  "dat .-(0 V1 & v )1" := (@desV01 dat _ _ V1 v)
                                      (at level 30, format "dat .-(0  V1  &  v  )1").
  Notation  "(0 V1 & v )1" := (_ .-(0 V1 & v )1)
                                (at level 30, format "(0  V1  &  v  )1").
  Axiom desV01_consV10 :
    forall {log : logic} (V2 V2' V1 : obV log) (v : log.-V(0 V2' |- V2 )0) (W : obV log)
      (w : log.-V(0 log.-(0 V1 & V2 )0 |- W )0),
      Des( [1 v ~> W ]0 <o (Cons w) ) ~~ w <o log.-(0 V1 & v )1 .

  Axiom desIdenObLKV_IdenOb_Assoc_Rev_desIdenObLK : forall {log : logic} (V : obV log),
      log.-1 ~~ ( ( (log.-(1 desIdenObLKV & V )0)
                      o> Assoc_Rev ) o> (log.-(0 log.-I & desIdenObLK )1)
                  : log.-V(0 log.-(0 log.-I & V )0 |- log.-(0 log.-I & V )0 )0 ).

(**#+END_SRC

** The generated conversion relations over the morhisms

The grammatical description of polymorph coparametrism functor, secondo the conversion
relations over the morphisms :

#+BEGIN_SRC coq :exports both :results silent **)
  
  Reserved Notation "f2 ~~~ f1" (at level 70).

  Inductive convMod {log : logic} : forall (V : obV log) (A1 A2 : obMod),
      'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> Prop :=

  | Mod_ReflV : forall (V : obV log) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
      a ~~~ a

  | Mod_TransV : forall (V : obV log) (A1 A2 : obMod)
               (uTrans a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
      uTrans ~~~ a -> forall (a0 : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        a0 ~~~ uTrans -> a0 ~~~ a

  | Mod_SymV : forall (V : obV log) (A1 A2 : obMod) (a a0 : 'Mod(0 V |- [0 A1 ~> A2]0 )0),
      a ~~~ a0 -> a0 ~~~ a

  | PolyV_Mod_cong : forall (A1 A2 : obMod) (V V' : obV log) (v v0 : V(0 V' |- V )0)
                       (a a0 : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
      v0 ~~ v -> a0 ~~~ a -> ( v0 o>' a0 ) ~~~ ( v o>' a )

  | GenArrowsMod_cong : forall (V V' : obV log), forall (A1 A2 : obMod_gen) (aGen : Mod_gen V A1 A2)
      , forall (v v0 : V(0 V' |- V )0), v0 ~~ v -> v0 o>| #1| aGen ~~~ v o>| #1| aGen

  | UnitMod_cong : forall (V : obV log), forall {A : obMod} (v v0 : V(0 V |- log.-I )0),
        v0 ~~ v -> v0 o>| @uMod A ~~~ v o>| @uMod A

  | Mod_cong :
      forall (V : obV log) (A A' : obMod) (a_ a_0 : 'Mod(0 V |- [0 A ~> A' ]0 )0),
      forall (W : obV log) (A'' : obMod) (a' a'0 : 'Mod(0 W |- [0 A' ~> A'' ]0 )0),
      forall (WV : obV log) (v v0 : V(0 WV |- (0 W & V )0 )0),
        v0 ~~ v -> a_0 ~~~ a_ -> a'0 ~~~ a' -> ( v0 o>| a_0 o>Mod a'0 ) ~~~ ( v o>| a_ o>Mod a' )

  | UnitDeClass_cong :
      forall (A : obMod) (A' : obMod) (W W' : obV log) (v v0 : V(0 W' |- (0 W & log.-I )0 )0) (a a0 : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        v0 ~~ v -> a0 ~~~ a -> ( v0 o>| 'D1| a0 ) ~~~ ( v o>| 'D1| a )

  | PolyDeClass_cong :
      forall (V : obV log) (B : obMod) (A : obMod) (b b0 : 'D(0 V |- [0 B ~> A ]0 )0),
      forall (W : obV log) (A' : obMod) (a a0 : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v v0 : V(0 WV |- (0 W & V )0 )0),
        v0 ~~ v -> b0 ~~~ b -> a0 ~~~ a -> ( v0 o>| b0 o>D a0 ) ~~~ ( v o>| b o>D a )

  | Classifying_cong :
      forall (V V' : obV log) (v v0 : V(0 V' |- V )0) (A1 A2 : obMod) (a a0 : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        v0 ~~ v -> a0 ~~~ a -> (v0 o>| 'clfy o>Mod a0 ) ~~~ (v o>| 'clfy o>Mod a )

  | DeClassifying_cong :
      forall (V V' : obV log) (v v0 : V(0 V' |- V )0) (A1 A2 : obMod) (a a0 : 'D(0 V |- [0 A1 ~> A2 ]0 )0),
        v0 ~~ v -> a0 ~~~ a -> (v0 o>| a0 o>Mod 'declfy ) ~~~ (v o>| a o>Mod 'declfy )

  | GenArrowsMod_arrowLog : forall (V V' V'' : obV log) (A1 A2 : obMod_gen) (aGen : Mod_gen V A1 A2)
                              (v : V(0 V' |- V )0) (v' : V(0 V'' |- V' )0),
      ( ( v' o> v) o>| #1| aGen )
        ~~~ (v' o>' (v o>| #1| aGen)
            : 'Mod(0 V'' |- [0 #0| A1 ~> #0| A2 ]0)0 )

  | UnitMod_arrowLog : forall (V V' : obV log) (A : obMod) (v : V(0 V |- log.-I )0)
                         (v' : V(0 V' |- V )0),
      ( ( v' o> v ) o>| @uMod A )
        ~~~ (v' o>' (v o>| @uMod A)
            : 'Mod(0 V' |- [0 A ~> A ]0)0 )

  | Mod_arrowLog :
      forall (V : obV log) (A0 : obMod) (A : obMod)
        (a_ : 'Mod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obMod) (a' : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
      forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
        ( ( v0 o> v ) o>| a_ o>Mod a' )
          ~~~ ( v0 o>' ( v o>| a_ o>Mod a' )
                : 'Mod(0 WV0 |- [0 A0 ~> A' ]0)0 )

  | Mod_arrowPre :
      forall (V V' : obV log) (v : V(0 V' |- V )0) (A0 : obMod) (A : obMod)
        (a_ : 'Mod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obMod) (a' : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
        ( ( v0 o> log.-(0 _ & v )1 ) o>| a_ o>Mod a' )
          ~~~ ( v0 o>| ( v o>' a_ ) o>Mod a'
                : 'Mod(0 WV' |- [0 A0 ~> A' ]0)0 )

  | Mod_arrowPost :
      forall (V : obV log) (A0 : obMod) (A : obMod) (a_ : 'Mod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obMod)
        (a' : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
        ( ( w0 o> log.-(1 w & _ )0 ) o>| a_ o>Mod a' )
          ~~~ ( w0 o>| a_ o>Mod ( w o>' a' )
                : 'Mod(0 W'V |- [0 A0 ~> A' ]0)0 )

  | UnitDeClass_arrowLog :
      forall (W W' W'' : obV log) (w : V(0 W' |- (0 W & log.-I )0 )0)
        (w' : V(0 W'' |- W' )0)
          (A A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        ( ( w' o> w ) o>| 'D1| a )
          ~~~ (  w' o>' ( w o>| 'D1| a )
                : 'D(0 W'' |- [0 'D0| A ~> A' ]0)0 )

  | UnitDeClass_arrow :
      forall (W W' W'' : obV log) (w : V(0 W' |- W )0)
        (w' : V(0 W'' |- (0 W' & log.-I )0 )0)
          (A A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        ( ( w' o> log.-(1 w & log.-I )0 ) o>| 'D1| a )
          ~~~ (  w' o>| 'D1| ( w o>' a)
                : 'D(0 W'' |- [0 'D0| A ~> A' ]0)0 )

  | DeClass_arrowLog :
      forall (V : obV log) (B : obMod) (A : obMod)
        (b : 'D(0 V |- [0 B ~> A ]0 )0),
      forall (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
      forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
        ( ( v0 o> v ) o>| b o>D a )
          ~~~ ( v0 o>' ( v o>| b o>D a )
                : 'D(0 WV0 |- [0 B ~> A' ]0)0 )

  | DeClass_arrowPre :
      forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
        (b : 'D(0 V |- [0 B ~> A ]0 )0),
      forall (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
        ( ( v0 o> log.-(0 _ & v )1 ) o>| b o>D a )
          ~~~ ( v0 o>| ( v o>' b ) o>D a
                : 'D(0 WV' |- [0 B ~> A' ]0)0 )

  | DeClass_arrowPost :
      forall (V : obV log) (B : obMod) (A : obMod) (b : 'D(0 V |- [0 B ~> A ]0 )0),
      forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obMod)
        (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
        ( ( w0 o> log.-(1 w & _ )0 ) o>| b o>D a )
          ~~~ ( w0 o>| b o>D ( w o>' a )
                : 'D(0 W'V |- [0 B ~> A' ]0)0 )

  | Classifying_arrowLog : forall (V V' V'' : obV log) (v : V(0 V' |- V )0) (v0 : V(0 V'' |- V' )0)
                             (A1 A2 : obMod)
                          (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
      ( ( v0 o> v ) o>| 'clfy o>Mod a )
        ~~~ ( v0 o>' ( v o>| 'clfy o>Mod a ) 
              : 'Mod(0 V'' |- [0 'D0| A1 ~> A2 ]0)0 )

  | Classifying_arrow : forall (V V' V'' : obV log) (v : V(0 V' |- V )0)
                          (v0 : V(0 V'' |- V' )0) (A1 A2 : obMod)
                          (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v0 o> v ) o>| 'clfy o>Mod a )
          ~~~ ( v0 o>| 'clfy o>Mod ( v o>' a )
                : 'Mod(0 V'' |- [0 'D0| A1 ~> A2 ]0)0 )

  | DeClassifying_arrowLog :
      forall (V V' V'' : obV log) (v : V(0 V' |- V )0) (v0 : V(0 V'' |- V' )0) (A1 A2 : obMod)
        (a : 'D(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v0 o> v ) o>| a o>Mod 'declfy )
        ~~~ ( v0 o>' ( v o>| a o>Mod 'declfy )
                : 'D(0 V'' |- [0 A1 ~> 'D0| A2 ]0)0 )

  | DeClassifying_arrow :
      forall (V V' V'' : obV log) (v : V(0 V' |- V )0) (v0 : V(0 V'' |- V' )0) (A1 A2 : obMod)
        (a : 'D(0 V |- [0 A1 ~> A2 ]0 )0),
      ( ( v0 o> v ) o>| a o>Mod 'declfy )
        ~~~ ( v0 o>| ( v o>' a ) o>Mod 'declfy
              : 'D(0 V'' |- [0 A1 ~> 'D0| A2 ]0)0 )

  | PolyV_Mod_arrowLog :
      forall (V'' V' : obV log) (v' : V(0 V'' |- V' )0) (V : obV log)
        (v : V(0 V' |- V )0) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v' o> v ) o>' a )
          ~~~ ( v' o>' ( v o>' a )
                : 'Mod(0 V'' |- [0 A1 ~> A2 ]0)0 )

  (* non for reduction *)
  | Mod_morphism :
      forall (V : obV log) (B : obMod) (A : obMod) (b : 'Mod(0 V |- [0 B ~> A ]0 )0)
        (W_ : obV log) (A' : obMod) (a_ : 'Mod(0 W_ |- [0 A ~> A' ]0 )0)
        (W' : obV log) (A'' : obMod) (a' : 'Mod(0 W' |- [0 A' ~> A'' ]0 )0),
      forall (W_V : obV log) (v : V(0 W_V |- (0 W_ & V )0 )0),
      forall (W'W_V : obV log) (v0 : V(0 W'W_V |- (0 W' & W_V )0 )0),
        ( ( v0 o> (0 W' & v )1 o> Assoc ) o>| b o>Mod ( log.-1 o>| a_ o>Mod a' ) )
          ~~~ ( v0 o>| ( v o>| b o>Mod a_ ) o>Mod a'
                : 'Mod(0 W'W_V |- [0 B ~> A'' ]0)0 )

  | DeClass_morphismPost :
      forall (A : obMod)
        (W_ W_' : obV log) (v : V(0 W_' |- (0 W_ & log.-I )0 )0) (A' : obMod) (a_ : 'Mod(0 W_ |- [0 A ~> A' ]0 )0)
        (W' : obV log) (A'' : obMod) (a' : 'Mod(0 W' |- [0 A' ~> A'' ]0 )0),
      forall (W'W_' : obV log) (v0 : V(0 W'W_' |- (0 W' & W_' )0 )0),
        ( ( v0 o> desIdenObRKV ) o>| 'D1| ( (log.-1) o>| ( ( v o> desIdenObRK ) o>' a_ ) o>Mod a' )  )
          ~~~ ( v0 o>| ( v o>| 'D1| a_ ) o>D a'
                : 'D(0 W'W_' |- [0 'D0| A ~> A'' ]0)0 )

  | DeClass_morphismPre :
      forall (A : obMod) (V' : obV log) (B' : obMod) (b' : 'D(0 V' |- [0 B' ~> A ]0 )0),
      forall (W W' : obV log) (v : V(0 W' |- (0 W & log.-I )0 )0) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (W'V' : obV log) (v0 : V(0 W'V' |- (0 W' & V' )0 )0),
        ( v0  o>| b' o>D ( ( v o> desIdenObRK )  o>' a ) )
          ~~~ ( v0 o>| b' o>Mod ( v o>| 'D1| a )
                : 'D(0 W'V' |- [0 B' ~> A' ]0)0 )

  | PolyV_Mod_unit :
      forall (V : obV log) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( a ) ~~~ ( log.-1 o>' a
                    : 'Mod(0 V |- [0 A1 ~> A2 ]0)0 )

  | Mod_unit :
      forall (A : obMod) (V : obV log) (v : V(0 V |- log.-I )0)
        (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
        ( ( v0 o> log.-(0 W & v )1 o> desIdenObRK ) o>' a )
          ~~~ ( v0 o>| ( v o>| uMod ) o>Mod a
                : 'Mod(0 WV |- [0 A ~> A' ]0)0 )

  | Mod_inputUnitMod :
      forall (V : obV log) (B : obMod) (A : obMod) (b : 'Mod(0 V |- [0 B ~> A ]0 )0),
      forall (W : obV log) (w : V(0 W |- log.-I )0),
      forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
        ( ( w0 o> log.-(1 w & V )0 o> desIdenObLK ) o>' b )
          ~~~  ( w0 o>| b o>Mod ( w o>| uMod )
                 : 'Mod(0 WV |- [0 B ~> A ]0)0 )

  | DeClass_unit :
      forall (V : obV log) (v : V(0 V |- log.-I )0) (A : obMod) (A' : obMod) (W : obV log) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
        ( ( v0 o> log.-(0 W & v )1 ) o>| 'D1| a )
          ~~~ ( v0 o>| ( v o>| uMod ) o>D a
                : 'D(0 WV |- [0 'D0| A ~> A' ]0 )0 )

  | DeClass_inputUnitMod :
      forall (V : obV log) (B : obMod) (A : obMod) (b : 'D(0 V |- [0 B ~> A ]0 )0),
        forall (W : obV log) (w : V(0 W |- log.-I )0),
      forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
        ( ( w0 o> ( log.-(1 w & _ )0 ) o> desIdenObLK ) o>' b )
          ~~~ ( w0 o>| b o>D ( w o>| uMod )
                : 'D(0 WV |- [0 B ~> A ]0)0 )

  | Classifying_morphismPre :
      forall (V V' : obV log) (v : V(0 V' |- V )0 ) (A1 A2 : obMod) (a_ : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
        (W : obV log) (A3 : obMod) (a' : 'Mod(0 W |- [0 A2 ~> A3 ]0 )0),
      forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
        ( ( log.-1 ) o>| 'clfy o>Mod ( ( v0 o> (0 _ & v )1 ) o>| a_ o>Mod a' ) )
          ~~~ ( v0 o>| (v o>| 'clfy o>Mod a_ ) o>Mod a'
                : 'Mod(0 WV' |- [0 'D0| A1 ~> A3 ]0)0 )

  (* non-necessary, deductible *)
  | Classifying_morphismPre_DeClass :
      forall (V V' : obV log) (v : V(0 V' |- V )0 ) (A1 A2 : obMod) (b : 'D(0 V |- [0 A1 ~> A2 ]0 )0)
        (W : obV log) (A3 : obMod) (a' : 'Mod(0 W |- [0 A2 ~> A3 ]0 )0),
      forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
        ( ( log.-1 ) o>| 'clfy o>Mod ( ( v0 o> (0 _ & v )1 ) o>| b o>D a' ) )
          ~~~ ( v0 o>| (v o>| 'clfy o>Mod b ) o>D a'
              : 'D(0 WV' |- [0 'D0| A1 ~> A3 ]0)0 )

  | Classifying_morphismPost :
      forall (V V' : obV log) (v : V(0 V' |- (0 V & log.-I )0 )0) (A1 A2 : obMod) (a_ : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
        (W W' : obV log) (w : V(0 W' |- W )0) (A3 : obMod) (a' : 'Mod(0 W |- [0 A2 ~> A3 ]0 )0),
      forall (W'V' : obV log) (v0 : V(0 W'V' |- (0 W' & V' )0 )0),
        ( ( log.-1 )
            o>| 'clfy o>Mod ( v0 o>| ( ( v o> desIdenObRK ) o>' a_ ) o>Mod (w o>' a') ) )
          ~~~ ( v0 o>| ( v o>| 'D1| a_ ) o>Mod ( w o>| 'clfy o>Mod a' )
                : 'Mod(0 W'V' |- [0 'D0| A1 ~> A3 ]0)0 ) 

  | DeClassifying_morphismPost :
      forall (V : obV log) (A1 A2 : obMod) (b_ : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
        (W W' : obV log) (w : V(0 W' |- W )0) (A3 : obMod) (b' : 'D(0 W |- [0 A2 ~> A3 ]0 )0),
      forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
        ( log.-1 o>| ( ( w0 o> (1 w & _ )0 ) o>| b_ o>Mod b' ) o>Mod 'declfy )
          ~~~ ( w0 o>| b_ o>Mod ( w o>| b' o>Mod 'declfy )
                : 'D(0 W'V |- [0 A1 ~> 'D0| A3 ]0)0 )

  | DeClassifying_morphismPre :
      forall (V V' : obV log) (v : V(0 V' |- V )0) (A1 A2 : obMod) (b_ : 'D(0 V |- [0 A1 ~> A2 ]0 )0)
        (W W' : obV log) (w : V(0 W' |- (0 W & log.-I )0 )0) (A4 : obMod) (b' : 'Mod(0 W |- [0 A2 ~> A4 ]0 )0),
      forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
        ( log.-1 o>| ( wv o>| ( v o>' b_ ) o>D ( ( w o> desIdenObRK ) o>' b') ) o>Mod 'declfy )
          ~~~ ( wv o>| ( v o>| b_ o>Mod 'declfy ) o>D ( w o>| 'D1| b' )
              : 'D(0 W'V' |- [0 A1 ~> 'D0| A4 ]0)0 )

  | CancelOuter : forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
                    (b : 'D(0 V |- [0 B ~> A ]0 )0) (A' : obMod)
                    (W W' : obV log) (w : V(0 W' |- W )0) (a : 'Mod(0 W |- [0 'D0| A ~> A' ]0 )0),
      forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
     ( wv o>| ( v o>' b ) o>Mod ( w o>' a ) )
       ~~~ ( wv o>| ( v o>| b o>Mod 'declfy ) o>Mod ( w o>| 'clfy o>Mod a )
                          : 'Mod(0 W'V' |- [0 B ~> A' ]0)0 )

  | CancelInner : forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
                    (b : 'D(0 V |- [0 B ~> A ]0 )0) (A' : obMod)
                    (W W' : obV log) (w : V(0 W' |- W )0) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
      ( wv o>| (v o>' b) o>D (w o>' a) )
        ~~~ ( wv o>| (v o>| b o>Mod 'declfy ) o>D (w o>| 'clfy o>Mod a )
                        : 'D(0 W'V' |- [0 B ~> A' ]0)0 )

  | PermOuterInner : forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
                       (b : 'D(0 V |- [0 B ~> A ]0 )0) (W W' : obV log) (w : V(0 W' |- W )0)
                       (u : V(0 W |- log.-I )0),
      forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
      ( wv o>| ( ( log.-(1 w & _ )0 o> log.-(1 u & _ )0 o> desIdenObLK ) o>| ( v o>' b ) o>Mod 'declfy ) o>Mod 'declfy )
        ~~~ ( wv o>| ( v o>| b o>Mod 'declfy ) o>D ( w o>| (u o>| uMod) o>Mod 'declfy )
              : 'D(0 W'V' |- [0 B ~> 'D0| 'D0| A ]0)0 )

  where "f2 ~~~ f1" := (@convMod _ _ _ _ f2 f1).

  Hint Constructors convMod.

  Hint Extern 4 (_ ~~?lo` _) => eapply (@ReflV lo _).
  Ltac rewriterMod := repeat match goal with | [ HH : @eq (Mod00 _ _ _) _ _  |- _ ] =>  try rewrite -> HH in *; clear HH end. 

(**#+END_SRC

Descriptions for the congruent rewriting tactics :

#+BEGIN_SRC coq :exports both :results silent **)

  Add Parametric Relation {log : logic} (V : obV log) (A1 A2 : obMod) :
    ('Mod(0 V |- [0 A1 ~> A2 ]0 )0) (@convMod log V A1 A2)
        reflexivity proved by (@Mod_ReflV log V A1 A2)
        symmetry proved by (@Mod_SymV log V A1 A2)
        transitivity proved by
        (fun x y z r1 r2 =>  ((@Mod_TransV log V A1 A2) y z r2 x r1))
          as convMod_rewrite.

  Add Parametric Relation {log : logic} (V1 V2 : obV log) :
    (log.-V(0 V1 |- V2 )0) (@convV log V1 V2)
      reflexivity proved by (@ReflV log log V1 V2)
      symmetry proved by (fun x => (@SymV log log V1 V2)^~ x)
      transitivity proved by
      (fun x y z r1 r2 =>  ((@TransV log log V1 V2) y z r2 x r1))
        as convV_rewrite.

  Add Parametric Morphism {log : logic} (V V' : obV log) (A1 A2 : obMod) :
    (@PolyV_Mod_rewrite log V V' A1 A2) with
      signature ((@convV log V' V)
                   ==> (@convMod log V A1 A2)
                   ==> (@convMod log V' A1 A2))
        as PolyV_Mod_cong_rewrite.
      by move => *; apply: PolyV_Mod_cong. Qed.

  Add Parametric Morphism {log : logic} (V V' : obV log) (A1 A2 : obMod_gen)
      (aGen : Mod_gen V A1 A2) :
    (@GenArrowsMod log V V' A1 A2 aGen) with
      signature ((@convV log V' V)
                   ==> (@convMod log V' (#0| A1) (#0| A2)))
        as GenArrowsMod_cong_rewrite.
      by move => *; apply: GenArrowsMod_cong. Qed.

  Add Parametric Morphism {log : logic} (V : obV log) (A : obMod)
    : (@UnitMod log V A) with
      signature ((@convV log V log.-I)
                   ==> (@convMod log V A A))
        as UnitMod_cong_rewrite.
      by move => *; apply: UnitMod_cong. Qed.

  Add Parametric Morphism {log : logic} (V : obV log) (A A' : obMod)
      (W : obV log) (A'' : obMod) (WV : obV log) :
    (@PolyMod_rewrite log V A A' A'' W WV ) with
      signature ((@convV log WV ((0 W & V)0) )
                 ==>(@convMod log V A A')
                 ==> (@convMod log W A' A'')
                 ==> (@convMod log WV A A''))
        as Mod_cong_rewrite.
      by move => *; apply: Mod_cong. Qed.

  Add Parametric Morphism {log : logic} (A A' : obMod) (W W' : obV log) :
    (@UnitDeClass log A A' W W') with
      signature ( (@convV log W' ((0 W & log.-I )0) )
                    ==> (@convMod log W A A')
                    ==> (@convMod log W' ('D0| A) ('D0| A')))
        as UnitDeClass_cong_rewrite.
      by move => *; apply: UnitDeClass_cong. Qed.

  Add Parametric Morphism {log : logic} (V : obV log) (B A A' : obMod) (W WV : obV log) :
    (@PolyDeClass_rewrite log V B A A' W WV) with
      signature ((@convV log WV ((0 W & V )0) )
                   ==> (@convMod log V B ('D0| A))
                   ==> (@convMod log W A A')
                   ==> (@convMod log WV B ('D0| A')))
        as PolyDeClass_cong_rewrite.
      by move => *; apply: PolyDeClass_cong. Qed.

  Add Parametric Morphism {log : logic} (V V' : obV log) (A1 A2 : obMod) :
    (@Classifying log V V' A1 A2) with
      signature ((@convV log V' V)
                   ==> (@convMod log V A1 A2)
                   ==> (@convMod log V' ('D0| A1) A2))
        as Classifying_cong_rewrite.
      by move => *; apply: Classifying_cong. Qed.

  Add Parametric Morphism {log : logic} (V V' : obV log) (A1 A2 : obMod) :
    (@DeClassifying log V V' A1 A2) with
      signature ((@convV log V' V)
                   ==> (@convMod log V A1 ('D0| A2))
                   ==> (@convMod log V' A1 ('D0| ('D0| A2))))
        as DeClassifying_cong_rewrite.
      by move => *; apply: DeClassifying_cong. Qed.

(**#+END_SRC

* Iterated constructors

** Indexed list, lemmas

Some definitions :

#+BEGIN_SRC coq :exports both :results silent **)

  Module Import Destruct_hlist.

    Inductive hlist (A : Type) (B  : A -> Type)
    : list A -> Type :=
    | HNil : hlist B nil
    | HCons : forall (x : A) (ls : list A), B x -> hlist B ls -> hlist B (x :: ls).

    Implicit Arguments HNil [A B].
    Implicit Arguments HCons [A B x ls].

    Infix ":::" := HCons (right associativity, at level 60).

    Section Section1.
      Variable (A : Type) (B1 B2 : A -> Type).
      Variable f : forall x, B1 x -> B2 x.

      Fixpoint hmap (ls : list A) (hl : hlist B1 ls) : hlist B2 ls :=
        match hl with
        | HNil => HNil
        | HCons _ _ x hl' => f x ::: hmap hl'
        end.
    End Section1.

    Implicit Arguments hmap [A B1 B2 ls].

(**#+END_SRC

Lemmas for (dependent-)destruction by inner instantiations of indices :

#+BEGIN_SRC coq :exports both :results silent **)

    Section Section2.

    Variables (A : Type) (B  : A -> Type).

    Inductive hlist_nil : hlist B ( [::]) -> Type :=
    | Hlist_nil : hlist_nil (HNil : hlist B [::]).

    Inductive hlist_cons : forall (a : A) (ls' : list A), hlist B (a :: ls') -> Type :=
    | Hlist_cons : forall a ls' (ba : B a) (hls' : hlist B ls'),
          @hlist_cons a ls' (ba ::: hls' : hlist B ([:: a & ls'])).

    Definition hlist_destructP_type : forall (ls : list A) (hls : hlist B ls), Type.
    Proof.
      move => ls. case : ls => [ | a ls'] hls.
      - refine (@hlist_nil hls).
      - refine (@hlist_cons a ls' hls).
    Defined.

    Definition hlist_destructP : forall (ls : list A) (hls : hlist B ls),
        @hlist_destructP_type ls hls.
    Proof.
      move => ls hls. case: ls / hls.
      rewrite /hlist_destructP_type /=.
      - constructor.
      - constructor.
    Defined.

    (* type indeed computes: ... 
    Definition hlist_cons_destructP (a : A) (ls' : list A)
               (hls : hlist B (a :: ls')) :
      (@hlist_cons a ls' hls).
    Proof.
      apply: (hlist_destructP hls ).
    Defined. *)

    Definition hlist_eta_type : forall  (ls : list A) (hls : hlist B ( ls)), Type.
    Proof.
      move => ls hls. refine (hls = _ ). move: hls. case: ls.
      - move => _ . exact: HNil.
      - move => a ls' hls'. refine (_ ::: _).
        + case: a ls' hls' / (hlist_destructP hls') => a ls' ba _.
          exact: ba. (* hhd *)
        + case: a ls' hls' / (hlist_destructP hls') => a ls' _ hls'.
          exact: hls'. (* htl *)
    Defined. 

    Lemma hlist_eta : forall  (ls : list A) (hls : hlist B ( ls)),
        @hlist_eta_type ls hls.
    Proof.
      move => ls hls. case: ls / hls.
      rewrite /hlist_eta_type. reflexivity.
      rewrite /hlist_eta_type. reflexivity.
    Defined.

    (* memo: may .. *)
    Definition tl_hlist_type : forall  (ls : list A) (hls : hlist B ( ls)), Type.
    Proof.
      move => ls. case: ls.
      - move => _ . refine (hlist B [::]).
      - move => a ls' hls'. refine (hlist B ls').
    Defined.

    Definition tl_hlist : forall  (ls : list A) (hls : hlist B ( ls)), tl_hlist_type hls.
    Proof.
      move => ls. case: ls => /=.
      - move => hls. exact: hls.
      - move => a ls' hls. case: a ls' hls / (hlist_destructP hls) => a ls' _ hls'.
        exact: hls'.
    Defined.
    
    End Section2.

  End Destruct_hlist.
  
(**#+END_SRC

** Chained lists, lemmas

Some definitions :

#+BEGIN_SRC coq :exports both :results silent **)
  
  Fixpoint chain (T : Type) (ls : list T) {struct ls} : list (prod T T) :=
    match ls with
    | nil => nil
    | cons t0 ls' => match ls' with
                    | nil => nil
                    | cons t1 ls'' => (t0, t1) :: chain ls'
                    end 
    end.

  Arguments chain : simpl nomatch.
  Eval compute in chain [:: 0; 11; 2; 3].

  Inductive chain_graph (T : Type) : list T -> list (prod T T) -> Type :=
  | Chain_nil :  chain_graph [::] (chain [::])
  | Chain_cons_nil :  forall t0 : T, chain_graph [:: t0] (chain [:: t0])
  | Chain_cons_cons : forall (t0 t1 : T) (ls'' : list T),
        chain_graph (t1 :: ls'') (chain ([:: t1 & ls'']))
        -> chain_graph (t0 :: t1 :: ls'') ((t0 , t1) :: chain ([:: t1 & ls''])) .

  Lemma chain_graphP (T : Type) :
    forall  (ls : list T), chain_graph ls (chain ls).
  Proof.
    induction ls as [|t0 ls']. constructor 1.
    destruct ls' as [|t1 ls'']. constructor 2.
    simpl.  constructor 3. exact:  IHls'.
  Defined.

  Definition toArrowV {log : logic} {trf : obV log -> obV log}
             (V1V2 : prod (obV log) (obV log))
    := V(0 trf V1V2.1 |- trf V1V2.2 )0.
  
  Definition arrowList {log : logic} {trf : obV log -> obV log} ls
    := (hlist (@toArrowV log trf) (chain ls)).

(**#+END_SRC

Lemmas for (dependent-)destruction by inner instantiations of indices :

#+BEGIN_SRC coq :exports both :results silent **)

  Module Import Destruct_arrowList.
    
    Inductive arrowList_nil {log : logic} {trf : obV log -> obV log}
    : hlist (toArrowV (trf:=trf)) (chain [::]) -> Type :=
    | ArrowList_nil : arrowList_nil (HNil : arrowList [::]).

    Inductive arrowList_cons_nil {log : logic} {trf : obV log -> obV log}
      : forall V0 : (obV log), hlist (toArrowV (trf:=trf)) (chain [:: V0]) -> Type :=
    | ArrowList_cons_nil : forall V0, @arrowList_cons_nil log trf V0 (HNil : arrowList [:: V0]).

    Inductive arrowList_cons_cons {log : logic} {trf : obV log -> obV log}
      : forall (V0 V1 : obV log) (Vs'' : list (obV log)),
        hlist (toArrowV (trf:=trf)) ((V0 , V1) :: (chain (V1 :: Vs''))) -> Type :=
    | ArrowList_cons_cons :
        forall V0 V1 Vs'' (v01 : toArrowV (V0 , V1))
          (vs' : hlist (toArrowV (trf:=trf)) (chain [:: V1 & Vs''])),
          @arrowList_cons_cons log trf V0 V1 Vs''
          (v01 ::: vs' : hlist (toArrowV (trf:=trf)) ((V0 , V1) :: (chain [:: V1 & Vs'']))).

    Definition arrowList_destructP_type {log : logic}{trf : obV log -> obV log} :
      forall (Vs : list (obV log)) (vs : hlist (toArrowV (trf:=trf)) (chain Vs)), Type.
    Proof.
      move => Vs. case: Vs (chain Vs) / (chain_graphP Vs) =>
                 [ | V0 | V0 V1 Vs'' V1Vs''_chain_graph ] vs.
      - refine (@arrowList_nil log trf vs).
      - refine (@arrowList_cons_nil log trf V0 vs).
      - refine (@arrowList_cons_cons log trf V0 V1 Vs'' vs).
    Defined.

    Definition arrowList_destructP {log : logic}{trf : obV log -> obV log} :
      forall (Vs : list (obV log)) (vs : hlist (toArrowV (trf:=trf)) (chain Vs)),
        @arrowList_destructP_type log trf Vs vs.
    Proof.
      move => Vs. rewrite /arrowList_destructP_type.
      case: Vs (chain Vs) / (chain_graphP Vs) =>
      [ | V0 | V0 V1 Vs'' V1Vs''_chain_graph ] vs.
      - case : vs / (hlist_destructP vs). constructor.
      - case : vs / (hlist_destructP vs). constructor.
      - (* /!\ *) rewrite (hlist_eta vs). constructor.
    Defined.

    (* indeed computes: 
    Definition arrowList_cons_cons_destructP {log : logic}{trf : obV log -> obV log} :
      forall V0 V1 Vs'' (vs : hlist (toArrowV (trf:=trf)) (chain [:: V0, V1 & Vs''])),
        @arrowList_cons_cons log trf V0 V1 Vs'' vs.
    Proof.
      move => V0 V1 Vs'' vs. exact: (arrowList_destructP vs).
    Defined. *)

  End Destruct_arrowList.

  Inductive arrowList_prop {log : logic} {trf : obV log -> obV log}
    : forall ls : list (obV log),
      hlist (toArrowV (trf:=trf)) (chain ls) -> Type :=
  | ArrowList_nil : arrowList_prop (HNil : arrowList [::])
  | ArrowList_cons_nil : forall V0, arrowList_prop (HNil : arrowList [:: V0])
  | ArrowList_cons_cons :
      forall V0 V1 (v01 : toArrowV (V0, V1)) Vs'' (vs' : arrowList (V1 :: Vs'')),
        arrowList_prop vs' ->
        arrowList_prop (v01 ::: vs' : arrowList (V0 :: V1 :: Vs'')).

  Lemma arrowListP {log : logic}{trf : obV log -> obV log} :
    forall (Vs : list (obV log)) (vs :arrowList Vs),
      (@arrowList_prop log trf Vs vs).
  Proof.
    move => Vs. move: (chain_graphP Vs) => Vs_chainInputP.
    elim : Vs {-}(chain Vs) / Vs_chainInputP.
    - move => vs. case: (arrowList_destructP vs).
      apply: ArrowList_nil.
    - move => V0 vs. case: V0 vs / (arrowList_destructP vs) => V0.
      apply: ArrowList_cons_nil.
    - intros V0 V1 Vs'' (*ch_V1Vs''_P*) _ IHVs' vs''. move: IHVs'.
      case: V0 V1 Vs'' vs'' / (arrowList_destructP vs'') =>
      V0 V1 Vs'' v01 vs' IHVs'.
      apply: (ArrowList_cons_cons v01 (IHVs' vs')).
  Defined.

(**#+END_SRC

** Iterated constructors

Some definitions :

#+BEGIN_SRC coq :exports both :results silent **)
    
  Definition iterDeClass0 (n : nat) : obMod -> obMod
    := iter n DeClass0 .

  Definition iterDeClassifying {log : logic} {trf : obV log -> obV log}
             (V_dft : obV log) (B A : obMod) 
    : forall (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
        (b : 'D(0 trf (last V_dft Vs) |- [0 B ~> A ]0 )0),
      'D(0 trf(head V_dft Vs) |- [0 B ~> iterDeClass0 (length Vs).-1 A ]0 )0.
  Proof.
    move => Vs vs. move: (arrowListP (trf:=trf) vs) => vs_arrowListP.
    elim : vs_arrowListP => /= .
    - move => b; exact: b.
    - move => V0 b; exact: b.
    - move => V0 V1 v01 Vs'' vs' vs'_arrowListP vs'_IH b.
      refine (v01 o>| (vs'_IH b)  o>Mod 'declfy).
  Defined.

  Notation "vs o>|| a o>Mod ''declfy" :=
    (@iterDeClassifying _ _ _ _ _ _ vs a)
      (at level 25, a at next level, right associativity).
  
  Definition iterDeClassifying_rewrite_type {log : logic}{trf : obV log -> obV log}
             (V_dft : obV log)
             (B A : obMod) (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs))) : Prop.
  Proof.
    case: (arrowListP vs).
    - refine ( forall (b : 'D(0 trf(last V_dft [::]) |- [0 B ~> A ]0 )0),
                 iterDeClassifying (V_dft := V_dft) (HNil : arrowList ([::])) b = b ).
    - move => V0.
      refine ( forall (b : 'D(0 trf(last V0 [::]) |- [0 B ~> A ]0 )0),
                 iterDeClassifying (V_dft := V_dft) (HNil : arrowList ([:: V0])) b = b ).
    - move => V0 V1 v01 Vs'' vs' _ .
      refine ( forall (b : 'D(0 trf(last V1 Vs'') |- [0 B ~> A ]0 )0),
            iterDeClassifying (V_dft := V_dft) (v01 ::: vs' : arrowList (V0 :: V1 :: Vs'')) b
            = v01 o>| ( iterDeClassifying (V_dft := V_dft) vs' b ) o>Mod 'declfy ).
  Defined.

(**#+END_SRC

Some lemmas for the rewrite tactics :

#+BEGIN_SRC coq :exports both :results silent **)

  Lemma iterDeClassifying_rewrite {log : logic}{trf : obV log -> obV log} {V_dft : obV log} {B A : obMod} 
        (Vs : list (obV log)) (vs : arrowList Vs) :
    @iterDeClassifying_rewrite_type log trf V_dft B A Vs vs.
  Proof.
    rewrite /iterDeClassifying_rewrite_type.
    case: (arrowListP vs); reflexivity.
  Defined.

  Notation RHSc := (X in _ ~~~ X)%pattern.
  Notation LHSc := (X in X ~~~ _)%pattern.

  Definition tac_arrows := (@Mod_arrowPre, @Mod_arrowPost,
                            @UnitDeClass_arrow, @DeClass_arrowPre,
                            @DeClass_arrowPost, @Classifying_arrow, @DeClassifying_arrow).

(**#+END_SRC

Some deduced conversion relations over the generated morphisms :

#+BEGIN_SRC coq :exports both :results silent **)

  Hint Extern 4 (_ ~~?lo` _) => eapply (@SymV lo _) : logic_hints.
  Hint Resolve PolyV_unitPost : logic_hints.
  Hint Resolve PolyV_unitPre : logic_hints.

  Lemma GenArrowsMod_arrowLog_id {log : logic} :
    forall (V' V'' : obV log) (A1 A2 : obMod_gen) (aGen : Mod_gen V' A1 A2)
      (v' : V(0 V'' |- V' )0),
      ( ( v' ) o>| #1| aGen )
        ~~~ (v' o>' (log.-1 o>| #1| aGen) ).
  Proof. eauto with logic_hints.   Qed.

  Lemma UnitMod_arrowLog_id {log : logic} :
    forall (V' : obV log) (A : obMod)
      (v' : V(0 V' |- log.-I )0),
      ( ( v' ) o>| @uMod A )
        ~~~ (v' o>' (log.-1 o>| @uMod A) ).
  Proof. eauto with logic_hints. Qed.

  Lemma Mod_arrowLog_id {log : logic} :
    forall (V : obV log) (A0 : obMod) (A : obMod)
      (a_ : 'Mod(0 V |- [0 A0 ~> A ]0 )0),
    forall (W : obV log) (A' : obMod) (a' : 'Mod(0 W |- [0 A ~> A' ]0 )0),
    forall (WV0 : obV log) (v0 : V(0 WV0 |- (0 W & V )0 )0),
      ( ( v0 ) o>| a_ o>Mod a' )
        ~~~ ( v0 o>' ( log.-1 o>| a_ o>Mod a' ) ).
  Proof. eauto with logic_hints.  Qed.

  Lemma UnitDeClass_arrowLog_id {log : logic} :
    forall (W W'' : obV log)
      (w' : V(0 W'' |- (0 W & log.-I )0 )0)
      (A A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      ( ( w' ) o>| 'D1| a )
        ~~~ (  w' o>' ( log.-1 o>| 'D1| a ) ).
  Proof. eauto with logic_hints.  Qed.
  
  Lemma  DeClass_arrowLog_id {log : logic} :
    forall (V : obV log) (B : obMod) (A : obMod)
      (b : 'D(0 V |- [0 B ~> A ]0 )0),
    forall (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
    forall (WV0 : obV log) (v0 : V(0 WV0 |- (0 W & V )0  )0),
      ( ( v0  ) o>| b o>D a )
        ~~~ ( v0 o>' ( log.-1 o>| b o>D a ) ).
  Proof. eauto with logic_hints.  Qed.

  Lemma Classifying_arrowLog_id {log : logic} :
    forall (V' V'' : obV log) (v0 : V(0 V'' |- V' )0)
      (A1 A2 : obMod)
      (a : 'Mod(0 V' |- [0 A1 ~> A2 ]0 )0),
      ( ( v0 ) o>| 'clfy o>Mod a )
        ~~~ ( v0 o>' ( log.-1 o>| 'clfy o>Mod a ) ).
  Proof. eauto with logic_hints.  Qed.

  Lemma DeClassifying_arrowLog_id {log : logic} :
    forall (V' V'' : obV log)  (v0 : V(0 V'' |- V' )0) (A1 A2 : obMod)
      (a : 'D(0 V' |- [0 A1 ~> A2 ]0 )0),
      ( ( v0 ) o>| a o>Mod 'declfy )
        ~~~ ( v0 o>' ( log.-1 o>| a o>Mod 'declfy ) ).
  Proof. eauto with logic_hints.  Qed.

(**#+END_SRC

Some purely-logical lemmas :

#+BEGIN_SRC coq :exports both :results silent **)

  Lemma logic_decidable0 : forall {log : logic} (V : obV log),
      log.-1 ~~log` desIdenObLKV o>`log`>
         log.-(1 log.-1 & V )0 o>`log`> desIdenObLK .
  Admitted.
  Hint Resolve logic_decidable0 : logic_hints.

  Lemma logic_decidable1 : forall {log : logic}
                             (V W _WV WV : obV log)
                             (w : log.-V(0 WV |- log.-(0 W & V )0 )0)
                             (w0 : log.-V(0 _WV |- WV )0),
      w0 o>`log`> w ~~log` log.-1 o>`log`> (w0 o>`log`> w) o>`log`> log.-(1 log.-1 & V )0.
  Admitted.
  Hint Resolve logic_decidable1 : logic_hints.
  
  Lemma logic_decidable2 : forall {log : logic}
                             (V W WV' : obV log)
                             (v0 : log.-V(0 WV' |- log.-(0 W & V )0 )0),
      v0 ~~log` (v0 o>`log`> log.-(1 desIdenObRKV & V )0)
         o>`log`> log.-(1 log.-1 o>`log`> desIdenObRK & V )0.
  Admitted.
  Hint Resolve logic_decidable2 : logic_hints.

  Lemma logic_decidable3 : forall {log : logic}
                             (W' W_ W'W_ : obV log)
                             (v : log.-V(0 W'W_ |- log.-(0 W' & W_ )0 )0)
                             (W'W_I : obV log)
                             (v0 : log.-V(0 W'W_I |- log.-(0 W'W_ & log.-I )0 )0),
      v0 o>`log`> log.-(1 v & log.-I )0 ~~log`
         ((v0 o>`log`> log.-(1 v & log.-I )0 o>`log`> Assoc_Rev) o>`log`> desIdenObRKV)
         o>`log`> log.-(1 log.-1 o>`log`> (0 W' & log.-1 o>`log`> desIdenObRK )1 & log.-I )0.
  Admitted.
  Hint Resolve logic_decidable3 : logic_hints.

  Lemma logic_decidable4 : forall {log : logic}
                             (V W_ W' W'W_ : obV log)
                             (v : log.-V(0 W'W_ |- log.-(0 W' & W_ )0 )0)
                             (W'W_V : obV log)
                             (v0 : log.-V(0 W'W_V |- log.-(0 W'W_ & V )0 )0),
      v0 o>`log`> log.-(1 v & V )0 ~~log` (v0 o>`log`> log.-(1 v & V )0 o>`log`> Assoc_Rev)
         o>`log`> (0 W' & log.-1 )1 o>`log`> Assoc .
  Admitted.
  Hint Resolve logic_decidable4 : logic_hints.

  Lemma logic_decidable7 :
    forall {log : logic} (Vb Vb' : obV log) (vb : log.-V(0 Vb' |- Vb )0) (V0Vb' trfV0 trfV1 : obV log)
      (v01 : log.-V(0 trfV0 |- trfV1 )0) (v0b : log.-V(0 V0Vb' |- log.-(0 trfV0 & Vb' )0 )0),
      
(v0b o>`log`> (0 trfV0 & vb )1) o>`log`> log.-(1 v01 & Vb )0 ~~log`
(((((v0b o>`log`> log.-(1 desIdenObRKV & Vb' )0) o>`log`> 
log.-(1 (log.-1 o>`log`> log.-(1 v01 o>`log`> desIdenObLKV & log.-I )0 
o>`log`> Assoc_Rev) o>`log`> 
log.-(1 desIdenObRKV & log.-(0 trfV1 & log.-I )0 )0 & Vb' )0 
o>`log`> Assoc_Rev) o>`log`> (0 log.-(0 log.-I & log.-I )0 & 
(log.-1 o>`log`> log.-(1 log.-1 o>`log`> desIdenObRK & Vb' )0) 
o>`log`> log.-(1 desIdenObRKV & Vb' )0 )1 o>`log`> Assoc) 
o>`log`> (0 log.-(0 log.-(0 log.-I & log.-I )0 & 
log.-(0 trfV1 & log.-I )0 )0 & vb )1) o>`log`> 
log.-(1 (log.-1 o>`log`> desIdenObRKV) o>`log`> desIdenObRK & Vb )0) 
o>`log`> log.-(1 (log.-1 o>`log`> ((log.-1 o>`log`> 
log.-(1 log.-1 o>`log`> desIdenObRK & log.-(0 trfV1 & log.-I )0 )0) 
o>`log`> log.-(1 log.-1 & log.-(0 trfV1 & log.-I )0 )0) 
o>`log`> log.-(1 log.-1 & log.-(0 trfV1 & log.-I )0 )0 
o>`log`> desIdenObLK) o>`log`> log.-1 o>`log`> desIdenObRK & Vb )0 .

  Admitted.
  Hint Resolve logic_decidable7 : logic_hints.

(**#+END_SRC

Some more deduced conversion relations over the morphisms, this time the
orientation-of-the-most-general is reversed

#+BEGIN_SRC coq :exports both :results silent **)

  Lemma Mod_inputUnitMod_rev {log : logic} :
    forall (V : obV log) (B : obMod) (A : obMod) (b : 'Mod(0 V |- [0 B ~> A ]0 )0),
      ( b )
        ~~~  ( desIdenObLKV o>| b o>Mod ( log.-1 o>| uMod ) ).
  Proof. eauto with logic_hints. (* intros. rewrite -Mod_inputUnitMod. rewrite [LHSc]PolyV_Mod_unit.
               eapply PolyV_Mod_cong; [| reflexivity].
               clear. exact: logic_decidable0. *) Qed.  
  
  Lemma DeClassifying_morphismPost_rev {log : logic} :
    forall (V : obV log) (A1 A2 : obMod) (b_ : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
      (W _WV : obV log)  (A3 : obMod) (b' : 'D(0 W |- [0 A2 ~> A3 ]0 )0),
    forall (WV : obV log) (w : V(0 WV |- (0 W & V )0 )0) (w0 : V(0 _WV |- WV )0),
      ( w0 o>| ( w  o>| b_ o>Mod b' ) o>Mod 'declfy )
        ~~~ ( (w0 o> w) o>| b_ o>Mod ( log.-1 o>| b' o>Mod 'declfy ) ).
  Proof. 
    intros. rewrite -[in RHSc]DeClassifying_morphismPost. rewrite [in LHSc]Mod_arrowLog_id. rewrite -[in LHSc]DeClassifying_arrow.
    rewrite [in RHSc]Mod_arrowLog_id. rewrite -[in RHSc]DeClassifying_arrow. eauto with logic_hints.
  Qed.
  
  Lemma DeClass_morphismPre_rev {log : logic} :
    forall (A : obMod) (V : obV log) (B : obMod) (b' : 'D(0 V |- [0 B ~> A ]0 )0),
    forall (W : obV log)  (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
    forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V )0 )0),
      ( v0  o>| b' o>D ( a ) )
        ~~~ ( (v0 o> ((1 desIdenObRKV & _  )0))  o>| b' o>Mod ( log.-1 o>| 'D1| a )
              : 'D(0 WV' |- [0 B ~> A' ]0)0 ).
  Proof.
    intros. rewrite -[in RHSc]DeClass_morphismPre.
    rewrite -DeClass_arrowPost. eauto with logic_hints.
  Qed.
  
  Lemma DeClass_morphismPost_rev {log : logic}:
    forall (A : obMod)
      (W' W_ W'W_ : obV log) (v : V(0 W'W_ |- (0 W' & W_ )0 )0) (A' : obMod) (a_ : 'Mod(0 W_ |- [0 A ~> A' ]0 )0)
      (A'' : obMod) (a' : 'Mod(0 W' |- [0 A' ~> A'' ]0 )0),
    forall (W'W_I : obV log) (v0 : V(0 W'W_I |- (0 W'W_ & log.-I )0 )0),
      ( v0 o>| 'D1| ( v o>| a_ o>Mod a' ) )
        ~~~ ( (v0 o> (1 v & _ )0 o> Assoc_Rev) o>| ( (log.-1) o>| 'D1| a_ ) o>D a'
              : 'D(0 W'W_I |- [0 'D0| A ~> A'' ]0)0 ).
  Proof.
    intros. rewrite -[in RHSc]DeClass_morphismPost.
    rewrite -[in RHSc]Mod_arrowPre.   rewrite [in RHSc]Mod_arrowLog_id. rewrite -[in RHSc]UnitDeClass_arrow. rewrite [in LHSc]Mod_arrowLog_id. rewrite -[in LHSc]UnitDeClass_arrow.
    eauto with logic_hints.
  Qed.

  Lemma Mod_morphism_rev :
    forall {log : logic} (V : obV log) (B : obMod) (A : obMod) (b : 'Mod(0 V |- [0 B ~> A ]0 )0)
      (W_ : obV log) (A' : obMod) (a_ : 'Mod(0 W_ |- [0 A ~> A' ]0 )0)
      (W' : obV log) (A'' : obMod) (a' : 'Mod(0 W' |- [0 A' ~> A'' ]0 )0),
    forall (W'W_ : obV log) (v : V(0 W'W_ |- (0 W' & W_ )0 )0),
    forall (W'W_V : obV log) (v0 : V(0 W'W_V |- (0 W'W_ & V )0 )0),
      ( v0 o>| b o>Mod ( v o>| a_ o>Mod a' ) )
        ~~~ ( (v0 o> (1 v & _ )0 o> Assoc_Rev) o>| ( (log.-1) o>| b o>Mod a_ ) o>Mod a' ).
  Proof.
    intros. rewrite -Mod_morphism.
    rewrite [X in _ o>| _ o>Mod X ~~~ _]Mod_arrowLog_id.
    rewrite -[in LHSc]Mod_arrowPost. eauto with logic_hints.
  Qed.

(**#+END_SRC

Finally the deduced corresponding conversion relations for the iterated constructors :

#+BEGIN_SRC coq :exports both :results silent **)

  Module Import Iter_deduce.

    Module Import Ex_Notations.

    Delimit Scope short_scope with short.
    Open Scope short_scope.

    Notation "$ o>' a" := (_ o>' a) (at level 25) : short_scope.
    Notation "$ o>| #1| a" := (_ o>| #1| a) (at level 25) : short_scope.
    Notation "$ o>| 'uMod'" := (_ o>| uMod)(at level 25) : short_scope.
    Notation "$ o>| a_ o>Mod a'" := (_ o>| a_ o>Mod a') (at level 25) : short_scope.
    Notation "$ o>| ''D1|' a" := (_ o>| 'D1| a) (at level 25) : short_scope.
    Notation "$ o>| b o>D a" := (_ o>| b o>D a) (at level 25) : short_scope.
    Notation "$ o>| 'clfy o>Mod a'" := (_ o>| 'clfy o>Mod a') (at level 25) : short_scope.
    Notation "$ o>| a_ o>Mod 'declfy" := (_ o>| a_ o>Mod 'declfy) (at level 25) : short_scope.

    End Ex_Notations.
    
  Lemma iterCancelInner {log : logic} {trf : obV log -> obV log} :
        forall (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
        (Vb Vb' : obV log) (vb : V(0 Vb' |- Vb )0)
        (W W_dft : obV log) (V0Vb' : obV log)
        (va : V(0 trf(last W_dft Vs) |- W )0)
        (v0b : V(0 V0Vb' |- (0 trf(head W_dft Vs) & Vb' )0 )0)
        (B : obMod) (A : obMod) (b : 'D(0 Vb |- [0 B ~> A ]0 )0)
        (A' : obMod)(a : 'D(0 W |- [0 A ~> A' ]0 )0),
    ( v0b o>| ( vb o>' b)  o>D (iterDeClassifying (V_dft := W_dft) vs ( va o>' a)) )
      ~~~ ( v0b o>| (vb o>| b o>Mod 'declfy )
                o>D (iterDeClassifying (V_dft := W_dft) vs (va o>| 'clfy o>Mod a) )
            : 'D(0 V0Vb' |- [0 B ~> 'D0| (iterDeClass0 (length Vs).-1 A') ]0)0 ).
  Proof.
    move => Vs; elim : Vs => [ | V0 Vs' ].
    - move => vs. case:  vs / (arrowList_destructP vs); intros.
      do 2 rewrite (iterDeClassifying_rewrite (HNil : arrowList [::])).
        apply: CancelInner.
    - case: Vs' => [ | V1 Vs''] IHVs'.
      + move => vs. case:  V0 vs / (arrowList_destructP vs); intros.
        do 2 rewrite (iterDeClassifying_rewrite (HNil : arrowList [:: V0])).
        apply: CancelInner.
      + move => vs; move : IHVs'. case:  V0 V1 Vs'' vs / (arrowList_destructP vs).
        move => V0 V1 Vs'' v01 vs' IHVs' Vb Vb' vb W W_dft V0Vb' va v0b B A b A' a.
        do 2 rewrite (iterDeClassifying_rewrite (v01 ::: vs' : arrowList [:: V0 , V1 & Vs''])) /=.

        rewrite [(_ o>|| _ o>Mod ''declfy) in RHSc]
                Mod_inputUnitMod_rev.

        rewrite [_ o>| _ o>Mod 'declfy as X in _ ~~~ (_ o>| _ o>D X )]
                (DeClassifying_morphismPost_rev (log:=log)).
        rewrite [in RHSc]DeClass_morphismPre_rev.
        rewrite [in RHSc]DeClass_morphismPost_rev.
        rewrite [in RHSc]DeClass_morphismPre_rev.
        rewrite [in RHSc]Mod_morphism_rev.

        rewrite -[X in _ ~~~ (_ o>| X o>Mod _)]DeClass_morphismPre.
        rewrite -[in RHSc]DeClass_arrowPost.
        rewrite -[in RHSc]IHVs'.

        rewrite [in RHSc]DeClass_morphismPre_rev.
        rewrite -[in RHSc]Mod_morphism.
        rewrite -[in RHSc]DeClass_morphismPre.
        rewrite -[in RHSc]DeClass_morphismPost.
        rewrite -[in RHSc]Mod_arrowPost.
        rewrite -[in RHSc]DeClassifying_morphismPost.
        rewrite -[in RHSc]Mod_inputUnitMod.
        rewrite -[in RHSc]DeClass_morphismPre.

        rewrite -!tac_arrows.
        rewrite [in RHSc]DeClassifying_arrowLog_id -[in RHSc]DeClass_arrowPost.
        rewrite [in LHSc]DeClassifying_arrowLog_id -[in LHSc]DeClass_arrowPost.
        apply: PolyDeClass_cong; [ | reflexivity | reflexivity].

        clear. simpl in *. clear. revert dependent trf. rewrite /toArrowV. simpl.
        move => trf. move: (trf V0) (trf V1) => trfV0 trfV1. intros; clear.
        exact: logic_decidable7.
  Qed.
  Hint Resolve iterCancelInner.
  
  Lemma iterPermOuterInner_DeClass {log : logic}{trf : obV log -> obV log}
        (Wb Wa : obV log) (Vs : list (obV log)) (W_dft: obV log) (Wba : obV log)
        (Wb' : obV log) (wb : V(0 Wb' |- Wb )0)
        (trf':=fun z => (0 (trf z) & Wb' )0)
        (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
        (wa : V(0 trf(last W_dft Vs) |- (0 Wa & log.-I )0 )0)
        (wba : V(0 Wba |- (0 trf(head W_dft Vs) & Wb' )0 )0)
        (B : obMod) (A : obMod) (b : 'D(0 Wb |- [0 B ~> A ]0 )0)
        (A' : obMod) (a : 'Mod(0 Wa |- [0 A ~> A' ]0 )0) :
    ( wba o>| (iterDeClassifying (V_dft:=W_dft)
                                 (hmap (B2:=toArrowV (trf:=trf')) (fun U1U2 u => ((1 u & Wb')0)) vs)
                                 ( ( (1 wa o> desIdenObRK & _ )0 o> (0 _ & wb)1 ) o>| b o>D a ))
          o>Mod 'declfy )
      ~~~ ( wba o>| ( wb o>| b o>Mod 'declfy )
                o>D (iterDeClassifying (V_dft:=W_dft) vs ( wa o>| 'D1| a ))
            : 'D(0 Wba |- [0 B ~> 'D0| (iterDeClass0 (length Vs).-1 A') ]0)0 ) .
  Admitted. (* same deduction form *)
  Hint Resolve iterPermOuterInner_DeClass.
  
  Lemma iterPermOuterInner {log : logic}{trf : obV log -> obV log}
        (Wb : obV log) (Vs : list (obV log)) (W_dft: obV log) (Wba : obV log)
        (Wb' : obV log) (wb : V(0 Wb' |- Wb )0)
        (trf':=fun z => (0 (trf z) & Wb' )0)
        (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
        (wa : V(0 trf(last W_dft Vs) |- log.-I )0)
        (wba : V(0 Wba |- (0 trf(head W_dft Vs) & Wb' )0 )0)
        (B : obMod) (A : obMod) (b : 'D(0 Wb |- [0 B ~> A ]0 )0) :
    ( wba o>| (iterDeClassifying (V_dft:=W_dft)
                                 (hmap (B2:=toArrowV (trf:=trf')) (fun U1U2 u => ((1 u & Wb')0)) vs)
                                 ( ( (1 wa  & _ )0 o> (0 _ & wb)1 o> desIdenObLK ) o>' b ))
          o>Mod 'declfy )
      ~~~ ( wba o>| ( wb o>| b o>Mod 'declfy )
                o>D (iterDeClassifying (V_dft:=W_dft) vs ( wa o>| uMod ))
            : 'D(0 Wba |- [0 B ~> 'D0| (iterDeClass0 (length Vs).-1 A) ]0)0 ) .
  Admitted. (* same deduction form *)
  Hint Resolve iterPermOuterInner.

(**#+END_SRC

** COMMENT Old example attempt

#+BEGIN_SRC coq :exports both :results silent **)

  (* ============
     here are the old complete-deductions when only the logical arrows which
     are identity are enabled

  Definition iterDeClassifying {log : logic} (V : obV log) (B A : obMod)
             (b : 'D(0 V |- [0 B ~> A ]0 )0)
    : forall n : nat, 'D(0 V |- [0 B ~> iterDeClass0 n A ]0 )0 :=
    fix iterDeClassifying n :=
      match n return 'D(0 V |- [0 B ~> iterDeClass0 n A ]0 )0 with
      | O => b
      | S n => (iterDeClassifying n) o>Mod 'declfy
      end .

  Notation RHSc := (X in _ ~~~ X)%pattern.
  Notation LHSc := (X in X ~~~ _)%pattern.

  Lemma iterCancelInner {log : logic} (V : obV log) (B : obMod) (A : obMod)
        (b : 'D(0 V |- [0 B ~> A ]0 )0) (A' : obMod)
        (W : obV log) (a : 'D(0 W |- [0 A ~> A' ]0 )0) : forall n : nat,
      (b o>D (iterDeClassifying a n))
        ~~~ ((b o>Mod 'declfy) o>D (iterDeClassifying ('clfy o>Mod a) n)) .
  Proof.
    elim => [ | n IHn /= ]; first by apply: CancelInner.

    rewrite [iterDeClassifying _ _ in RHSc]PolyV_Mod_unit.
    rewrite [in RHSc]desIdenObLKV_K.
    rewrite [in RHSc]PolyV_Mod_arrow.
    rewrite [in RHSc]Mod_inputUnitMod.
    rewrite -[in RHSc]DeClassifying_arrow.
    rewrite -[in RHSc]DeClass_arrowPost.
    rewrite [in RHSc]DeClassifying_morphismPost.
    rewrite [_ o>D _ in RHSc]PolyV_Mod_unit.
    rewrite [in RHSc]Assoc_Rev_Assoc.
    rewrite -[(Assoc <`log`<o Assoc_Rev) in RHSc]polyV_relT_constant_rel_identitary.
    rewrite [in RHSc]PolyV_Mod_arrow.
    rewrite [in RHSc]DeClass_morphismPost.
    rewrite -[in RHSc]IHn.
    rewrite -[in RHSc]DeClass_morphismPost.
    rewrite -[in RHSc]DeClassifying_morphismPost.
    rewrite -[Assoc_Rev o>' Assoc o>' _ in RHSc]PolyV_Mod_arrow.
    rewrite [Assoc_Rev o>`log`> Assoc in RHSc](@polyV_relT_constant_rel_identitary log).
    rewrite -[Assoc <`log`<o Assoc_Rev in RHSc](@Assoc_Rev_Assoc log log).
    rewrite -[in RHSc]PolyV_Mod_unit.

    rewrite [iterDeClassifying _ _ in LHSc]PolyV_Mod_unit.
    rewrite [in LHSc]desIdenObLKV_K.
    rewrite [in LHSc]PolyV_Mod_arrow.
    rewrite [_ o>' iterDeClassifying _ _ in LHSc]Mod_inputUnitMod.
    rewrite -[in LHSc]DeClassifying_arrow.
    rewrite -[in LHSc]DeClass_arrowPost.

    reflexivity.
  Qed.
  
  Print iterCancelInner. (* 374 lines *)

  Lemma iterCancelInner_altdeduce {log : logic} (V : obV log) (B : obMod) (A : obMod)
        (b : 'D(0 V |- [0 B ~> A ]0 )0) (A' : obMod)
        (W : obV log) (a : 'D(0 W |- [0 A ~> A' ]0 )0) : forall n : nat,
      (b o>D (iterDeClassifying a n))
        ~~~ ((b o>Mod 'declfy) o>D (iterDeClassifying ('clfy o>Mod a) n)) .
  Proof.
    elim => [ | n IHn /= ]; first by apply: CancelInner.

    eapply Mod_TransV; [ eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                         eapply DeClassifying_cong;
                         eapply Mod_SymV, PolyV_Mod_unit | ].

    eapply Mod_TransV; [ eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                         eapply DeClassifying_cong;
                         eapply PolyV_Mod_cong; [|eapply Mod_ReflV];
                         eapply SymV, desIdenObLKV_K | ].
    
    eapply Mod_TransV; [ eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                         eapply DeClassifying_cong;
                         eapply Mod_SymV, PolyV_Mod_arrow | ].

    eapply Mod_TransV; [ eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                         eapply DeClassifying_cong;
                         eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply Mod_SymV, Mod_inputUnitMod | ].

    eapply Mod_TransV; [ eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                         eapply DeClassifying_arrow | ] .

    eapply Mod_TransV; [ eapply DeClass_arrowPost | ] .

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                         eapply Mod_SymV, DeClassifying_morphismPost | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply Mod_SymV, PolyV_Mod_unit | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyV_Mod_cong; [|eapply Mod_ReflV];
                         eapply SymV, Assoc_Rev_Assoc | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyV_Mod_cong; [|eapply Mod_ReflV];
                         eapply polyV_relT_constant_rel_identitary | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply Mod_SymV, PolyV_Mod_arrow | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply Mod_SymV, DeClass_morphismPost | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyDeClass_cong; [|eapply Mod_ReflV];
                         eapply IHn | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply  DeClass_morphismPost | ].

    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyV_Mod_cong; [eapply ReflV|];
                         eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                         eapply DeClassifying_morphismPost | ].

    eapply Mod_TransV; [ | eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                           eapply DeClassifying_cong;
                           eapply PolyV_Mod_unit ].

    eapply Mod_TransV; [ | eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                           eapply DeClassifying_cong;
                           eapply PolyV_Mod_cong; [|eapply Mod_ReflV];
                           eapply desIdenObLKV_K ].

    eapply Mod_TransV; [ | eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                           eapply DeClassifying_cong;
                           eapply PolyV_Mod_arrow ].

    eapply Mod_TransV; [ | eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                           eapply DeClassifying_cong;
                           eapply PolyV_Mod_cong; [eapply ReflV|];
                           eapply Mod_inputUnitMod ].

    eapply Mod_TransV; [ | eapply PolyDeClass_cong; [eapply Mod_ReflV|];
                           eapply Mod_SymV, DeClassifying_arrow ].

    eapply Mod_TransV; [ | eapply Mod_SymV, DeClass_arrowPost ].

    eapply PolyV_Mod_cong; [eapply ReflV|].
    eapply Mod_TransV; [ eapply PolyV_Mod_arrow | ].
    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [|eapply Mod_ReflV];
                         eapply SymV, polyV_relT_constant_rel_identitary | ].
    eapply Mod_TransV; [ eapply PolyV_Mod_cong; [|eapply Mod_ReflV];
                         eapply Assoc_Rev_Assoc | ].
    eapply PolyV_Mod_unit.
  Qed.

  Print iterCancelInner_altdeduce.  (* 162 lines *)

  Lemma iterPermOuterInner_DeClass {log : logic}
        (V : obV log) (B : obMod) (A : obMod)
        (b : 'D(0 V |- [0 B ~> A ]0 )0) (A' : obMod)
        (a_ : 'D(0 V |- [0 'D0| A ~> A' ]0 )0) (A'' : obMod)
        (a' : 'Mod(0 V |- [0 A' ~> A'' ]0 )0) : forall n : nat,
        ( ( iterDeClassifying ( b o>Mod ( a_ o>D a' ) ) n ) o>Mod 'declfy )
          ~~~ ( ( b o>Mod 'declfy ) o>D (iterDeClassifying ( a_ o>D a' ) n)
                : 'D(0 (0 (0 V & V )0 & V )0 |- [0 B ~> 'D0| (iterDeClass0 n A'') ]0)0 ).
  Proof.
    elim => [ | n IHn /= ]; first by apply: DeClassifying_morphismPre.

    rewrite [iterDeClassifying _ _ in RHSc]PolyV_Mod_unit.
    rewrite [in RHSc]desIdenObLKV_K.
    rewrite [in RHSc]PolyV_Mod_arrow.
    rewrite [in RHSc]Mod_inputUnitMod.
    rewrite -[in RHSc]DeClassifying_arrow.
    rewrite -[in RHSc]DeClass_arrowPost.
    rewrite [in RHSc]DeClassifying_morphismPost.
    rewrite [_ o>D _ in RHSc]PolyV_Mod_unit.
    rewrite [in RHSc]Assoc_Rev_Assoc.
    rewrite -[(Assoc <`log`<o Assoc_Rev) in RHSc]polyV_relT_constant_rel_identitary.
    rewrite [in RHSc]PolyV_Mod_arrow.
    rewrite [in RHSc]DeClass_morphismPost.
    rewrite -[in RHSc]IHn.
    rewrite -[in RHSc]PermOuterInner.
    rewrite -2![in RHSc]PolyV_Mod_arrow.
    rewrite -[X in _ ~~~ (X o>' _) ]desIdenObLKV_Assoc_Rev_desIdenObLK.
    rewrite -[in RHSc]PolyV_Mod_unit; reflexivity.
  Qed.

  Lemma iterPermOuterInner {log : logic}
        (V : obV log) (B : obMod) (A : obMod)
        (b : 'D(0 V |- [0 B ~> A ]0 )0) : forall n : nat,
        ( desIdenObLK o>' ( (iterDeClassifying b n) o>Mod 'declfy ) )
          ~~~ ( ( b o>Mod 'declfy ) o>D (iterDeClassifying uMod n)
                : 'D(0 (0 log.-I & V )0 |- [0 B ~> 'D0| (iterDeClass0 n A) ]0)0 ).
  Proof.
    elim => [ /= | n IHn /= ]; first by rewrite -DeClass_inputUnitMod; reflexivity.

    rewrite [iterDeClassifying _ _ in RHSc]PolyV_Mod_unit.
    rewrite [in RHSc]desIdenObLKV_K.
    rewrite [in RHSc]PolyV_Mod_arrow.
    rewrite [in RHSc]Mod_inputUnitMod.
    rewrite -[in RHSc]DeClassifying_arrow.
    rewrite -[in RHSc]DeClass_arrowPost.
    rewrite [in RHSc]DeClassifying_morphismPost.
    rewrite [_ o>D _ in RHSc]PolyV_Mod_unit.
    rewrite [in RHSc]Assoc_Rev_Assoc.
    rewrite -[(Assoc <`log`<o Assoc_Rev) in RHSc]polyV_relT_constant_rel_identitary.
    rewrite [in RHSc]PolyV_Mod_arrow.
    rewrite [in RHSc]DeClass_morphismPost.
    rewrite -[in RHSc]IHn.
    rewrite -[in RHSc]DeClass_arrowPre.
    rewrite -2![in RHSc]PolyV_Mod_arrow.
    rewrite -[X in _ ~~~ (X o>' _) ]desIdenObLKV_IdenOb_Assoc_Rev_desIdenObLK.
    rewrite -[in RHSc]PolyV_Mod_unit.
    rewrite -[in RHSc]PermOuterInner; reflexivity.
  Qed.

   =========== *)

  End Iter_deduce.

(**#+END_SRC

* Grade

Definitions ...

#+BEGIN_SRC coq :exports both :results silent **)
  
  Definition grade {log : logic} :
    forall (V : obV log) (A1 A2 : obMod), 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> nat.
  Proof.
    move => V A1 A2 a; elim : V A1 A2 / a.
    - intros; refine (S _); assumption (* intros; assumption *) . (* PolyV_Mod *)
    - intros; exact (S O). (* GenArrowsMod *)
    - intros; exact (S (S O)). (* UnitMod *)
    - move => ? ? ? a_ grade_a_ ? ? ? ? a' grade_a';
               refine (S  (S (grade_a_ + grade_a')%coq_nat)). (* PolyMod *)
    - intros; refine (S  (S (S (S _)))); assumption. (* UnitDeClass *)
    - move => ? ? ? b grade_b ? ? ? ? a grade_a;
               refine (S  (S (S (grade_b + grade_a)%coq_nat))). (* PolyDeClass *)
    - intros; refine ( (S  (S _))); assumption. (* Classifying *)
    - intros; refine ( (S  (S _))); assumption. (* DeClassifying *)
  Defined.

  Definition gradeCom {log : logic} :
    forall (V : obV log) (A1 A2 : obMod), 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> nat.
  Proof.
    move => V A1 A2 a; elim : V A1 A2 / a.
    - intros; assumption. (* PolyV_Mod *)
    - intros; exact (O). (* GenArrowsMod *)
    - intros; exact (O). (* UnitMod *)
    - move => ? ? ? a_ gradeCom_a_ ? ? ? v a' gradeCom_a';
               refine (gradeCom_a_ + (gradeCom_a' + (grade ( v o>| a_ o>Mod a')))%coq_nat)%coq_nat.
    (* PolyMod *)
    - intros; assumption. (* UnitDeClass *)
    - move => ? ? ? b gradeCom_b ? ? ? v a gradeCom_a;
               refine (gradeCom_b + (gradeCom_a )%coq_nat)%coq_nat.
    (* PolyDeClass *)
    - intros; assumption. (* Classifying *)
    - intros; assumption. (* DeClassifying *)
  Defined.

  Definition gradeDeClass {log : logic} :
    forall (V : obV log) (A1 A2 : obMod), 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> nat.
  Proof.
    move => V A1 A2 a; elim : V A1 A2 / a.
    - intros; assumption. (* PolyV_Mod *)
    - intros; exact (O). (* GenArrowsMod *)
    - intros; exact (O). (* UnitMod *)
    - move => ? ? ? a_ gradeDeClass_a_ ? ? ? v a' gradeDeClass_a';
               refine (gradeDeClass_a_ + (gradeDeClass_a')%coq_nat)%coq_nat.
    (* PolyMod *)
    - intros; assumption. (* UnitDeClass *)
    - move => ? ? ? b gradeDeClass_b ? ? ? v a gradeDeClass_a;
               refine (gradeDeClass_b + (gradeDeClass_a + (grade (v o>| b o>D a)))%coq_nat)%coq_nat.
    (* PolyDeClass *)
    - intros; assumption. (* Classifying *)
    - intros; assumption. (* DeClassifying *)
  Defined.

  Definition gradeTotal {log : logic} (V : obV log) (A1 A2 : obMod) :
    'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> nat.
  Proof.
    move => a; refine ( (grade a) + ( (gradeCom a) + (gradeDeClass a) )%coq_nat )%coq_nat.
  Defined.

(**#+END_SRC

Some lemmas :

#+BEGIN_SRC coq :exports both :results silent **)

  Lemma grade_iterDeClassifying {log : logic} {trf : obV log -> obV log}
        (V_dft : obV log) (B A : obMod) 
        (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs))) :
    forall (b : 'D(0 trf (last V_dft Vs) |- [0 B ~> A ]0 )0),
    grade (iterDeClassifying vs b) = ((2 * (length (chain Vs)))%coq_nat + grade b)%coq_nat.
  Proof.
    move: (arrowListP (trf:=trf) vs) => vs_arrowListP.
    elim : vs_arrowListP.
    - reflexivity.
    - reflexivity.
    - move => V0 V1 v01 Vs'' vs' vs'_arrowListP IHvs' b.
      rewrite (iterDeClassifying_rewrite (v01 ::: vs' : arrowList [:: V0, V1 & Vs''])) /= ||
              rewrite /= -/(iterDeClassifying vs' b) .
      rewrite IHvs' /=; Omega.omega.
  Qed.
  Hint Rewrite (@grade_iterDeClassifying).

  Lemma gradeCom_iterDeClassifying {log : logic} {trf : obV log -> obV log}
        (V_dft : obV log) (B A : obMod) 
        (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs))) :
    forall (b : 'D(0 trf (last V_dft Vs) |- [0 B ~> A ]0 )0),
    gradeCom (iterDeClassifying vs b) = (gradeCom b).
  Proof.
    move: (arrowListP (trf:=trf) vs) => vs_arrowListP.
    elim : vs_arrowListP.
    - reflexivity.
    - reflexivity.
    - move => V0 V1 v01 Vs'' vs' vs'_arrowListP IHvs' b.
      rewrite (iterDeClassifying_rewrite (v01 ::: vs' : arrowList [:: V0, V1 & Vs''])) /= ||
              rewrite /= -/(iterDeClassifying vs' b) .
      rewrite IHvs' /=; reflexivity.
  Qed.
  Hint Rewrite (@gradeCom_iterDeClassifying).

  Lemma gradeDeClass_iterDeClassifying {log : logic} {trf : obV log -> obV log}
        (V_dft : obV log) (B A : obMod) 
        (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs))) :
    forall (b : 'D(0 trf (last V_dft Vs) |- [0 B ~> A ]0 )0),
    gradeDeClass (iterDeClassifying vs b) = (gradeDeClass b).
  Proof.
    move: (arrowListP (trf:=trf) vs) => vs_arrowListP.
    elim : vs_arrowListP.
    - reflexivity.
    - reflexivity.
    - move => V0 V1 v01 Vs'' vs' vs'_arrowListP IHvs' b.
      rewrite (iterDeClassifying_rewrite (v01 ::: vs' : arrowList [:: V0, V1 & Vs''])) /= ||
              rewrite /= -/(iterDeClassifying vs' b) .
      rewrite IHvs' /=; reflexivity.
  Qed.
  Hint Rewrite (@gradeDeClass_iterDeClassifying).

(**#+END_SRC

* Reduction

** Grammatical generation of the reduction relation

Generating the reduction relations, memo that the conversion relation =Mod_morphism=
for associativity, is not contained in the reduction relations :

#+BEGIN_SRC coq :exports both :results silent **)

  Module Red.
    
    Reserved Notation "f2 <~~ f1" (at level 70).

    Inductive convMod {log : logic} : forall (V : obV log) (A1 A2 : obMod),
        'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> Prop :=

    | Mod_TransV : forall (V : obV log) (A1 A2 : obMod)
                     (uTrans a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        uTrans <~~ a -> forall (a0 : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
          a0 <~~ uTrans -> a0 <~~ a

    | PolyV_Mod_cong : forall (A1 A2 : obMod) (V V' : obV log) (v v0 : V(0 V' |- V )0)
                         (a a0 : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        v0 ~~ v -> a0 <~~ a -> ( v0 o>' a0 ) <~~ ( v o>' a )

    | Mod_cong_Pre :
        forall (V : obV log) (A A' : obMod) (a_ a_0 : 'Mod(0 V |- [0 A ~> A' ]0 )0),
        forall (W : obV log) (A'' : obMod) (a' : 'Mod(0 W |- [0 A' ~> A'' ]0 )0),
        forall (WV : obV log) (v v0 : V(0 WV |- (0 W & V )0 )0),
          v0 ~~ v -> a_0 <~~ a_ -> ( v0 o>| a_0 o>Mod a' ) <~~ ( v o>| a_ o>Mod a' )

    | Mod_cong_Post :
        forall (V : obV log) (A A' : obMod) (a_ : 'Mod(0 V |- [0 A ~> A' ]0 )0),
        forall (W : obV log) (A'' : obMod) (a' a'0 : 'Mod(0 W |- [0 A' ~> A'' ]0 )0),
        forall (WV : obV log) (v v0 : V(0 WV |- (0 W & V )0 )0),
          v0 ~~ v -> a'0 <~~ a' -> ( v0 o>| a_ o>Mod a'0 ) <~~ ( v o>| a_ o>Mod a' )

    | UnitDeClass_cong :
        forall (A : obMod) (A' : obMod) (W W' : obV log) (v v0 : V(0 W' |- (0 W & log.-I )0 )0) (a a0 : 'Mod(0 W |- [0 A ~> A' ]0 )0),
          v0 ~~ v -> a0 <~~ a -> ( v0 o>| 'D1| a0 ) <~~ ( v o>| 'D1| a )

    | PolyDeClass_cong_Pre :
        forall (V : obV log) (B : obMod) (A : obMod) (b b0 : 'D(0 V |- [0 B ~> A ]0 )0),
        forall (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v v0 : V(0 WV |- (0 W & V )0 )0),
          v0 ~~ v -> b0 <~~ b -> ( v0 o>| b0 o>D a ) <~~ ( v o>| b o>D a )

    | PolyDeClass_cong_Post :
        forall (V : obV log) (B : obMod) (A : obMod) (b : 'D(0 V |- [0 B ~> A ]0 )0),
        forall (W : obV log) (A' : obMod) (a a0 : 'Mod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v v0 : V(0 WV |- (0 W & V )0 )0),
          v0 ~~ v -> a0 <~~ a -> ( v0 o>| b o>D a0 ) <~~ ( v o>| b o>D a )

    | Classifying_cong :
      forall (V V' : obV log) (v v0 : V(0 V' |- V )0) (A1 A2 : obMod) (a a0 : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        v0 ~~ v -> a0 <~~ a -> (v0 o>| 'clfy o>Mod a0 ) <~~ (v o>| 'clfy o>Mod a )

    | DeClassifying_cong :
      forall (V V' : obV log) (v v0 : V(0 V' |- V )0) (A1 A2 : obMod) (a a0 : 'D(0 V |- [0 A1 ~> A2 ]0 )0),
        v0 ~~ v -> a0 <~~ a -> (v0 o>| a0 o>Mod 'declfy ) <~~ (v o>| a o>Mod 'declfy )

    | GenArrowsMod_arrowLog : forall (V V' V'' : obV log) (A1 A2 : obMod_gen)
                                (aGen : Mod_gen V A1 A2) (v : V(0 V' |- V )0)
                                (v' : V(0 V'' |- V' )0) ,
        ( ( v' o> v) o>| #1| aGen )
          <~~ (v' o>' (v o>| #1| aGen)
               : 'Mod(0 V'' |- [0 #0| A1 ~> #0| A2 ]0)0 )

    | UnitMod_arrowLog : forall (V V' : obV log) (A : obMod) (v : V(0 V |- log.-I )0)
                        (v' : V(0 V' |- V )0),
        ( ( v' o> v ) o>| @uMod A )
          <~~ (v' o>' (v o>| @uMod A)
               : 'Mod(0 V' |- [0 A ~> A ]0)0 )

    | Mod_arrowLog :
        forall (V : obV log) (A0 : obMod) (A : obMod)
          (a_ : 'Mod(0 V |- [0 A0 ~> A ]0 )0),
        forall (W : obV log) (A' : obMod) (a' : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
        forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
          ( ( v0 o> v ) o>| a_ o>Mod a' )
            <~~ ( v0 o>' ( v o>| a_ o>Mod a' )
                  : 'Mod(0 WV0 |- [0 A0 ~> A' ]0)0 )

    | Mod_arrowPre :
        forall (V V' : obV log) (v : V(0 V' |- V )0) (A0 : obMod) (A : obMod)
          (a_ : 'Mod(0 V |- [0 A0 ~> A ]0 )0),
        forall (W : obV log) (A' : obMod) (a' : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
          ( ( v0 o> log.-(0 _ & v )1 ) o>| a_ o>Mod a' )
            <~~ ( v0 o>| ( v o>' a_ ) o>Mod a'
                  : 'Mod(0 WV' |- [0 A0 ~> A' ]0)0 )

    | Mod_arrowPost :
        forall (V : obV log) (A0 : obMod) (A : obMod) (a_ : 'Mod(0 V |- [0 A0 ~> A ]0 )0),
        forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obMod)
          (a' : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
          ( ( w0 o> log.-(1 w & _ )0 ) o>| a_ o>Mod a' )
            <~~ ( w0 o>| a_ o>Mod ( w o>' a' )
                  : 'Mod(0 W'V |- [0 A0 ~> A' ]0)0 )

    | UnitDeClass_arrowLog :
        forall (W W' W'' : obV log) (w : V(0 W' |- (0 W & log.-I )0 )0)
          (w' : V(0 W'' |- W' )0)
          (A A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
          ( ( w' o> w ) o>| 'D1| a )
            <~~ (  w' o>' ( w o>| 'D1| a )
                   : 'D(0 W'' |- [0 'D0| A ~> A' ]0)0 )

    | UnitDeClass_arrow :
        forall (W W' W'' : obV log) (w : V(0 W' |- W )0)
          (w' : V(0 W'' |- (0 W' & log.-I )0 )0)
          (A A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
          ( ( w' o> log.-(1 w & log.-I )0 ) o>| 'D1| a )
            <~~ (  w' o>| 'D1| ( w o>' a)
                               : 'D(0 W'' |- [0 'D0| A ~> A' ]0)0 )

    | DeClass_arrowLog :
        forall (V : obV log) (B : obMod) (A : obMod)
          (b : 'D(0 V |- [0 B ~> A ]0 )0),
        forall (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
        forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
          ( ( v0 o> v ) o>| b o>D a )
            <~~ ( v0 o>' ( v o>| b o>D a )
                : 'D(0 WV0 |- [0 B ~> A' ]0)0 )

    | DeClass_arrowPre :
        forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
          (b : 'D(0 V |- [0 B ~> A ]0 )0),
        forall (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
          ( ( v0 o> log.-(0 _ & v )1 ) o>| b o>D a )
            <~~ ( v0 o>| ( v o>' b ) o>D a
                : 'D(0 WV' |- [0 B ~> A' ]0)0 )

    | DeClass_arrowPost :
        forall (V : obV log) (B : obMod) (A : obMod) (b : 'D(0 V |- [0 B ~> A ]0 )0),
        forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obMod)
          (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
          ( ( w0 o> log.-(1 w & _ )0 ) o>| b o>D a )
            <~~ ( w0 o>| b o>D ( w o>' a )
                  : 'D(0 W'V |- [0 B ~> A' ]0)0 )

    | Classifying_arrowLog : forall (V V' V'' : obV log) (v : V(0 V' |- V )0) (v0 : V(0 V'' |- V' )0)
                               (A1 A2 : obMod)
                               (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v0 o> v ) o>| 'clfy o>Mod a )
          <~~ ( v0 o>' ( v o>| 'clfy o>Mod a ) 
                : 'Mod(0 V'' |- [0 'D0| A1 ~> A2 ]0)0 )

    | Classifying_arrow : forall (V V' V'' : obV log) (v : V(0 V' |- V )0)
                            (v0 : V(0 V'' |- V' )0) (A1 A2 : obMod)
                            (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v0 o> v ) o>| 'clfy o>Mod a )
          <~~ ( v0 o>| 'clfy o>Mod ( v o>' a )
                : 'Mod(0 V'' |- [0 'D0| A1 ~> A2 ]0)0 )

    | DeClassifying_arrowLog :
        forall (V V' V'' : obV log) (v : V(0 V' |- V )0) (v0 : V(0 V'' |- V' )0) (A1 A2 : obMod)
          (a : 'D(0 V |- [0 A1 ~> A2 ]0 )0),
          ( ( v0 o> v ) o>| a o>Mod 'declfy )
            <~~ ( v0 o>' ( v o>| a o>Mod 'declfy )
                  : 'D(0 V'' |- [0 A1 ~> 'D0| A2 ]0)0 )

    | DeClassifying_arrow :
        forall (V V' V'' : obV log) (v : V(0 V' |- V )0) (v0 : V(0 V'' |- V' )0) (A1 A2 : obMod)
          (a : 'D(0 V |- [0 A1 ~> A2 ]0 )0),
          ( ( v0 o> v ) o>| a o>Mod 'declfy )
            <~~ ( v0 o>| ( v o>' a ) o>Mod 'declfy
                  : 'D(0 V'' |- [0 A1 ~> 'D0| A2 ]0)0 )

    | PolyV_Mod_arrowLog :
        forall (V'' V' : obV log) (v' : V(0 V'' |- V' )0) (V : obV log)
          (v : V(0 V' |- V )0) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
          ( ( v' o> v ) o>' a )
            <~~ ( v' o>' ( v o>' a )
                  : 'Mod(0 V'' |- [0 A1 ~> A2 ]0)0 )

    | DeClass_morphismPost :
        forall (A : obMod)
          (W_ W_' : obV log) (v : V(0 W_' |- (0 W_ & log.-I )0 )0) (A' : obMod) (a_ : 'Mod(0 W_ |- [0 A ~> A' ]0 )0)
          (W' : obV log) (A'' : obMod) (a' : 'Mod(0 W' |- [0 A' ~> A'' ]0 )0),
        forall (W'W_' : obV log) (v0 : V(0 W'W_' |- (0 W' & W_' )0 )0),
          ( ( v0 o> desIdenObRKV ) o>| 'D1| ( (log.-1) o>| ( ( v o> desIdenObRK ) o>' a_ ) o>Mod a' )  )
            <~~ ( v0 o>| ( v o>| 'D1| a_ ) o>D a'
                  : 'D(0 W'W_' |- [0 'D0| A ~> A'' ]0)0 )

    | DeClass_morphismPre :
        forall (A : obMod) (V' : obV log) (B' : obMod) (b' : 'D(0 V' |- [0 B' ~> A ]0 )0),
        forall (W W' : obV log) (v : V(0 W' |- (0 W & log.-I )0 )0) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (W'V' : obV log) (v0 : V(0 W'V' |- (0 W' & V' )0 )0),
          ( v0  o>| b' o>D ( ( v o> desIdenObRK )  o>' a ) )
            <~~ ( v0 o>| b' o>Mod ( v o>| 'D1| a )
                  : 'D(0 W'V' |- [0 B' ~> A' ]0)0 )

    | PolyV_Mod_unit :
        forall (V : obV log) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
          ( a ) <~~ ( log.-1 o>' a
                      : 'Mod(0 V |- [0 A1 ~> A2 ]0)0 )

    | Mod_unit :
        forall (A : obMod) (V : obV log) (v : V(0 V |- log.-I )0)
          (W : obV log) (A' : obMod) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
          ( ( v0 o> log.-(0 W & v )1 o> desIdenObRK ) o>' a )
            <~~ ( v0 o>| ( v o>| uMod ) o>Mod a
                  : 'Mod(0 WV |- [0 A ~> A' ]0)0 )

    | Mod_inputUnitMod :
        forall (V : obV log) (B : obMod) (A : obMod) (b : 'Mod(0 V |- [0 B ~> A ]0 )0),
        forall (W : obV log) (w : V(0 W |- log.-I )0),
        forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
          ( ( w0 o> log.-(1 w & V )0 o> desIdenObLK ) o>' b )
            <~~  ( w0 o>| b o>Mod ( w o>| uMod )
                   : 'Mod(0 WV |- [0 B ~> A ]0)0 )

    | DeClass_unit :
        forall (V : obV log) (v : V(0 V |- log.-I )0) (A : obMod) (A' : obMod) (W : obV log) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
          ( ( v0 o> log.-(0 W & v )1 ) o>| 'D1| a )
            <~~ ( v0 o>| ( v o>| uMod ) o>D a
                  : 'D(0 WV |- [0 'D0| A ~> A' ]0 )0 )

    | DeClass_inputUnitMod :
        forall (V : obV log) (B : obMod) (A : obMod) (b : 'D(0 V |- [0 B ~> A ]0 )0),
        forall (W : obV log) (w : V(0 W |- log.-I )0),
        forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
          ( ( w0 o> ( log.-(1 w & _ )0 ) o> desIdenObLK ) o>' b )
            <~~ ( w0 o>| b o>D ( w o>| uMod )
                  : 'D(0 WV |- [0 B ~> A ]0)0 )

    | Classifying_morphismPre :
        forall (V V' : obV log) (v : V(0 V' |- V )0 ) (A1 A2 : obMod) (a_ : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
          (W : obV log) (A3 : obMod) (a' : 'Mod(0 W |- [0 A2 ~> A3 ]0 )0),
        forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
          ( ( log.-1 ) o>| 'clfy o>Mod ( ( v0 o> (0 _ & v )1 ) o>| a_ o>Mod a' ) )
            <~~ ( v0 o>| (v o>| 'clfy o>Mod a_ ) o>Mod a'
                  : 'Mod(0 WV' |- [0 'D0| A1 ~> A3 ]0)0 )

    | Classifying_morphismPre_DeClass :
        forall (V V' : obV log) (v : V(0 V' |- V )0 ) (A1 A2 : obMod) (b : 'D(0 V |- [0 A1 ~> A2 ]0 )0)
          (W : obV log) (A3 : obMod) (a' : 'Mod(0 W |- [0 A2 ~> A3 ]0 )0),
        forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
          ( ( log.-1 ) o>| 'clfy o>Mod ( ( v0 o> (0 _ & v )1 ) o>| b o>D a' ) )
            <~~ ( v0 o>| (v o>| 'clfy o>Mod b ) o>D a'
                  : 'D(0 WV' |- [0 'D0| A1 ~> A3 ]0)0 )

    | Classifying_morphismPost :
        forall (V V' : obV log) (v : V(0 V' |- (0 V & log.-I )0 )0) (A1 A2 : obMod) (a_ : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
          (W W' : obV log) (w : V(0 W' |- W )0) (A3 : obMod) (a' : 'Mod(0 W |- [0 A2 ~> A3 ]0 )0),
      forall (W'V' : obV log) (v0 : V(0 W'V' |- (0 W' & V' )0 )0),
        ( ( log.-1 )
            o>| 'clfy o>Mod ( v0 o>| ( ( v o> desIdenObRK ) o>' a_ ) o>Mod (w o>' a') ) )
          <~~ ( v0 o>| ( v o>| 'D1| a_ ) o>Mod ( w o>| 'clfy o>Mod a' )
                : 'Mod(0 W'V' |- [0 'D0| A1 ~> A3 ]0)0 ) 

    | DeClassifying_morphismPost :
        forall (V : obV log) (A1 A2 : obMod) (b_ : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
          (W W' : obV log) (w : V(0 W' |- W )0) (A3 : obMod) (b' : 'D(0 W |- [0 A2 ~> A3 ]0 )0),
        forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
          ( ( log.-1 ) o>| ( ( w0 o> (1 w & _ )0 ) o>| b_ o>Mod b' ) o>Mod 'declfy )
            <~~ ( w0 o>| b_ o>Mod ( w o>| b' o>Mod 'declfy )
                  : 'D(0 W'V |- [0 A1 ~> 'D0| A3 ]0)0 )

    | DeClassifying_morphismPre :
        forall (V V' : obV log) (v : V(0 V' |- V )0) (A1 A2 : obMod) (b_ : 'D(0 V |- [0 A1 ~> A2 ]0 )0)
          (W W' : obV log) (w : V(0 W' |- (0 W & log.-I )0 )0) (A4 : obMod) (b' : 'Mod(0 W |- [0 A2 ~> A4 ]0 )0),
        forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
          ( log.-1 o>| ( wv o>| ( v o>' b_ ) o>D ( ( w o> desIdenObRK ) o>' b') ) o>Mod 'declfy )
            <~~ ( wv o>| ( v o>| b_ o>Mod 'declfy ) o>D ( w o>| 'D1| b' )
                  : 'D(0 W'V' |- [0 A1 ~> 'D0| A4 ]0)0 )

    | CancelOuter : forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
                      (b : 'D(0 V |- [0 B ~> A ]0 )0) (A' : obMod)
                      (W W' : obV log) (w : V(0 W' |- W )0) (a : 'Mod(0 W |- [0 'D0| A ~> A' ]0 )0),
        forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
          ( wv o>| ( v o>' b ) o>Mod ( w o>' a ) )
            <~~ ( wv o>| ( v o>| b o>Mod 'declfy ) o>Mod ( w o>| 'clfy o>Mod a )
                  : 'Mod(0 W'V' |- [0 B ~> A' ]0)0 )

    | CancelInner : forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
                      (b : 'D(0 V |- [0 B ~> A ]0 )0) (A' : obMod)
                      (W W' : obV log) (w : V(0 W' |- W )0) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0),
        forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
          ( wv o>| (v o>' b) o>D (w o>' a) )
            <~~ ( wv o>| (v o>| b o>Mod 'declfy ) o>D (w o>| 'clfy o>Mod a )
                  : 'D(0 W'V' |- [0 B ~> A' ]0)0 )

    | PermOuterInner : forall (V V' : obV log) (v : V(0 V' |- V )0) (B : obMod) (A : obMod)
                         (b : 'D(0 V |- [0 B ~> A ]0 )0) (W W' : obV log) (w : V(0 W' |- W )0)
                         (u : V(0 W |- log.-I )0),
        forall (W'V' : obV log) (wv : V(0 W'V' |- (0 W' & V' )0 )0),
          ( wv o>| ( ( log.-(1 w & _ )0 o> log.-(1 u & _ )0 o> desIdenObLK ) o>| ( v o>' b ) o>Mod 'declfy ) o>Mod 'declfy )
            <~~ ( wv o>| ( v o>| b o>Mod 'declfy ) o>D ( w o>| (u o>| uMod) o>Mod 'declfy )
                  : 'D(0 W'V' |- [0 B ~> 'D0| 'D0| A ]0)0 )

    | IterPermOuterInner :
        forall {trf : obV log -> obV log}
          (Wb : obV log) (Vs : list (obV log)) (W_dft: obV log) (Wba : obV log)
          (Wb' : obV log) (wb : V(0 Wb' |- Wb )0)
          (trf':=fun z => (0 (trf z) & Wb' )0)
          (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
          (wa : V(0 trf(last W_dft Vs) |- log.-I )0)
          (wba : V(0 Wba |- (0 trf(head W_dft Vs) & Wb' )0 )0)
          (B : obMod) (A : obMod) (b : 'D(0 Wb |- [0 B ~> A ]0 )0),
          ( wba o>| (iterDeClassifying (V_dft:=W_dft)
            (hmap (B2:=toArrowV (trf:=trf')) (fun U1U2 u => ((1 u & Wb')0)) vs)
            ( ( (1 wa  & _ )0 o> (0 _ & wb)1 o> desIdenObLK ) o>' b ))
                o>Mod 'declfy )
            <~~ ( wba o>| ( wb o>| b o>Mod 'declfy )
                    o>D (iterDeClassifying (V_dft:=W_dft) vs ( wa o>| uMod ))
                : 'D(0 Wba |- [0 B ~> 'D0| (iterDeClass0 (length Vs).-1 A) ]0)0 )

    | IterPermOuterInner_DeClass :
        forall {trf : obV log -> obV log}
          (Wb Wa : obV log) (Vs : list (obV log)) (W_dft: obV log) (Wba : obV log)
          (Wb' : obV log) (wb : V(0 Wb' |- Wb )0)
          (trf':=fun z => (0 (trf z) & Wb' )0)
          (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
          (wa : V(0 trf(last W_dft Vs) |- (0 Wa & log.-I )0 )0)
          (wba : V(0 Wba |- (0 trf(head W_dft Vs) & Wb' )0 )0)
          (B : obMod) (A : obMod) (b : 'D(0 Wb |- [0 B ~> A ]0 )0)
          (A' : obMod) (a : 'Mod(0 Wa |- [0 A ~> A' ]0 )0),
            ( wba o>| (iterDeClassifying (V_dft:=W_dft)
              (hmap (B2:=toArrowV (trf:=trf')) (fun U1U2 u => ((1 u & Wb')0)) vs)
              ( ( (1 wa o> desIdenObRK & _ )0 o> (0 _ & wb)1 ) o>| b o>D a ))
                  o>Mod 'declfy )
              <~~ ( wba o>| ( wb o>| b o>Mod 'declfy )
                      o>D (iterDeClassifying (V_dft:=W_dft) vs ( wa o>| 'D1| a ))
                  : 'D(0 Wba |- [0 B ~> 'D0| (iterDeClass0 (length Vs).-1 A') ]0)0 )

    | IterCancelInner :
        forall {trf : obV log -> obV log}
          (Vb Vb' : obV log) (vb : V(0 Vb' |- Vb )0)
          (W W_dft : obV log) (V0Vb' : obV log) (Vs : list (obV log))
          (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
          (va : V(0 trf(last W_dft Vs) |- W )0)
          (v0b : V(0 V0Vb' |- (0 trf(head W_dft Vs) & Vb' )0 )0)
          (B : obMod) (A : obMod) (b : 'D(0 Vb |- [0 B ~> A ]0 )0)
          (A' : obMod)(a : 'D(0 W |- [0 A ~> A' ]0 )0),
          ( v0b o>| ( vb o>' b)  o>D (iterDeClassifying (V_dft := W_dft) vs ( va o>' a)) )
            <~~ ( v0b o>| (vb o>| b o>Mod 'declfy )
                    o>D (iterDeClassifying (V_dft := W_dft) vs (va o>| 'clfy o>Mod a) )
                : 'D(0 V0Vb' |- [0 B ~> 'D0| (iterDeClass0 (length Vs).-1 A') ]0)0 )

    where "f2 <~~ f1" := (@convMod _ _ _ _ f2 f1).

    Module Export Ex_Notations.

      Notation "f2 <~~ f1" := (@convMod _ _ _ _ f2 f1).
      Hint Constructors convMod.
      Hint Extern 0 (_ <~~ _) =>
      ( exact: (@Red.IterPermOuterInner _ id) ) : iter_hints.
      Hint Extern 0 (_ <~~ _) =>
      ( exact: (@Red.IterPermOuterInner_DeClass _ id) ) : iter_hints.
      Hint Extern 0 (_ <~~ _) =>
      ( exact: (@Red.IterCancelInner _ id) ) : iter_hints.

      Add Parametric Relation {log : logic} (V : obV log) (A1 A2 : obMod) :
        ('Mod(0 V |- [0 A1 ~> A2 ]0 )0) (@convMod log V A1 A2)
          transitivity proved by
          (fun x y z r1 r2 =>  ((@Mod_TransV log V A1 A2) y z r2 x r1))
            as convMod_rewrite.
      
    End Ex_Notations.

(**#+END_SRC

** Degradation lemmas

#+BEGIN_SRC coq :exports both :results silent **)

    Lemma Red_convMod_convMod {log : logic} :
      forall (V : obV log) (A1 A2 : obMod) (a aDeg : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        aDeg <~~ a -> aDeg ~~~ a.
    Proof.
      move => V A1 A2 a aDeg. elim; eauto. Show.
    Qed.

    Lemma degrade {log : logic} :
      forall (V : obV log) (A1 A2 : obMod) (aDeg a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        aDeg <~~ a ->
        ((grade aDeg) <= (grade a))%coq_nat
        /\ ( ( (gradeTotal aDeg) < (gradeTotal a) )%coq_nat ).
    Proof.
      (move => V A1 A2 aDeg a red_a); elim : V A1 A2 aDeg a / red_a;
        try solve [ ( rewrite /gradeTotal /= => * );
                    repeat rewrite !(grade_iterDeClassifying,
                                     gradeCom_iterDeClassifying,
                                     gradeDeClass_iterDeClassifying) /= ;
                    abstract intuition Omega.omega ].
    Qed.
    Hint Resolve degrade.

    Lemma degradeTotal {log : logic} :
      forall (V : obV log) (A1 A2 : obMod) (aDeg a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        aDeg <~~ a -> ( (gradeTotal aDeg) < (gradeTotal a) )%coq_nat.
    Proof.
      eapply degrade.
    Qed.
    Hint Resolve degradeTotal.

    Lemma degrade_gt0 {log : logic} :
      forall (V : obV log) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        ((S O) <= grade a )%coq_nat.
    Proof.
      move=> V A1 A2 a; apply/leP; elim : a; simpl; auto. (* alt: Omega.omega. *)
    Qed.
    Hint Resolve degrade_gt0.

    Lemma degradeTotal_gt0 {log : logic} :
      forall (V : obV log) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0),
        ((S O) <= gradeTotal a )%coq_nat.
    Proof.
      move=> V A1 A2 a; move: (degrade_gt0 a);
              rewrite /gradeTotal; move => * ; Omega.omega.
    Qed.

  End Red.

(**#+END_SRC

* Solution

** Grammatical generation of the solution morphisms

#+BEGIN_SRC coq :exports both :results silent **)
  
  Module Sol.

    Section Section1.

    Delimit Scope gen_scope with gen.

    Inductive Mod_genAtomic {log : logic} : obV log -> obMod_gen -> obMod_gen -> Type :=

    | GenArrowsMod : forall (V V' : obV log), forall A1 A2 : obMod_gen
        , Mod_gen V A1 A2 -> 
          V(0 V' |- V )0 -> 'Mod(0 V' |- [0 A1 ~> A2 ]0 )0

    | PolyMod : forall (V : obV log) (A2 : obMod_gen) (A1 : obMod_gen)
      , 'Mod(0 V |- [0 A2 ~> A1 ]0 )0 -> forall A1' : obMod_gen, forall (W WV : obV log),
            V(0 WV |- (0 W & V )0 )0 ->
            'Mod(0 W |- [0 A1 ~> A1' ]0 )0 -> 'Mod(0 WV |- [0 A2 ~> A1' ]0 )0
    where
    "''Mod' (0 V |- [0 A1 ~> A2 ]0 )0"
      := (@Mod_genAtomic _ V A1 A2) : gen_scope.

    Inductive Mod00 {log : logic} : obV log -> obMod -> obMod -> Type :=

    | GenAtomicArrowsMod : forall (V : obV log), forall A1 A2 : obMod_gen
        , ( 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 ) %gen -> 'Mod(0 V |- [0 (#0| A1) ~> (#0| A2) ]0 )0

    | UnitMod : forall (V : obV log), forall {A : obMod}
        ,  V(0 V |- log.-I )0 -> 'Mod(0 V |- [0 A ~> A ]0 )0

    | UnitDeClass : forall (A : obMod) (A' : obMod) (W W' : obV log)
      , V(0 W' |- (0 W & log.-I)0 )0 ->
        'Mod(0 W |- [0 A ~> A' ]0 )0 -> 'D(0 W' |- [0 'D0| A ~> A' ]0 )0

    | Classifying : forall (V V' : obV log), forall (A1 A2 : obMod),
          V(0 V' |- V )0 ->
          'Mod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'Mod(0 V' |- [0 ('D0| A1) ~> A2 ]0 )0

    | DeClassifying : forall (V V' : obV log), forall (A1 A2 : obMod),
          V(0 V' |- V )0 -> 
          'D(0 V |- [0 A1 ~> A2 ]0 )0 -> 'D(0 V' |- [0 A1 ~> ('D0| A2) ]0 )0

    where
    "''Mod' (0 V |- [0 A1 ~> A2 ]0 )0"
      := (@Mod00 _ V A1 A2) and "''D' (0 V |- [0 A1 ~> A2 ]0 )0"
           := (@Mod00 _ V A1 ('D0| A2)).

    End Section1.
    
    Module Import Ex_Notations0.
      Delimit Scope sol_scope with sol.
      Coercion GenAtomicArrowsMod : Mod_genAtomic >-> Mod00.
      Notation "''Mod' (0 V |- [0 A1 ~> A2 ]0 )0"
        := (@Mod00 _ V A1 A2) : sol_scope.
      Notation "''D' (0 V |- [0 A1 ~> A2 ]0 )0"
        := (@Mod00 _ V A1 ('D0| A2)) : sol_scope.
      Notation "v o>| #1| a" :=
        (@GenArrowsMod _ _ _ _ _ a v) (at level 25, right associativity) : sol_scope.
      Notation "v o>| a_ o>Mod a'" :=
        (@PolyMod _ _ _ _ a_ _ _ _ v a')
          (at level 25, right associativity, a_ at next level, format "v  o>|  a_  o>Mod  a'") : sol_scope.
      Notation "v o>| 'uMod'" := (@UnitMod _ _ _ v)(at level 25) : sol_scope.
      Notation "v o>| @ 'uMod' A" :=
        (@UnitMod _ _ A v) (at level 25, only parsing) : sol_scope.
      Notation "v o>| ''D1|' a" := (@UnitDeClass _ _ _ _ _ v a)
                                     (at level 25, right associativity) : sol_scope.
      Notation "v o>| 'clfy o>Mod a'" :=
        (@Classifying _ _ _ _ _ v a') (at level 25, right associativity) : sol_scope.
      Notation "v o>| a_ o>Mod 'declfy" :=
        (@DeClassifying _ _ _ _ _ v a_) (at level 25, a_ at next level, right associativity) : sol_scope.
    End Ex_Notations0.

(**#+END_SRC

** Containment of the solution morphisms into all the morphisms

#+BEGIN_SRC coq :exports both :results silent **)

    Definition iterDeClassifyingSol {log : logic} {trf : obV log -> obV log}
               (V_dft : obV log) (B A : obMod) 
      : forall (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
          (b : 'D(0 trf (last V_dft Vs) |- [0 B ~> A ]0 )0 % sol),
        'D(0 trf(head V_dft Vs) |- [0 B ~> iterDeClass0 (length Vs).-1 A ]0 )0 %sol .
    Proof.
      move => Vs vs. move: (arrowListP (trf:=trf) vs). elim => /= .
      - move => b; exact: b.
      - move => V0 b; exact: b.
      - move => V0 V1 v01 Vs'' vs' vs'_arrowListP vs'_IH b.
        refine (v01 o>| (vs'_IH b)  o>Mod 'declfy)%sol.
    Defined.

    Module Import Ex_Notations.
      Export Ex_Notations0.
      Notation "vs o>|| a o>Mod ''declfy" :=
        (@iterDeClassifyingSol _ _ _ _ _ _ vs a)
          (at level 25, a at next level, right associativity) : sol_scope.
    End Ex_Notations.

    Definition toMod_gen {log : logic} : forall (V : obV log) (A1 A2 : obMod_gen),
        Mod_genAtomic V A1 A2 -> 'Mod(0 V |- [0 #0| A1 ~> #0| A2 ]0 )0.
    Proof.
      move => V A1 A2 a; elim : V A1 A2 / a =>
      [ V V' A1 A2 aGen v (* (v o>| #1| aGen)%sol *)
      | V A2 A1 a_GenAtom a_GenAtom_toMod A1' W WV wv a'GenAtom a'GenAtom_toMod
          (* (a_GenAtom o>Mod a'GenAtom)%sol *)
          ] ;
        [ apply: (v o>| #1| aGen)
        | apply: (wv o>| a_GenAtom_toMod o>Mod a'GenAtom_toMod) ].
    Defined.

    Definition toMod {log : logic} : forall (V : obV log) (A1 A2 : obMod),
        'Mod(0 V |- [0 A1 ~> A2 ]0 )0 % sol -> 'Mod(0 V |- [0 A1 ~> A2 ]0 )0.
    Proof.
        (move => V A1 A2 a); elim : V A1 A2 / a =>
        [ V A1 A2 a (* GenAtomicArrowsMod *)
        | V A v (* (v o>| @uMod A)%sol *)
        | A A' W W' v aSol aSol_toMod  (* (v o>| 'D1| aSol)%sol *)
        | V V' A1 A2 v aSol aSol_toMod  (* (v o>| 'clfy o>Mod aSol)%sol *)
        | V V' A1 A2 v aSol aSol_toMod  (* (v o>| aSol o>Mod 'declfy)%sol *)
        ] ;
          [ apply: toMod_gen a
          | apply: (v o>| @uMod A)
          | apply: (v o>| 'D1| aSol_toMod)
          | apply: (v o>| 'clfy o>Mod aSol_toMod)
          | apply: (v o>| aSol_toMod o>Mod 'declfy) ].
    Defined.

    Lemma toMod_iterDeClassifyingSol {log : logic} {trf : obV log -> obV log}
               (V_dft : obV log) (B A : obMod) 
      : forall (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=trf)) (chain Vs)))
          (b : 'D(0 trf (last V_dft Vs) |- [0 B ~> A ]0 )0 % sol),
        toMod (vs o>|| b o>Mod ''declfy)%sol = vs o>|| toMod b o>Mod ''declfy.
    Proof.
      move => Vs vs; elim: Vs vs / (arrowListP vs).
      - reflexivity.
      - reflexivity.
      - move => V0 V1 v01 Vs' vs' vs'_arrowListP IH_vs'_arrowListP b.
        rewrite (iterDeClassifying_rewrite (v01 ::: vs' : arrowList (V0 :: V1 :: Vs'))).
        rewrite -IH_vs'_arrowListP. reflexivity.      
    Defined.

(**#+END_SRC

** Destruction of morphisms with inner-instantiation of object-indices

Lemmas for (dependent-)destruction by inner instantiations of indices (objects).

Where the domain of the morphism is some object of the generator graph :

#+BEGIN_SRC coq :exports both :results silent **)
    
    Module Destruct_domGen.

      Inductive Mod00_domGen {log : logic}
      : forall (V : obV log) (A1 : obMod_gen) (A2 : obMod),
        ( 'Mod(0 V |- [0 #0| A1 ~> A2 ]0 )0 %sol ) -> Type :=

      | GenAtomicArrowsMod : forall (V : obV log) (A1 A2 : obMod_gen)
                               (aGen : Mod_genAtomic V A1 A2),
          Mod00_domGen (GenAtomicArrowsMod aGen)

      | UnitMod : forall (V : obV log) {A : obMod_gen} (v : V(0 V |- log.-I )0),
          Mod00_domGen (v o>| @uMod (#0| A) )%sol

      | DeClassifying : forall (V V' : obV log) (A1 : obMod_gen) (A2 : obMod)
                          (v : V(0 V' |- V )0)
                          (a : 'D(0 V |- [0 #0| A1 ~> A2 ]0 )0 %sol ),
          Mod00_domGen (v o>| a o>Mod 'declfy)%sol.

      Lemma Mod00_domGenP {log : logic}
        : forall (V : obV log) (A1 : obMod) (A2 : obMod)
            ( a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol ),
          match A1 as A1 return 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol -> Type with
          | 'D0| A1 => fun _ => unit
          | #0| A1 => fun a => @Mod00_domGen log V A1 A2 a
          end a.
      Proof.
        intros. case: V A1 A2 / a.
        - constructor 1.
        - intros. destruct A. constructor 2. exact: tt.
        - intros. exact: tt.
        - intros. exact: tt.
        - intros. destruct A1. constructor 3. exact: tt.
      Defined.

    End Destruct_domGen.

(**#+END_SRC

Where the domain of the morphism is some functor-onto-object construction :

#+BEGIN_SRC coq :exports both :results silent **)

    Module Destruct_domDeClass.

      Inductive Mod00_domDeClass {log : logic}
      : forall (V : obV log) (A1 : obMod) (A2 : obMod),
        ( 'Mod(0 V |- [0 'D0| A1 ~> A2 ]0 )0 %sol ) -> Type :=
                                                             
      | UnitMod : forall (V : obV log) {A : obMod} (v : V(0 V |- log.-I )0),
          Mod00_domDeClass (v o>| @uMod ('D0| A))%sol
                                                     
      | UnitDeClass : forall (A : obMod) (A' : obMod) (W W' : obV log)
                        ( v : V(0 W' |- (0 W & log.-I)0 )0) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0 %sol),
          Mod00_domDeClass (v o>| 'D1| a)%sol

      | Classifying : forall (V V' : obV log) (A1 A2 : obMod)
                        (v : V(0 V' |- V )0) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol),
          Mod00_domDeClass (v o>| 'clfy o>Mod a)%sol

      | DeClassifying :
          forall (V V' : obV log) (A1 : obMod) (A2 : obMod) (v : V(0 V' |- V )0)
            (a : 'D(0 V |- [0 'D0| A1 ~> A2 ]0 )0 %sol ),
            Mod00_domDeClass (v o>| a o>Mod 'declfy)%sol.

      Lemma Mod00_domDeClassP {log : logic}
        : forall (V : obV log) (A1 : obMod) (A2 : obMod)
            ( a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol ),
          match A1 as A1 return 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol -> Type with
          | 'D0| A1 => fun a => @Mod00_domDeClass log V A1 A2 a
          | #0| A1 => fun _ => unit
          end a.
      Proof.
        intros. case: V A1 A2 / a.
        - intros. exact: tt.
        - move => V A v. destruct A. exact: tt. constructor 1.
        - intros. constructor 2.
        - move => V V' A1 A2 v a. constructor 3.
        - move => V V' A1 A2 v a. destruct A1. exact: tt. constructor 4. 
      Defined.

    End Destruct_domDeClass.

(**#+END_SRC

Where the domain of the morphism is deeper two functor-onto-object constructions :

#+BEGIN_SRC coq :exports both :results silent **)

    Module Destruct_dom2DeClass.

      Inductive Mod00_dom2DeClass {log : logic}
      : forall (V : obV log) (A1 : obMod) (A2 : obMod),
        ( 'Mod(0 V |- [0 'D0| ('D0| A1) ~> A2 ]0 )0 %sol ) -> Type :=
                                                             
      | UnitMod : forall (V : obV log) {A : obMod} (v : V(0 V |- log.-I )0),
          Mod00_dom2DeClass (v o>| @uMod ('D0| ('D0| A)))%sol
                                                     
      | UnitDeClass : forall (A : obMod) (A' : obMod) (W W' : obV log)
                        ( v : V(0 W' |- (0 W & log.-I)0 )0) (a : 'Mod(0 W |- [0 'D0| A ~> A' ]0 )0 %sol),
          Mod00_dom2DeClass (v o>| 'D1| a)%sol

      | Classifying : forall (V V' : obV log) (A1 A2 : obMod)
                        (v : V(0 V' |- V )0) (a : 'Mod(0 V |- [0 'D0| A1 ~> A2 ]0 )0 %sol),
          Mod00_dom2DeClass (v o>| 'clfy o>Mod a)%sol

      | DeClassifying :
          forall (V V' : obV log) (A1 : obMod) (A2 : obMod) (v : V(0 V' |- V )0)
            (a : 'D(0 V |- [0 'D0| ('D0| A1) ~> A2 ]0 )0 %sol ),
            Mod00_dom2DeClass (v o>| a o>Mod 'declfy)%sol.

      Lemma Mod00_dom2DeClassP {log : logic}
        : forall (V : obV log) (A1 : obMod) (A2 : obMod)
            ( a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol ),
          match A1 as A1 return 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol -> Type with
          | 'D0| A1 => fun a =>
                        match A1 as A1 return 'Mod(0 V |- [0 'D0| A1 ~> A2 ]0 )0 %sol -> Type with
                        | 'D0| A1 => fun a => @Mod00_dom2DeClass log V A1 A2 a
                        | #0| A1 => fun _ => unit
                        end a
          | #0| A1 => fun _ => unit
          end a.
      Proof.
        intros. case: V A1 A2 / a.
        - intros. exact: tt.
        - move => V A v. destruct A as [|A]; [exact: tt | destruct A; [exact: tt | constructor 1]].
        - move => A A' W W' v a. destruct A; [exact: tt | constructor 2].
        - move => V V' A1 A2 v a. destruct A1; [exact: tt | constructor 3].
        - move => V V' A1 A2 v a. destruct A1 as [|A1]; [exact: tt | destruct A1; [exact: tt | constructor 4]].
      Defined.

    End Destruct_dom2DeClass.

(**#+END_SRC

Where the codomain of the morphism is some functor-onto-object construction :

#+BEGIN_SRC coq :exports both :results silent **)

    Module Destruct_codomDeClass.

      Inductive Mod00_codomDeClass {log : logic}
      : forall (V : obV log) (A1 : obMod) (A2 : obMod),
        ( 'Mod(0 V |- [0 A1 ~> 'D0| A2 ]0 )0 %sol ) -> Type :=
                                                             
      | UnitMod : forall (V : obV log) {A : obMod} (v : V(0 V |- log.-I )0),
          Mod00_codomDeClass (v o>| @uMod ('D0| A))%sol
                                                     
      | UnitDeClass : forall (A : obMod) (A' : obMod) (W W' : obV log)
                        ( v : V(0 W' |- (0 W & log.-I)0 )0) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0 %sol),
          Mod00_codomDeClass (v o>| 'D1| a)%sol

      | Classifying : forall (V V' : obV log) (A1 A2 : obMod)
                        (v : V(0 V' |- V )0) (a : 'Mod(0 V |- [0 A1 ~> 'D0| A2 ]0 )0 %sol),
          Mod00_codomDeClass (v o>| 'clfy o>Mod a)%sol

      | DeClassifying :
          forall (V V' : obV log) (A1 : obMod) (A2 : obMod) (v : V(0 V' |- V )0)
            (a : 'D(0 V |- [0 A1 ~> A2 ]0 )0 %sol ),
            Mod00_codomDeClass (v o>| a o>Mod 'declfy)%sol.

      Lemma Mod00_codomDeClassP {log : logic}
        : forall (V : obV log) (A1 : obMod) (A2 : obMod)
            ( a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol ),
          match A2 as A2 return 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol -> Type with
          | 'D0| A2 => fun a => @Mod00_codomDeClass log V A1 A2 a
          | #0| A2 => fun _ => unit
          end a.
      Proof.
        intros. case: V A1 A2 / a.
        - intros. exact: tt.
        - move => V A v. destruct A. exact: tt. constructor 1.
        - intros. constructor 2.
        - move => V V' A1 A2 v a. destruct A2. intros; exact: tt. constructor 3.
        - move => V V' A1 A2 v a. constructor 4. 
      Defined.

    End Destruct_codomDeClass.

(**#+END_SRC

Where both domain and codomain of the morphism are some functor-onto-object
constructions :

#+BEGIN_SRC coq :exports both :results silent **)

    Module Destruct_domCodomDeClass.

      Inductive Mod00_domCodomDeClass {log : logic}
      : forall (V : obV log) (A1 : obMod) (A2 : obMod),
        ( 'Mod(0 V |- [0 'D0| A1 ~> 'D0| A2 ]0 )0 %sol ) -> Type :=
                                                             
      | UnitMod : forall (V : obV log) {A : obMod} (v : V(0 V |- log.-I )0),
          Mod00_domCodomDeClass (v o>| @uMod ('D0| A))%sol
                                                     
      | UnitDeClass : forall (A : obMod) (A' : obMod) (W W' : obV log)
                        ( v : V(0 W' |- (0 W & log.-I)0 )0) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0 %sol),
          Mod00_domCodomDeClass (v o>| 'D1| a)%sol

      | Classifying : forall (V V' : obV log) (A1 A2 : obMod)
                        (v : V(0 V' |- V )0) (a : 'Mod(0 V |- [0 A1 ~> 'D0| A2 ]0 )0 %sol),
          Mod00_domCodomDeClass (v o>| 'clfy o>Mod a)%sol

      | DeClassifying :
          forall (V V' : obV log) (A1 : obMod) (A2 : obMod) (v : V(0 V' |- V )0)
            (a : 'D(0 V |- [0 'D0| A1 ~> A2 ]0 )0 %sol ),
            Mod00_domCodomDeClass a ->
            Mod00_domCodomDeClass (v o>| a o>Mod 'declfy)%sol.

      Lemma Mod00_domCodomDeClassP {log : logic}
        : forall (V : obV log) (A1 : obMod) (A2 : obMod)
            ( a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol ),
          match A1 as A1 return 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol -> Type with
          | 'D0| A1 => fun a =>
                        match A2 as A2 return 'Mod(0 V |- [0 'D0| A1 ~> A2 ]0 )0 %sol -> Type with
                        | 'D0| A2 => fun a => @Mod00_domCodomDeClass log V A1 A2 a
                        | #0| A2 => fun _ => unit
                        end a
          | #0| A1 => fun _ => unit
          end a.
      Proof.
        intros. elim: V A1 A2 / a.
        - intros. exact: tt.
        - move => V A v. destruct A. exact: tt. constructor 1.
        - intros. constructor 2.
        - move => V V' A1 A2 v a _ . destruct A2. exact: tt. constructor 3.
        - move => V V' A1 A2 v a IHa. destruct A1. exact: tt. constructor 4.
          exact: IHa.
      Defined.

    End Destruct_domCodomDeClass.

(**#+END_SRC

** Iterated =DeClassifying= prefix

Any solution morphism may be written as some decomposition with maximal prefix of
iterated =DeClassifying= constructors :

#+BEGIN_SRC coq :exports both :results silent **)

    Module Destruct_iterDeClassifying.

      Inductive codomDeClass_prefixDeClassifying_Sol {log : logic} : forall (V : obV log) (A1 A2 : obMod),
        'Mod(0 V |- [0 'D0| A1 ~> 'D0| A2 ]0 )0 % sol -> Type :=

      | IterDeClassifying_UnitMod : 
          forall (V_dft : obV log) (A : obMod) 
           (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=fun z => z)) (chain Vs)))
           (va : V(0 last V_dft Vs |- log.-I )0),
           codomDeClass_prefixDeClassifying_Sol (iterDeClassifyingSol (V_dft:=V_dft) vs
           ( va o>| @uMod ('D0| A) )%sol)

      | IterDeClassifying_UnitDeClass : 
         forall (V_dft : obV log) (A A' : obMod) 
           (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=fun z => z)) (chain Vs)))
           (Va : obV log) (va : V(0 last V_dft Vs |- (0 Va & log.-I)0 )0)
           (a : 'Mod(0 Va |- [0 A ~> A' ]0 )0 %sol ),
           codomDeClass_prefixDeClassifying_Sol (iterDeClassifyingSol (V_dft:=V_dft) vs
           ( va o>| 'D1| a )%sol)

      | IterDeClassifying_Classifying : 
         forall (V_dft : obV log) (A1 A2 : obMod) 
           (Vs : list (obV log)) (vs : (hlist (toArrowV (trf:=fun z => z)) (chain Vs)))
           (Va : obV log) (va : V(0 last V_dft Vs |- Va )0)
           (a : 'D(0 Va |- [0 A1 ~> A2 ]0 )0 %sol ),
           codomDeClass_prefixDeClassifying_Sol (iterDeClassifyingSol (V_dft:=V_dft) vs
           ( va o>| 'clfy o>Mod a )%sol) .

      Inductive prefixDeClassifying_Sol {log : logic} : forall (V : obV log) (A1 A2 : obMod),
        'Mod(0 V |- [0 'D0| A1 ~> A2 ]0 )0 % sol -> Type :=
                                                      
      | UnitMod : forall (V : obV log) {A : obMod} (v : V(0 V |- log.-I )0),
          prefixDeClassifying_Sol (v o>| @uMod ('D0| A) )%sol
                                   
      | UnitDeClass :
          forall (A : obMod) (A' : obMod) (W W' : obV log)
            (v : V(0 W' |- (0 W & log.-I)0 )0) (a : 'Mod(0 W |- [0 A ~> A' ]0 )0 %sol),
            prefixDeClassifying_Sol (v o>| 'D1| a)%sol
                                        
      | Classifying : forall (V V' : obV log) (A1 A2 : obMod) (v : V(0 V' |- V )0)
                        (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol),
          prefixDeClassifying_Sol (v o>| 'clfy o>Mod a)%sol 

      | CodomDeClass_prefixDeClassifying_Sol :
          forall (V : obV log) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 'D0| A1 ~> 'D0| A2 ]0 )0 % sol),
            @codomDeClass_prefixDeClassifying_Sol log V A1 A2 a
            -> prefixDeClassifying_Sol a .

      Lemma prefixP0 {log : logic} (V : obV log) (A1 A2 : obMod)
            (a : 'Mod(0 V |- [0 'D0| A1 ~> 'D0| A2 ]0 )0 % sol) :
        codomDeClass_prefixDeClassifying_Sol a.
      Proof.
        elim : V A1 A2 a / (Destruct_domCodomDeClass.Mod00_domCodomDeClassP a). 
        - move => V A v. About IterDeClassifying_UnitMod.
          eapply (IterDeClassifying_UnitMod (V_dft:=V) (Vs:=[::]) A HNil v).
        - move => A A' W W' v a.
          eapply (IterDeClassifying_UnitDeClass (V_dft:=W') (Vs:=[::]) HNil v a).
        - move => V V' A1 A2 v a.
          eapply (IterDeClassifying_Classifying (V_dft:=V') (Vs:=[::]) HNil v a).
        - move => V V' A1 A2 v a (*a_domCodom*) _ IH_a_domCodom.
          (*Set Printing Implicit. Show.*)
          move: V' v. case: V A1 A2 a / IH_a_domCodom.
          + move => V_dft A [ | V0 Vs'] vs;
                     [ rewrite (hlist_eta vs) /= | ];
                     move => va V' v.
            eapply (IterDeClassifying_UnitMod (V_dft:=V_dft)
                   (Vs:=[:: V' ; (head V_dft [::])]) A
                   ((v : toArrowV (trf:=fun z => z) (V', (head V_dft [::])) ) ::: HNil) va).
            eapply (IterDeClassifying_UnitMod (V_dft:=V_dft)
                   (Vs:=[:: V', V0 & Vs']) A
                   ((v : toArrowV (trf:=fun z => z) (V', (head V_dft [:: V0 & Vs'])) ) ::: vs) va).
          + move => V_dft A A' [ | V0 Vs'] vs;
                     [ rewrite (hlist_eta vs) /= | ];
                     move => Va va a V' v.
            eapply (IterDeClassifying_UnitDeClass (V_dft:=V_dft)
                   (Vs:=[:: V' ; (head V_dft [::])])
                   ((v : toArrowV (trf:=fun z => z) (V', (head V_dft [::])) ) ::: HNil) va a).
            eapply (IterDeClassifying_UnitDeClass (V_dft:=V_dft)
                   (Vs:=[:: V', V0 & Vs'])
                   ((v : toArrowV (trf:=fun z => z) (V', (head V_dft [:: V0 & Vs'])) ) ::: vs) va a).
          + move => V_dft A1 A2 [ | V0 Vs'] vs;
                     [ rewrite (hlist_eta vs) /= | ];
                     move => Va va a V' v.
            eapply (IterDeClassifying_Classifying (V_dft:=V_dft)
                   (Vs:=[:: V' ; (head V_dft [::])])
                   ((v : toArrowV (trf:=fun z => z) (V', (head V_dft [::])) ) ::: HNil) va a).
            eapply (IterDeClassifying_Classifying (V_dft:=V_dft)
                   (Vs:=[:: V', V0 & Vs'])
                   ((v : toArrowV (trf:=fun z => z) (V', (head V_dft [:: V0 & Vs'])) ) ::: vs) va a).
      Defined.

      Lemma prefixP {log : logic} (V : obV log) (A1 A2 : obMod)
            (a : 'Mod(0 V |- [0 'D0| A1 ~> A2 ]0 )0 % sol) :
        prefixDeClassifying_Sol a.
      Proof.
        elim : V A1 A2 a / (Destruct_domDeClass.Mod00_domDeClassP a). 
        - constructor 1.
        - constructor 2.
        - constructor 3.
        - move => V V' A1 A2 v a. constructor 4. apply: Destruct_iterDeClassifying.prefixP0.
      Defined.

    End Destruct_iterDeClassifying.

  End Sol.

(**#+END_SRC

* Resolution

Any morphism is or may be reduced to some solution morphism. Memo that this resolution
is non-congruent which is that it is total / global cut elimination /
desintegration. Oneself may later attempt to program the congruent-resolution
technique such to get specifications for computational reflection and confluence and
decidability ...

This deduction is mostly-automated via these tactics which are inquired many times :

#+BEGIN_SRC coq :exports both :results silent **)

  Ltac tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop :=
    destruct a_Sol_prop as [a_Sol_prop |a_Sol_prop];
    [ move : (Red.degrade a_Sol_prop);
      destruct a'Sol_prop as [a'Sol_prop |a'Sol_prop];
      [ move : (Red.degrade a'Sol_prop)
      | subst ]
    | subst;
      destruct a'Sol_prop as [a'Sol_prop |a'Sol_prop];
      [ move : (Red.degrade a'Sol_prop)
      | subst ]
    ];
    move : H_gradeTotal; clear; rewrite /gradeTotal /= ;
    repeat rewrite Sol.toMod_iterDeClassifyingSol /= ;
    repeat rewrite !(grade_iterDeClassifying,
                     gradeCom_iterDeClassifying,
                     gradeDeClass_iterDeClassifying) /= ;
    move => * ; abstract intuition Omega.omega.

  Ltac tac_reduce :=
    simpl in *; abstract (
    intuition (eauto with iter_hints; try subst; rewriterMod; try congruence;
                               eauto 12 with iter_hints)).

  Section Section1.

  Import Sol.Ex_Notations.
  Import Red.Ex_Notations.
  Context {log : logic}.

(**#+END_SRC

Finally :

#+BEGIN_SRC coq :exports both :results silent **)

  Fixpoint solveMod len {struct len} :
    forall (V : obV log) (A1 A2 : obMod) (a : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0)
      (H_gradeTotal : (gradeTotal a <= len)%coq_nat),
      { aSol : 'Mod(0 V |- [0 A1 ~> A2 ]0 )0 %sol
      | ( (Sol.toMod aSol) <~~ a ) \/ ( (Sol.toMod aSol) = a ) }.
  Proof.
    case : len => [ | len ].

    (* n is O *)
    - clear; ( move => V A1 A2 a H_gradeTotal ); exfalso;
        move : (Red.degradeTotal_gt0 a) => H_degradeTotal_gt0; abstract Omega.omega.

    (* n is (S n) *)
    - move => V A1 A2 a; case : V A1 A2 / a =>
      [ V V' v A1 A2 a (* v o>' a *)
      | V V' A1 A2 aGen v (* v o>| #1| aGen *)
      | V A v (* v o>| @uMod A *)
      | V A2 A1 a_ A1' W WV wv a' (* wv o>| a_ o>Mod a' *)
      | A A' W W' v a (* v o>| 'D1| a *)
      | V B A b A' W WV wv a (* wv o>| b o>D a *)
      | V V' A1 A2 v a (* v o>| 'clfy o>Mod a *)
      | V V' A1 A2 v a (* v o>| a o>Mod 'dlclfy *) ].

      (* a is v o>' a *)
      + rewrite -/(v o>' a) => H_gradeTotal.
        case : (solveMod len _ _ _ a) =>
        [ | aSol aSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega.
        * { destruct aSol as [ (*V A1 A2 aGenAtom*)
                            _ _ _ [ V _V' A1 A2 aGen _v  (* (_v o>| #1| aGen)%sol *)
                                     | V A2 A1 a_GenAtom A1' W WV wv a'GenAtom
                                         (* (wv o>| a_GenAtom o>Mod a'GenAtom)%sol *)
                                     ]
                             | V A _v (* (_v o>| @uMod A)%sol *)
                             | A A' W W' _v aSol   (* (_v o>| 'D1| aSol)%sol *)
                             | V _V' A1 A2 _v aSol  (* (_v o>| 'clfy o>Mod aSol)%sol *)
                             | V _V' A1 A2 _v aSol  (* (_v o>| aSol o>Mod 'declfy)%sol *) ].

            (* a to v o>' (_v o>| #1| aGen)%sol *)
            - exists ( (v o> _v) o>| #1| aGen )%sol.
              clear -aSol_prop. tac_reduce.
                
            (* a to v o>' (wv o>| a_GenAtom o>Mod a'GenAtom)%sol *)
            - exists ( (v o> wv) o>| a_GenAtom o>Mod a'GenAtom )%sol .
              clear -aSol_prop. tac_reduce.
              (* clear -aSol_prop.
              simpl in *; abstract (
                  intuition (eauto; try subst; rewriterMod; try congruence; try (transitivity
                  ((v o>' wv) o>| (Sol.toMod_gen a_GenAtom) o>Mod (Sol.toMod_gen a'GenAtom));
                  eauto); eauto 12)). *)
                
            (* a to v o>' (_v o>| @uMod A)%sol *)
            - exists ( (v o> _v) o>| uMod )%sol.
              clear -aSol_prop. tac_reduce.

            (* a to v o>' (_v o>| 'D1| aSol)%sol *)
            - exists ( (v o> _v) o>| 'D1| aSol )%sol.
              clear -aSol_prop. tac_reduce.

            (* a to v o>' (_v o>| 'clfy o>Mod aSol)%sol *)
            - exists ( (v o> _v) o>| 'clfy o>Mod aSol )%sol.
              clear -aSol_prop. tac_reduce.

            (* a to v o>' (_v o>| aSol o>Mod 'declfy)%sol *)
            - exists ( (v o> _v) o>| aSol o>Mod 'declfy )%sol.
              clear -aSol_prop. tac_reduce.
              (* move : aSol_prop; clear;
                case => aSol_prop;
                         first by left; transitivity (v o>' (Sol.toMod ( _v o>| aSol o>Mod 'declfy )%sol));
                           [ apply: Red.DeClassifying_arrowLog |
                             apply: Red.PolyV_Mod_cong; [apply: ReflV | ] ].
                by left; rewrite -aSol_prop; apply: Red.DeClassifying_arrowLog. *)
          }

      (* a is v o>| #1| aGen *)
      + move => H_gradeTotal. exists (v o>| #1| aGen)%sol. right. reflexivity.

      (* a is v o>| @uMod A *)
      + move => H_gradeTotal. exists (v o>| uMod)%sol. right. reflexivity.

      (* a is wv o>| a_ o>Mod a' *)
      + rewrite -/(wv o>| a_ o>Mod a') => H_gradeTotal. all: cycle 1. 

      (* a is v o>| 'D1| a *)
      + move => H_gradeTotal.
        case : (solveMod len _ _ _ a) =>
        [ | aSol aSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega.
        * exists (v o>| 'D1| aSol)%sol.
          clear -aSol_prop. tac_reduce.

      (* a is wv o>| b o>D a *)
      + rewrite -/(wv o>| b o>D a) => H_gradeTotal. all: cycle 1. 

      (* a is v o>| 'clfy o>Mod a *)
      + move => H_gradeTotal.
        case : (solveMod len _ _ _ a) =>
        [ | aSol aSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega.
        * exists (v o>| 'clfy o>Mod aSol)%sol.
          clear -aSol_prop. tac_reduce.

      (* a is v o>| a o>Mod 'declfy *)
      + move => H_gradeTotal.
        case : (solveMod len _ _ _ a) =>
        [ | aSol aSol_prop ].
        * move : H_gradeTotal; clear; rewrite /gradeTotal /=; move => *; abstract Omega.omega.
        * exists (v o>| aSol o>Mod 'declfy)%sol.
          clear -aSol_prop. tac_reduce.
          (* move : aSol_prop; clear;
            case => aSol_prop;
                     first by left; apply: Red.DeClassifying_cong; [apply: ReflV |].
            by right; rewrite -aSol_prop. *)

      (* a is (wv o>| a_ o>Mod a') *)
      + case : (solveMod len _ _ _ a_) =>
        [ | a_Sol a_Sol_prop ];
          [ move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega | ].
        case : (solveMod len _ _ _ a') =>
        [ | a'Sol a'Sol_prop ];
          [ move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega | ].

        (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol) *)
        destruct a_Sol as
            [ V A1 A2 a_GenAtom  (* a_GenAtom : ('Mod(0 _ |- [0 _ ~> _ ]0 )0 %sol) *)
            | V A v  (* (v o>| @uMod A)%sol *)
            | A A' _W W' v a_Sol'   (* (v o>| 'D1| aSol)%sol *)
            | V V' A1 A2 v a_Sol'  (* (v o>| 'clfy o>Mod aSol)%sol *)
            | V V' A1 A2 v a_Sol'  (* (v o>| aSol o>Mod 'declfy)%sol *) ].

        (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (a_GenAtom) o>Mod a'Sol) *)
        * { clear - solveMod H_gradeTotal a_Sol_prop a'Sol_prop.
            move: (Sol.Destruct_domGen.Mod00_domGenP a'Sol) => a'Sol_domGenP.
            destruct a'Sol_domGenP as
                [ _V _A1 A2 a'GenAtom  (* a'GenAtom : ('Mod(0 _ |- [0 _ ~> _ ]0 )0 %sol) *)
                | _V A v  (* (v o>| @uMod A)%sol *)
                | _V V' _A1 A2 v a'Sol'  (* (v o>| a'Sol o>Mod 'declfy)%sol *) ].

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (a_GenAtom) o>Mod a'Sol) , is  (wv o>| (a_GenAtom) o>Mod a'GenAtom)  *)
            - exists (wv o>| a_GenAtom o>Mod a'GenAtom)%sol.
              clear -a_Sol_prop a'Sol_prop. tac_reduce.
                (* intuition (simpl; eauto; try subst; try congruence;
                    try transitivity (wv o>| (Sol.toMod a_GenAtom) o>Mod a');
                    simpl; eauto 12). *)

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (a_GenAtom) o>Mod a'Sol) , is  (wv o>| (a_GenAtom) o>Mod (v o>| uMod))  *)
            - destruct a_GenAtom as
                  [ V V' A1 A2 a_Gen _v  (* (_v o>| #1| a_Gen)%sol *)
                  | V A2 A1 a_GenAtom_ A1' W _WV _v a_GenAtom'  (* (_v o>| a_GenAtom_ o>Mod a'GenAtom')%sol *) ].

              (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (a_GenAtom) o>Mod a'Sol) , is  (wv o>| (_v o>| #1| a_Gen) o>Mod (v o>| uMod))  *)
              + exists ( ( ( (wv o> log.-(1 v & _ )0 o> desIdenObLK) o> _v )
                        o>| #1| a_Gen)%sol ) .
                clear -a_Sol_prop a'Sol_prop. tac_reduce.
                (* intuition (simpl; eauto; try subst; try congruence;
                           try transitivity (wv o>| (Sol.toMod (p o>| #1| m)%sol) o>Mod a');
                           try intuition (simpl; eauto; transitivity (wv o>| (Sol.toMod (p o>| #1| m)%sol) o>Mod Sol.toMod (_v o>| uMod)%sol); simpl; eauto );
                           simpl; eauto 12). *)
                
              (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (a_GenAtom) o>Mod a'Sol) , is  (wv o>| (_v o>| a_GenAtom_ o>Mod a_GenAtom') o>Mod (v o>| uMod))  *)
              + exists ( ( ( (wv o> log.-(1 v & _ )0 o> desIdenObLK) o> _v )
                        o>| a_GenAtom_ o>Mod a_GenAtom')%sol ) .
                clear -a_Sol_prop a'Sol_prop. tac_reduce.
                (* intuition (simpl; eauto; try subst; try congruence;
                           try transitivity (wv o>| (Sol.toMod (p o>| #1| m)%sol) o>Mod a');
                           try intuition (simpl; eauto; transitivity (wv o>| (Sol.toMod (p o>| a_GenAtom1 o>Mod a_GenAtom2)%sol) o>Mod Sol.toMod (_v o>| uMod)%sol); simpl; eauto );
                           simpl; eauto 12). *)

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (a_GenAtom) o>Mod a'Sol) , is  (wv o>| (a_GenAtom) o>Mod ((v o>| a'Sol' o>Mod 'declfy))  *)
            - case : (solveMod len _ _ _ ((wv o> log.-(1 v & _ )0)
                        o>| (Sol.toMod a_GenAtom) o>Mod (Sol.toMod a'Sol'))) =>
              [ | a_o_a'Sol a_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists ( (log.-1) o>| a_o_a'Sol o>Mod 'declfy )%sol .
                clear -a_Sol_prop a'Sol_prop a_o_a'Sol_prop. tac_reduce.
          }

        (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| uMod ) o>Mod a'Sol) *)
        * { case : (solveMod len _ _ _ ((wv o> log.-(0 _ & v)1 o> desIdenObRK)
                                          o>' (Sol.toMod a'Sol))) =>
            [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
            - tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
            - exists (a_Sol_o_a'Sol).
              clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.
              (* clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop;
              simpl in *;
                intuition (eauto; try subst; rewriter; try congruence; try (transitivity
                ((wv o> log.-(0 _ & v)1 o> desIdenObRK) o>' (Sol.toMod a'Sol));
                eauto); eauto 12). *)
          }
          
        (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod a'Sol) *)
        * { move: (Sol.Destruct_domDeClass.Mod00_domDeClassP a'Sol) => a'Sol_domDeClassP.
            destruct a'Sol_domDeClassP as
                [ V _A _v  (* _v o>| @uMod _A %sol *)
                | _A A' W _W' _v a'Sol' (* _v o>| 'D1| a'Sol' %sol *)
                | V V' A1 A2 _v a'Sol' (* _v o>| 'clfy o>Mod a'Sol' %sol *)
                | V V' A1 A2 _v a'Sol' (* _v o>| a'Sol' o>Mod 'declfy %sol *) ].

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod (_v o>| @uMod _A)) *)
            - case : (solveMod len _ _ _ ((wv o> log.-(1 _v & _ )0 o> desIdenObLK)
                                          o>' (Sol.toMod (v o>| 'D1| a_Sol')%sol))) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod (_v o>| 'D1| a'Sol')) *)
            - case : (solveMod len _ _ _ (wv o>| (Sol.toMod (v o>| 'D1| a_Sol')%sol)
                                  o>D ((_v o>desIdenObRK) o>' (Sol.toMod a'Sol')))) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod (_v o>| 'clfy o>Mod a'Sol')) *)
            - case : (solveMod len _ _ _
              ((log.-1) o>| 'clfy o>Mod (wv o>| ((v o> desIdenObRK) o>' (Sol.toMod a_Sol'))
                                            o>Mod (_v o>' (Sol.toMod a'Sol'))))) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod a'Sol)  , is (wv o>| (v o>| 'D1| a_Sol') o>Mod (_v o>| a'Sol' o>Mod 'declfy)) *)
            - case : (solveMod len _ _ _
              ((log.-1) o>| ((wv o> (1 _v & _ )0) o>| (Sol.toMod (v o>| 'D1| a_Sol')%sol)
                                                  o>Mod (Sol.toMod a'Sol')) o>Mod 'declfy)) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.
          }
          
        (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| 'clfy o>Mod a_Sol') o>Mod a'Sol) *)
        * { case : (solveMod len _ _ _
                 ((log.-1) o>| 'clfy o>Mod ((wv o> (0 _ & v )1) o>| (Sol.toMod a_Sol')
                                                      o>Mod (Sol.toMod a'Sol)))) =>
            [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
            - tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
            - exists (a_Sol_o_a'Sol).
              clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.
          }
          
        (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| a_Sol' o>Mod 'declfy) o>Mod a'Sol) *)
        * { move: (Sol.Destruct_dom2DeClass.Mod00_dom2DeClassP a'Sol) => a'Sol_dom2DeClassP.
            destruct a'Sol_dom2DeClassP as
                [ _V A _v  (* _v o>| @uMod A %sol *)
                | A A' W W' _v a'Sol' (* _v o>| 'D1| a'Sol' %sol *)
                | _V _V' _A1 A2 _v a'Sol' (* _v o>| 'clfy o>Mod a'Sol' %sol *)
                | _V _V' _A1 A2 _v a'Sol' (* _v o>| a'Sol' o>Mod 'declfy %sol *) ].

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| a_Sol' o>Mod 'declfy) o>Mod (_v o>| @uMod A)) *)
            - case : (solveMod len _ _ _
                               ((wv o> log.-(1 _v & _ )0 o> desIdenObLK)
                                  o>' (v o>| (Sol.toMod a_Sol') o>Mod 'declfy))) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| a_Sol' o>Mod 'declfy) o>Mod (_v o>| 'D1| a'Sol')) *)
            - case : (solveMod len _ _ _
                              (wv o>| (Sol.toMod (v o>| a_Sol' o>Mod 'declfy)%sol)
                                  o>D ((_v o> desIdenObRK) o>' (Sol.toMod a'Sol')))) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.

            (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| a_Sol' o>Mod 'declfy) o>Mod (_v o>| 'clfy o>Mod a'Sol')) *)
            - case : (solveMod len _ _ _
                               (wv o>| (v o>' (Sol.toMod a_Sol'))
                                   o>Mod (_v o>' (Sol.toMod a'Sol')))) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.

              (* a is (wv o>| a_ o>Mod a') , to (wv o>| a_Sol o>Mod a'Sol)  , is (wv o>| (v o>| a_Sol' o>Mod 'declfy) o>Mod (_v o>| a'Sol' o>Mod 'declfy)) *)
            - case : (solveMod len _ _ _
                     ((log.-1) o>| ((wv o> (1 _v & _ )0)
                                      o>| (Sol.toMod (v o>| a_Sol' o>Mod 'declfy)%sol)
                                      o>Mod (Sol.toMod a'Sol')) o>Mod 'declfy)) =>
              [ | a_Sol_o_a'Sol a_Sol_o_a'Sol_prop ].
              + tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop.
              + exists (a_Sol_o_a'Sol).
                clear -a_Sol_prop a'Sol_prop a_Sol_o_a'Sol_prop. tac_reduce.
          }

      (* a is (wv o>| b o>D a) *)
      + case : (solveMod len _ _ _ b) =>
        [ | bSol bSol_prop ];
          [ move : H_gradeTotal; clear; rewrite /gradeTotal /=; move => *; Omega.omega | ].
        case : (solveMod len _ _ _ a) =>
        [ | aSol aSol_prop ];
          [ move : H_gradeTotal; clear; rewrite /gradeTotal /=; move => *; Omega.omega | ].
        move: (Sol.Destruct_codomDeClass.Mod00_codomDeClassP bSol) => bSol_codomDeClassP.
        destruct bSol_codomDeClassP as
            [ V A v  (* v o>| @uMod A %sol *)
            | A _A' _W W' v bSol' (* v o>| 'D1| bSol' %sol *)
            | V V' A1 A2 v bSol' (* v o>| 'clfy o>Mod bSol' %sol *)
            | V V' A1 A2 v bSol' (* v o>| bSol' o>Mod 'declfy %sol *) ].

        (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| @uMod A) o>D aSol) *)
        * { case : (solveMod len _ _ _
                     ((wv o> log.-(0 _ & v )1) o>| 'D1| (Sol.toMod aSol))) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              - tac_degrade H_gradeTotal bSol_prop aSol_prop.
              - exists (bSol_oD_aSol).
                clear -bSol_prop aSol_prop bSol_oD_aSol_prop. tac_reduce.
          }
          
        (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| 'D1| bSol') o>D aSol) *)
        * { case : (solveMod len _ _ _
                   ((wv o> desIdenObRKV) o>| 'D1| ((log.-1) o>|
                                     ((v o> desIdenObRK) o>' (Sol.toMod bSol'))
                                     o>Mod (Sol.toMod aSol)))) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              - tac_degrade H_gradeTotal bSol_prop aSol_prop.
              - exists (bSol_oD_aSol).
                clear -bSol_prop aSol_prop bSol_oD_aSol_prop. tac_reduce.
          }

        (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| 'clfy o>Mod bSol') o>D aSol) *)
        * { case : (solveMod len _ _ _
              ((log.-1) o>| 'clfy o>Mod ((wv o> (0 _ & v )1) o>| (Sol.toMod bSol')
                                                             o>D (Sol.toMod aSol)))) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              - tac_degrade H_gradeTotal bSol_prop aSol_prop.
              - exists (bSol_oD_aSol).
                clear -bSol_prop aSol_prop bSol_oD_aSol_prop. tac_reduce.
          }

        (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D aSol) *)
        * { move: (Sol.Destruct_iterDeClassifying.prefixP aSol) => aSol_prefixP.
            destruct aSol_prefixP as
                [ _V A _v  (* _v o>| @uMod A %sol *)
                | A A' W W' _v aSol'  (* _v o>| 'D1| aSol' %sol *)
                | _V _V' _A1 A2 _v aSol'  (* _v o>| 'clfy o>Mod aSol' %sol *)
                | _ _ _ _
                    [ V_dft A Vs vs vaSol'  (* vs o>|| (vaSol' o>| @uMod A) ''declfy %sol *)
                    | V_dft A A' Vs vs Va vaSol' aSol'  (* vs o>|| (vaSol' o>| 'D1| aSol') ''declfy %sol *)
                    | V_dft _A1 A2 Vs vs Va vaSol' aSol'  (* vs o>|| (vaSol' o>| 'clfy o>Mod aSol') ''declfy %sol *) ] ].
                 
            (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D (_v o>| @uMod A)) *)
            - case : (solveMod len _ _ _
                               ((wv o> log.-(1 _v & _ )0 o> desIdenObLK)
                                  o>' (v o>| (Sol.toMod bSol') o>Mod 'declfy))) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              + tac_degrade H_gradeTotal bSol_prop aSol_prop.
              + exists (bSol_oD_aSol).
                clear -bSol_prop aSol_prop bSol_oD_aSol_prop. tac_reduce.
                
            (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D (_v o>| 'D1| aSol')) *)
            - case : (solveMod len _ _ _
                      ((log.-1) o>| (wv o>| (v o>' (Sol.toMod bSol'))
                                      o>D ((_v o> desIdenObRK) o>' (Sol.toMod aSol')))
                                o>Mod 'declfy)) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              + tac_degrade H_gradeTotal bSol_prop aSol_prop.
              + exists (bSol_oD_aSol).
                clear -bSol_prop aSol_prop bSol_oD_aSol_prop. tac_reduce.

            (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D (_v o>| 'clfy o>Mod aSol')) *)
            - case : (solveMod len _ _ _
                      (wv o>| (v o>' (Sol.toMod bSol')) o>D (_v o>' (Sol.toMod aSol')))) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              + tac_degrade H_gradeTotal bSol_prop aSol_prop.
              + exists (bSol_oD_aSol).
                clear -bSol_prop aSol_prop bSol_oD_aSol_prop. tac_reduce.

            (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D (vs o>|| (vaSol' o>| uMod) o>Mod ''declfy)) *)
            - case : (solveMod len _ _ _
                      (wv
                         o>| (hmap (fun U1U2 u => ((1 u & _ )0)) vs
                              o>|| ((log.-(1 vaSol' & _ )0 o> (0 log.-I & v )1 o> desIdenObLK) o>' (Sol.toMod bSol'))
                              o>Mod ''declfy) o>Mod 'declfy)) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              + tac_degrade H_gradeTotal bSol_prop aSol_prop.

              + exists (bSol_oD_aSol).
                move: bSol_prop aSol_prop bSol_oD_aSol_prop ; clear.
                simpl; repeat rewrite Sol.toMod_iterDeClassifyingSol /= . tac_reduce.

            - case : (solveMod len _ _ _
                      (wv o>| (hmap (fun U1U2 u => ((1 u & _)0)) vs
                                    o>|| ((log.-(1 vaSol' o> desIdenObRK & _ )0 o> (0 _ & v )1) o>| (Sol.toMod bSol') o>D (Sol.toMod aSol'))
                                    o>Mod ''declfy) o>Mod 'declfy)) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              + tac_degrade H_gradeTotal bSol_prop aSol_prop.
              + exists (bSol_oD_aSol).
                move: bSol_prop aSol_prop bSol_oD_aSol_prop ; clear.
                simpl; repeat rewrite Sol.toMod_iterDeClassifyingSol /= . tac_reduce.

            (* a is (wv o>| b o>D a) , to (wv o>| bSol o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D aSol)  , is (wv o>| (v o>| bSol' o>Mod 'declfy) o>D (vs o>|| (vaSol' o>| 'clfy o>Mod aSol') o>Mod ''declfy)) *)
            - case : (solveMod len _ _ _
                  (wv o>| (v o>' (Sol.toMod bSol'))
                      o>D (vs o>|| ( vaSol' o>' (Sol.toMod aSol')) o>Mod ''declfy))) =>
              [ | bSol_oD_aSol bSol_oD_aSol_prop ].
              + tac_degrade H_gradeTotal bSol_prop aSol_prop.
              + exists (bSol_oD_aSol).
                move: bSol_prop aSol_prop bSol_oD_aSol_prop ; clear.
                simpl; repeat rewrite Sol.toMod_iterDeClassifyingSol /= . tac_reduce.
          }

  Defined.

  End Section1.

End COPARAM.

(**#+END_SRC

Voila. **)
