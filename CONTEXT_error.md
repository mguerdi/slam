Reproduction of CONTEXT exception that only appears when running with mirabelle.

```
theory misc

imports "JEHA_TEST_BASE.test_base"

begin

declare [[jeha_trace]]
declare [[metis_trace]]

(* This line is critical to the reproduction *)
declare [[jeha_proof_reconstruction]]

lemma
  shows "(1 :: nat) + 1 = 2"
  using Num.nat_1_add_1 by jeha (* 51 ms *)
```

running mirabelle via

```
> ~/Isabelle2023/bin/isabelle mirabelle -d ~/git/jeha -d ~/git/jeha/tests -O ~/mirabelle_output -A jeha -m 10000000 -s 0 -t 60 -T misc JEHA_TEST_GENERAL
```

results in

```
> cat ~/mirabelle_output/mirabelle.log
0.jeha goal.by           16ms JEHA_TEST_GENERAL.misc 75:1669  exception: CONTEXT ("No content for theory certificate misc:44", [], [], ["\<lbrakk>PROP ?V; PROP ?V \<Longrightarrow> PROP ?W\<rbrakk> \<Longrightarrow> PROP ?W", "??.HOL.Trueprop (??.HOL.eq (??.Groups.plus_class.plus ??.Groups.one_class.one ??.Groups.one_class.one) (??.Num.numeral_class.numeral (??.Num.num.Bit0 ??.Num.num.One)))"], NONE)
0.jeha goal.using        27ms JEHA_TEST_GENERAL.misc 75:1647  failed:
0.jeha goal.using        27ms JEHA_TEST_GENERAL.misc 75:1647  Pure.protectI
```

Search:

Two possible places where this exception could have been raised:
```
juba ~/Isabelle2023 % rg "raise CONTEXT.*msg[^\[]*\[\][^\[]*\[\]" 
src/Pure/thm.ML
...
697:        handle ERROR msg => raise CONTEXT (msg, [], [], ths, NONE))
...
2193:            raise CONTEXT (msg, [], [], [state, orule], Option.map Context.Proof opt_ctxt);
```

Underlying error in both cases:
```
juba ~/Isabelle2023 % rg "No content for theory certificate"
src/Pure/context.ML
626:      error ("No content for theory certificate " ^ display_name thy_id);
```

