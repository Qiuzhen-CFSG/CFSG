module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.Certificate

/-!
# Checked actor recovery in binary derived Bruhat cells 9 through 11

The words in `source/bru_hat_witnesses.json` use C(1)E(1)F(1), E(1), and
F(1)^a w_i F(1)^b. Each intermediate matrix is checked on all eight basis
vectors by the kernel. The actual word therefore recovers each cubic actor.

Root matrices: Gerald Höhn and the ATLAS contributors, ATLAS Research and
Attribution License 1.0 (LICENSES/ATLAS.txt). Source application: the G₂(2)′
branch on Aschbacher–Smith, printed pp.1144–1145.
-/

public section
namespace Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
open Atlas.G2.Explicit Atlas.SplitOctonion BinaryCore Certificate

private theorem recover_9_0_0_0 : word (representative 9 0 0) [0, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 4665804584541527399 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 11342109557141553344) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 2).val (column 11342109557141553344 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 11383449706502856666) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 11383449706502856666 c) r =
          column 11342109557141553344 c r) c)
    refine Check.cons (b := 11518557695323971066) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 2).val (column 11518557695323971066 c) r =
          column 11383449706502856666 c r) c)
    refine Check.cons (b := 11476853365881423033) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 11476853365881423033 c) r =
          column 11518557695323971066 c r) c)
    refine Check.cons (b := 11476786295672102841) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 1).val (column 11476786295672102841 c) r =
          column 11476853365881423033 c r) c)
    refine Check.cons (b := 11518792990805933315) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 11518792990805933315 c) r =
          column 11476786295672102841 c r) c)
    refine Check.cons (b := 11518557695317574147) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 1).val (column 11518557695317574147 c) r =
          column 11518792990805933315 c r) c)
    refine Check.cons (b := 144998311370137562) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 2).val (column 144998311370137562 c) r =
          column 11518557695317574147 c r) c)
    refine Check.cons (b := 144431916278644800) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 144431916278644800 c) r =
          column 144998311370137562 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 2).val (column 9241421688590303745 c) r =
          column 144431916278644800 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_9_0_0_1 : word (representative 9 0 0) [2, 1, 0, 1, 0, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 432732661174403104) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 2).val (column 432732661174403104 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 432733760686031392) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 1).val (column 432733760686031392 c) r =
          column 432732661174403104 c r) c)
    refine Check.cons (b := 434421950840561886) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 434421950840561886 c) r =
          column 432733760686031392 c r) c)
    refine Check.cons (b := 434429647421938654) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 1).val (column 434429647421938654 c) r =
          column 434421950840561886 c r) c)
    refine Check.cons (b := 432732661174534208) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 0).val (column 432732661174534208 c) r =
          column 434429647421938654 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 2).val (column 9241492057334482433 c) r =
          column 432732661174534208 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 0 0) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_9_1_1_0 : word (representative 9 1 1) [0, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 4665804584541527399 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 11342109557141553344) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 2).val (column 11342109557141553344 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 11383449706502856666) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 11383449706502856666 c) r =
          column 11342109557141553344 c r) c)
    refine Check.cons (b := 11518557695323971066) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 2).val (column 11518557695323971066 c) r =
          column 11383449706502856666 c r) c)
    refine Check.cons (b := 11476853365881423033) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 11476853365881423033 c) r =
          column 11518557695323971066 c r) c)
    refine Check.cons (b := 11476786295672102841) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 1).val (column 11476786295672102841 c) r =
          column 11476853365881423033 c r) c)
    refine Check.cons (b := 11518792990805933315) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 11518792990805933315 c) r =
          column 11476786295672102841 c r) c)
    refine Check.cons (b := 11518557695317574147) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 1).val (column 11518557695317574147 c) r =
          column 11518792990805933315 c r) c)
    refine Check.cons (b := 144998311370137562) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 2).val (column 144998311370137562 c) r =
          column 11518557695317574147 c r) c)
    refine Check.cons (b := 144431916278644800) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 144431916278644800 c) r =
          column 144998311370137562 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 2).val (column 9241421688590303745 c) r =
          column 144431916278644800 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_9_1_1_1 : word (representative 9 1 1) [2, 1, 0, 1, 0, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 432732661174403104) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 2).val (column 432732661174403104 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 432733760686031392) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 1).val (column 432733760686031392 c) r =
          column 432732661174403104 c r) c)
    refine Check.cons (b := 434421950840561886) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 434421950840561886 c) r =
          column 432733760686031392 c r) c)
    refine Check.cons (b := 434429647421938654) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 1).val (column 434429647421938654 c) r =
          column 434421950840561886 c r) c)
    refine Check.cons (b := 432732661174534208) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 0).val (column 432732661174534208 c) r =
          column 434429647421938654 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 2).val (column 9241492057334482433 c) r =
          column 432732661174534208 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 9 1 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_10_1_0_0 : word (representative 10 1 0) [2, 0, 1, 2, 2, 0, 1, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 153123555704308800) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 153123555704308800 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 153721840942556671) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 0).val (column 153721840942556671 c) r =
          column 153123555704308800 c r) c)
    refine Check.cons (b := 153688855593696511) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 1).val (column 153688855593696511 c) r =
          column 153721840942556671 c r) c)
    refine Check.cons (b := 14087888727672095490) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 14087888727672095490 c) r =
          column 153688855593696511 c r) c)
    refine Check.cons (b := 73186844359081155) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 73186844359081155 c) r =
          column 14087888727672095490 c r) c)
    refine Check.cons (b := 73472708760468128) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 0).val (column 73472708760468128 c) r =
          column 73186844359081155 c r) c)
    refine Check.cons (b := 73467211202306208) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 1).val (column 73467211202306208 c) r =
          column 73472708760468128 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 9241421688590303745 c) r =
          column 73467211202306208 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_10_1_0_1 : word (representative 10 1 0) [2, 2, 2, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 538750151060119680) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 538750151060119680 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 16194487371846977031) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 16194487371846977031 c) r =
          column 538750151060119680 c r) c)
    refine Check.cons (b := 73471626496073952) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 73471626496073952 c) r =
          column 16194487371846977031 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 2).val (column 9241492057334482433 c) r =
          column 73471626496073952 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 1 0) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_10_0_1_0 : word (representative 10 0 1) [1, 2, 0, 0, 0, 0, 0, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4665944770113977603) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 1).val (column 4665944770113977603 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 233972952786650244) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 2).val (column 233972952786650244 c) r =
          column 4665944770113977603 c r) c)
    refine Check.cons (b := 233063652356268988) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 0).val (column 233063652356268988 c) r =
          column 233972952786650244 c r) c)
    refine Check.cons (b := 233973965794237818) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 0).val (column 233973965794237818 c) r =
          column 233063652356268988 c r) c)
    refine Check.cons (b := 233062479280473703) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 0).val (column 233062479280473703 c) r =
          column 233973965794237818 c r) c)
    refine Check.cons (b := 233972952786651067) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 0).val (column 233972952786651067 c) r =
          column 233062479280473703 c r) c)
    refine Check.cons (b := 233063652356268160) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 0).val (column 233063652356268160 c) r =
          column 233972952786651067 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 2).val (column 9241421688590303745 c) r =
          column 233063652356268160 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_10_0_1_1 : word (representative 10 0 1) [2, 2, 2, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 72908676540555488) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 2).val (column 72908676540555488 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 16203494571101586951) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 2).val (column 16203494571101586951 c) r =
          column 72908676540555488 c r) c)
    refine Check.cons (b := 539313101015638144) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 2).val (column 539313101015638144 c) r =
          column 16203494571101586951 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 2).val (column 9241492057334482433 c) r =
          column 539313101015638144 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 10 0 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_11_1_0_0 : word (representative 11 1 0) [2, 2, 2, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 144431916278644800) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 2).val (column 144431916278644800 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 13871152995604890370) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 2).val (column 13871152995604890370 c) r =
          column 144431916278644800 c r) c)
    refine Check.cons (b := 72906468893671616) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 2).val (column 72906468893671616 c) r =
          column 13871152995604890370 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 2).val (column 9241421688590303745 c) r =
          column 72906468893671616 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_11_1_0_1 : word (representative 11 1 0) [0, 2, 0, 2, 1, 0, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 9268479298589312221) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 0).val (column 9268479298589312221 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 11043990156150317184) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 2).val (column 11043990156150317184 c) r =
          column 9268479298589312221 c r) c)
    refine Check.cons (b := 11087130520813438471) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 0).val (column 11087130520813438471 c) r =
          column 11043990156150317184 c r) c)
    refine Check.cons (b := 73750880891323545) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 2).val (column 73750880891323545 c) r =
          column 11087130520813438471 c r) c)
    refine Check.cons (b := 73748681868059289) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 1).val (column 73748681868059289 c) r =
          column 73750880891323545 c r) c)
    refine Check.cons (b := 74032368804708544) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 0).val (column 74032368804708544 c) r =
          column 73748681868059289 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 2).val (column 9241492057334482433 c) r =
          column 74032368804708544 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 1 0) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_11_0_1_0 : word (representative 11 0 1) [2, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 216801875371016320) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 2).val (column 216801875371016320 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 2).val (column 9241421688590303745 c) r =
          column 216801875371016320 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_11_0_1_1 : word (representative 11 0 1) [2, 0, 2, 2, 0, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 74030161157824672) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 2).val (column 74030161157824672 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 73752001961287654) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 0).val (column 73752001961287654 c) r =
          column 74030161157824672 c r) c)
    refine Check.cons (b := 16625425561190991367) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 2).val (column 16625425561190991367 c) r =
          column 73752001961287654 c r) c)
    refine Check.cons (b := 504822153984981343) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 2).val (column 504822153984981343 c) r =
          column 16625425561190991367 c r) c)
    refine Check.cons (b := 506228796129591424) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 0).val (column 506228796129591424 c) r =
          column 504822153984981343 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 2).val (column 9241492057334482433 c) r =
          column 506228796129591424 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 11 0 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

/-- Cell 9 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_9 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 9 a b) (hg : representative 9 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · constructor
    · rw [← recover_9_0_0_0]
      exact word_mem K hP hg _
    · rw [← recover_9_0_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 9 0 1) hab)
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 9 1 0) hab)
  · constructor
    · rw [← recover_9_1_1_0]
      exact word_mem K hP hg _
    · rw [← recover_9_1_1_1]
      exact word_mem K hP hg _

/-- Cell 10 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_10 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 10 a b) (hg : representative 10 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 10 0 0) hab)
  · constructor
    · rw [← recover_10_0_1_0]
      exact word_mem K hP hg _
    · rw [← recover_10_0_1_1]
      exact word_mem K hP hg _
  · constructor
    · rw [← recover_10_1_0_0]
      exact word_mem K hP hg _
    · rw [← recover_10_1_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 10 1 1) hab)

/-- Cell 11 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_11 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 11 a b) (hg : representative 11 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 11 0 0) hab)
  · constructor
    · rw [← recover_11_0_1_0]
      exact word_mem K hP hg _
    · rw [← recover_11_0_1_1]
      exact word_mem K hP hg _
  · constructor
    · rw [← recover_11_1_0_0]
      exact word_mem K hP hg _
    · rw [← recover_11_1_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 11 1 1) hab)

end Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
