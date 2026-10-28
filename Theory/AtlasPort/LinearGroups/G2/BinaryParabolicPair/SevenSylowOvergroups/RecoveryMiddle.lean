module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.Certificate

/-!
# Checked actor recovery in binary derived Bruhat cells 6 through 8

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

private theorem recover_6_0_0_0 : word (representative 6 0 0) [0, 0, 2, 0, 0, 2, 0] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 4665804584541527399 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 18212670746566630724) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 2).val (column 18212670746566630724 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 18175586741497330394) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 18175586741497330394 c) r =
          column 18212670746566630724 c r) c)
    refine Check.cons (b := 18212728076129853152) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 18212728076129853152 c) r =
          column 18175586741497330394 c r) c)
    refine Check.cons (b := 9277662281737232027) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 2).val (column 9277662281737232027 c) r =
          column 18212728076129853152 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 9241421688590303745 c) r =
          column 9277662281737232027 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_6_0_0_1 : word (representative 6 0 0) [2, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 2, 0, 2] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 153123555704309344) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 2).val (column 153123555704309344 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 153721840942557149) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 153721840942557149 c) r =
          column 153123555704309344 c r) c)
    refine Check.cons (b := 153125901328989690) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 153125901328989690 c) r =
          column 153721840942557149 c r) c)
    refine Check.cons (b := 153723901992222302) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 153723901992222302 c) r =
          column 153125901328989690 c r) c)
    refine Check.cons (b := 13484443670182805027) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 2).val (column 13484443670182805027 c) r =
          column 153723901992222302 c r) c)
    refine Check.cons (b := 13517973009931223104) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 13517973009931223104 c) r =
          column 13484443670182805027 c r) c)
    refine Check.cons (b := 13484592617620529538) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 13484592617620529538 c) r =
          column 13517973009931223104 c r) c)
    refine Check.cons (b := 13518055619912631975) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 13518055619912631975 c) r =
          column 13484592617620529538 c r) c)
    refine Check.cons (b := 13517940171191704487) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 1).val (column 13517940171191704487 c) r =
          column 13518055619912631975 c r) c)
    refine Check.cons (b := 15967978632827853662) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 2).val (column 15967978632827853662 c) r =
          column 13517940171191704487 c r) c)
    refine Check.cons (b := 15943936840932056645) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 15943936840932056645 c) r =
          column 15967978632827853662 c r) c)
    refine Check.cons (b := 307446631297310270) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 2).val (column 307446631297310270 c) r =
          column 15943936840932056645 c r) c)
    refine Check.cons (b := 306245943034905120) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 0).val (column 306245943034905120 c) r =
          column 307446631297310270 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 0 0) 2).val (column 9241421688590303745 c) r =
          column 306245943034905120 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_6_1_1_0 : word (representative 6 1 1) [0, 0, 0, 2, 0, 0, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4665804584541527399 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 4647860261571585498) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4647860261571585498 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 4394457653265818977) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 2).val (column 4394457653265818977 c) r =
          column 4647860261571585498 c r) c)
    refine Check.cons (b := 4377713294450901252) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4377713294450901252 c) r =
          column 4394457653265818977 c r) c)
    refine Check.cons (b := 4394390854716555810) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4394390854716555810 c) r =
          column 4377713294450901252 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 2).val (column 9241421688590303745 c) r =
          column 4394390854716555810 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_6_1_1_1 : word (representative 6 1 1) [0, 2, 0, 0, 2, 1, 0, 1, 2, 0, 2, 0, 0, 2] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 9268479298589312221) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 9268479298589312221 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 2450689411462022148) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 2).val (column 2450689411462022148 c) r =
          column 9268479298589312221 c r) c)
    refine Check.cons (b := 2459136579587858144) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 2459136579587858144 c) r =
          column 2450689411462022148 c r) c)
    refine Check.cons (b := 2450726932833363263) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 2450726932833363263 c) r =
          column 2459136579587858144 c r) c)
    refine Check.cons (b := 11565483847216850270) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 2).val (column 11565483847216850270 c) r =
          column 2450726932833363263 c r) c)
    refine Check.cons (b := 11565343109728437598) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 1).val (column 11565343109728437598 c) r =
          column 11565483847216850270 c r) c)
    refine Check.cons (b := 11538462154321706969) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 11538462154321706969 c) r =
          column 11565343109728437598 c r) c)
    refine Check.cons (b := 11538497338693819865) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 1).val (column 11538497338693819865 c) r =
          column 11538462154321706969 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 2).val (column 4665804584541527399 c) r =
          column 11538497338693819865 c r) c)
    refine Check.cons (b := 4647860261571585498) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4647860261571585498 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 4394457653265818977) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 2).val (column 4394457653265818977 c) r =
          column 4647860261571585498 c r) c)
    refine Check.cons (b := 4377713294450901252) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4377713294450901252 c) r =
          column 4394457653265818977 c r) c)
    refine Check.cons (b := 4394390854716555810) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 0).val (column 4394390854716555810 c) r =
          column 4377713294450901252 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 6 1 1) 2).val (column 9241421688590303745 c) r =
          column 4394390854716555810 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_7_0_0_0 : word (representative 7 0 0) [0, 0, 1, 2, 2, 1, 0, 2, 0] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 4665804584541527399 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 4665874953285689703) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 1).val (column 4665874953285689703 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 7026855172085185728) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 2).val (column 7026855172085185728 c) r =
          column 4665874953285689703 c r) c)
    refine Check.cons (b := 18187717330176393348) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 2).val (column 18187717330176393348 c) r =
          column 7026855172085185728 c r) c)
    refine Check.cons (b := 18187689842385691012) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 1).val (column 18187689842385691012 c) r =
          column 18187717330176393348 c r) c)
    refine Check.cons (b := 18202354183927922912) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 18202354183927922912 c) r =
          column 18187689842385691012 c r) c)
    refine Check.cons (b := 9277662281737232027) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 2).val (column 9277662281737232027 c) r =
          column 18202354183927922912 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 9241421688590303745 c) r =
          column 9277662281737232027 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_7_0_0_1 : word (representative 7 0 0) [2, 0, 0, 0, 0, 2, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 459368330365501984) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 2).val (column 459368330365501984 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 461163177453413341) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 461163177453413341 c) r =
          column 459368330365501984 c r) c)
    refine Check.cons (b := 459375367239531966) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 459375367239531966 c) r =
          column 461163177453413341 c r) c)
    refine Check.cons (b := 461169360602397274) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 461169360602397274 c) r =
          column 459375367239531966 c r) c)
    refine Check.cons (b := 459368330365502528) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 0).val (column 459368330365502528 c) r =
          column 461169360602397274 c r) c)
    refine Check.cons (b := 288582288726720608) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 2).val (column 288582288726720608 c) r =
          column 459368330365502528 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 2).val (column 9241492057334482433 c) r =
          column 288582288726720608 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 0 0) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_7_1_1_0 : word (representative 7 1 1) [0, 1, 2, 2, 1, 0, 2, 1] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4647790168770664866) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 1).val (column 4647790168770664866 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 15680825506421505212) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 2).val (column 15680825506421505212 c) r =
          column 4647790168770664866 c r) c)
    refine Check.cons (b := 8937323143647805444) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 2).val (column 8937323143647805444 c) r =
          column 15680825506421505212 c r) c)
    refine Check.cons (b := 8937330840229200132) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 1).val (column 8937330840229200132 c) r =
          column 8937323143647805444 c r) c)
    refine Check.cons (b := 8969974947818406112) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 0).val (column 8969974947818406112 c) r =
          column 8937330840229200132 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 2).val (column 9241492057334482433 c) r =
          column 8969974947818406112 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_7_1_1_1 : word (representative 7 1 1) [2, 0, 0, 0, 0, 2, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 461064221407279834) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 2).val (column 461064221407279834 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 459473883481801792) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 0).val (column 459473883481801792 c) r =
          column 461064221407279834 c r) c)
    refine Check.cons (b := 461057210415908187) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 0).val (column 461057210415908187 c) r =
          column 459473883481801792 c r) c)
    refine Check.cons (b := 459480920355806174) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 0).val (column 459480920355806174 c) r =
          column 461057210415908187 c r) c)
    refine Check.cons (b := 461064221407280316) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 0).val (column 461064221407280316 c) r =
          column 459480920355806174 c r) c)
    refine Check.cons (b := 8969974947818406112) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 2).val (column 8969974947818406112 c) r =
          column 461064221407280316 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 2).val (column 9241492057334482433 c) r =
          column 8969974947818406112 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 7 1 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_8_0_0_0 : word (representative 8 0 0) [2, 1, 0, 2, 1, 2, 0, 1] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4324511225313574916) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 2).val (column 4324511225313574916 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4324514523848458500) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 1).val (column 4324514523848458500 c) r =
          column 4324511225313574916 c r) c)
    refine Check.cons (b := 4341400706739765408) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 0).val (column 4341400706739765408 c) r =
          column 4324514523848458500 c r) c)
    refine Check.cons (b := 15753661800467414208) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 2).val (column 15753661800467414208 c) r =
          column 4341400706739765408 c r) c)
    refine Check.cons (b := 15753767353583713472) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 1).val (column 15753767353583713472 c) r =
          column 15753661800467414208 c r) c)
    refine Check.cons (b := 9277592188940507807) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 2).val (column 9277592188940507807 c) r =
          column 15753767353583713472 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 0).val (column 9241492057334482433 c) r =
          column 9277592188940507807 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_8_0_0_1 : word (representative 8 0 0) [2, 2, 0, 0, 0, 0, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 144431916278775904) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 2).val (column 144431916278775904 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 459368330365501984) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 2).val (column 459368330365501984 c) r =
          column 144431916278775904 c r) c)
    refine Check.cons (b := 461163177453413341) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 0).val (column 461163177453413341 c) r =
          column 459368330365501984 c r) c)
    refine Check.cons (b := 459375367239531966) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 0).val (column 459375367239531966 c) r =
          column 461163177453413341 c r) c)
    refine Check.cons (b := 461169360602397274) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 0).val (column 461169360602397274 c) r =
          column 459375367239531966 c r) c)
    refine Check.cons (b := 459368330365502528) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 0).val (column 459368330365502528 c) r =
          column 461169360602397274 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 2).val (column 9241492057334482433 c) r =
          column 459368330365502528 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 0 0) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_8_1_1_0 : word (representative 8 1 1) [0, 1, 2, 1, 0, 2, 2, 1] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4647790168770664866) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 1).val (column 4647790168770664866 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 8937323143647805444) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 2).val (column 8937323143647805444 c) r =
          column 4647790168770664866 c r) c)
    refine Check.cons (b := 8937330840229200132) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 1).val (column 8937330840229200132 c) r =
          column 8937323143647805444 c r) c)
    refine Check.cons (b := 8969974947818406112) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 0).val (column 8969974947818406112 c) r =
          column 8937330840229200132 c r) c)
    refine Check.cons (b := 461064221407280316) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 2).val (column 461064221407280316 c) r =
          column 8969974947818406112 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 2).val (column 9241492057334482433 c) r =
          column 461064221407280316 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_8_1_1_1 : word (representative 8 1 1) [2, 2, 0, 0, 0, 0, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 8826387663297609952) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 2).val (column 8826387663297609952 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 461064221407279834) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 2).val (column 461064221407279834 c) r =
          column 8826387663297609952 c r) c)
    refine Check.cons (b := 459473883481801792) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 0).val (column 459473883481801792 c) r =
          column 461064221407279834 c r) c)
    refine Check.cons (b := 461057210415908187) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 0).val (column 461057210415908187 c) r =
          column 459473883481801792 c r) c)
    refine Check.cons (b := 459480920355806174) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 0).val (column 459480920355806174 c) r =
          column 461057210415908187 c r) c)
    refine Check.cons (b := 461064221407280316) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 0).val (column 461064221407280316 c) r =
          column 459480920355806174 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 2).val (column 9241492057334482433 c) r =
          column 461064221407280316 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 8 1 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

/-- Cell 6 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_6 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 6 a b) (hg : representative 6 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · constructor
    · rw [← recover_6_0_0_0]
      exact word_mem K hP hg _
    · rw [← recover_6_0_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 6 0 1) hab)
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 6 1 0) hab)
  · constructor
    · rw [← recover_6_1_1_0]
      exact word_mem K hP hg _
    · rw [← recover_6_1_1_1]
      exact word_mem K hP hg _

/-- Cell 7 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_7 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 7 a b) (hg : representative 7 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · constructor
    · rw [← recover_7_0_0_0]
      exact word_mem K hP hg _
    · rw [← recover_7_0_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 7 0 1) hab)
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 7 1 0) hab)
  · constructor
    · rw [← recover_7_1_1_0]
      exact word_mem K hP hg _
    · rw [← recover_7_1_1_1]
      exact word_mem K hP hg _

/-- Cell 8 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_8 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 8 a b) (hg : representative 8 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · constructor
    · rw [← recover_8_0_0_0]
      exact word_mem K hP hg _
    · rw [← recover_8_0_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 8 0 1) hab)
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 8 1 0) hab)
  · constructor
    · rw [← recover_8_1_1_0]
      exact word_mem K hP hg _
    · rw [← recover_8_1_1_1]
      exact word_mem K hP hg _

end Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
