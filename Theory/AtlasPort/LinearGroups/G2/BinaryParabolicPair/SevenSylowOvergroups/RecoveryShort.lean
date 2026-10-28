module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.Certificate

/-!
# Checked actor recovery in binary derived Bruhat cells 3 through 5

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

private theorem recover_3_1_0_0 : word (representative 3 1 0) [0, 1, 2, 2, 0, 2, 2, 2, 2, 0] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4647790168770664866) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 1).val (column 4647790168770664866 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 4918170301080042364) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 4918170301080042364 c) r =
          column 4647790168770664866 c r) c)
    refine Check.cons (b := 15655773534989584129) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 15655773534989584129 c) r =
          column 4918170301080042364 c r) c)
    refine Check.cons (b := 15680759794432949500) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 0).val (column 15680759794432949500 c) r =
          column 15655773534989584129 c r) c)
    refine Check.cons (b := 4600775378993463360) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 4600775378993463360 c) r =
          column 15680759794432949500 c r) c)
    refine Check.cons (b := 4341400706740551776) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 4341400706740551776 c) r =
          column 4600775378993463360 c r) c)
    refine Check.cons (b := 13852087463977410622) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 13852087463977410622 c) r =
          column 4341400706740551776 c r) c)
    refine Check.cons (b := 9277662281737232027) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 9277662281737232027 c) r =
          column 13852087463977410622 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 0).val (column 9241421688590303745 c) r =
          column 9277662281737232027 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_3_1_0_1 : word (representative 3 1 0) [0, 2, 2, 1, 2, 0, 2, 2, 2, 2, 0] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 9268479298589312221) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 0).val (column 9268479298589312221 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 4647790168770648354) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 4647790168770648354 c) r =
          column 9268479298589312221 c r) c)
    refine Check.cons (b := 4918099932335881084) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 4918099932335881084 c) r =
          column 4647790168770648354 c r) c)
    refine Check.cons (b := 4918170301080042364) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 1).val (column 4918170301080042364 c) r =
          column 4918099932335881084 c r) c)
    refine Check.cons (b := 15655773534989584129) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 15655773534989584129 c) r =
          column 4918170301080042364 c r) c)
    refine Check.cons (b := 15680759794432949500) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 0).val (column 15680759794432949500 c) r =
          column 15655773534989584129 c r) c)
    refine Check.cons (b := 4600775378993463360) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 4600775378993463360 c) r =
          column 15680759794432949500 c r) c)
    refine Check.cons (b := 4341400706740551776) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 4341400706740551776 c) r =
          column 4600775378993463360 c r) c)
    refine Check.cons (b := 13852087463977410622) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 13852087463977410622 c) r =
          column 4341400706740551776 c r) c)
    refine Check.cons (b := 9277662281737232027) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 2).val (column 9277662281737232027 c) r =
          column 13852087463977410622 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 1 0) 0).val (column 9241421688590303745 c) r =
          column 9277662281737232027 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_3_0_1_0 : word (representative 3 0 1) [0, 0, 2, 2, 2, 0, 0, 2, 2, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 0).val (column 4665804584541527399 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 4901214956755969947) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 4901214956755969947 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 11374236092258294750) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 11374236092258294750 c) r =
          column 4901214956755969947 c r) c)
    refine Check.cons (b := 7492472410635689637) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 7492472410635689637 c) r =
          column 11374236092258294750 c r) c)
    refine Check.cons (b := 7466231457512023359) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 0).val (column 7466231457512023359 c) r =
          column 7492472410635689637 c r) c)
    refine Check.cons (b := 7492578455580622976) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 0).val (column 7492578455580622976 c) r =
          column 7466231457512023359 c r) c)
    refine Check.cons (b := 18202354183915601952) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 18202354183915601952 c) r =
          column 7492578455580622976 c r) c)
    refine Check.cons (b := 13852087463977361410) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 13852087463977361410 c) r =
          column 18202354183915601952 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 9241421688590303745 c) r =
          column 13852087463977361410 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_3_0_1_1 : word (representative 3 0 1) [2, 2, 0, 2, 0, 1, 0, 2, 1, 2, 2] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 6980586079996739843) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 6980586079996739843 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 461057210415907645) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 461057210415907645 c) r =
          column 6980586079996739843 c r) c)
    refine Check.cons (b := 459480920355806654) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 0).val (column 459480920355806654 c) r =
          column 461057210415907645 c r) c)
    refine Check.cons (b := 7449408929607827038) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 7449408929607827038 c) r =
          column 459480920355806654 c r) c)
    refine Check.cons (b := 7423898561259022214) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 0).val (column 7423898561259022214 c) r =
          column 7449408929607827038 c r) c)
    refine Check.cons (b := 7423896362235774854) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 1).val (column 7423896362235774854 c) r =
          column 7423898561259022214 c r) c)
    refine Check.cons (b := 7449513383205952418) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 0).val (column 7449513383205952418 c) r =
          column 7423896362235774854 c r) c)
    refine Check.cons (b := 18202243133241205280) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 18202243133241205280 c) r =
          column 7449513383205952418 c r) c)
    refine Check.cons (b := 18202354183915601952) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 1).val (column 18202354183915601952 c) r =
          column 18202243133241205280 c r) c)
    refine Check.cons (b := 13852087463977361410) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 13852087463977361410 c) r =
          column 18202354183915601952 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 3 0 1) 2).val (column 9241421688590303745 c) r =
          column 13852087463977361410 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_4_1_0_0 : word (representative 4 1 0) [0, 2, 0, 2, 2, 1, 2, 2, 1, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 13906060480215762169) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 13906060480215762169 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 13852153434675028738) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 0).val (column 13852153434675028738 c) r =
          column 13906060480215762169 c r) c)
    refine Check.cons (b := 18205731728681712675) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 18205731728681712675 c) r =
          column 13852153434675028738 c r) c)
    refine Check.cons (b := 6627605765645385916) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 6627605765645385916 c) r =
          column 18205731728681712675 c r) c)
    refine Check.cons (b := 6627334186273300412) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 1).val (column 6627334186273300412 c) r =
          column 6627605765645385916 c r) c)
    refine Check.cons (b := 11710022351581283679) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 11710022351581283679 c) r =
          column 6627334186273300412 c r) c)
    refine Check.cons (b := 2351057169628683013) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 2351057169628683013 c) r =
          column 11710022351581283679 c r) c)
    refine Check.cons (b := 2350881247768215813) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 1).val (column 2350881247768215813 c) r =
          column 2351057169628683013 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 9241421688590303745 c) r =
          column 2350881247768215813 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_4_1_0_1 : word (representative 4 1 0) [2, 1, 0, 2, 2, 2, 0, 2, 2, 2] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 11563696179271655430) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 11563696179271655430 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 11563830319690245894) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 1).val (column 11563830319690245894 c) r =
          column 11563696179271655430 c r) c)
    refine Check.cons (b := 11590717639074635870) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 0).val (column 11590717639074635870 c) r =
          column 11563830319690245894 c r) c)
    refine Check.cons (b := 8826387663297609952) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 8826387663297609952 c) r =
          column 11590717639074635870 c r) c)
    refine Check.cons (b := 506226597106327680) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 506226597106327680 c) r =
          column 8826387663297609952 c r) c)
    refine Check.cons (b := 72628283826535072) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 72628283826535072 c) r =
          column 506226597106327680 c r) c)
    refine Check.cons (b := 72907577028992998) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 0).val (column 72907577028992998 c) r =
          column 72628283826535072 c r) c)
    refine Check.cons (b := 153686518596699487) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 153686518596699487 c) r =
          column 72907577028992998 c r) c)
    refine Check.cons (b := 2350881247768215813) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 2350881247768215813 c) r =
          column 153686518596699487 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 1 0) 2).val (column 9241421688590303745 c) r =
          column 2350881247768215813 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_4_0_1_0 : word (representative 4 0 1) [0, 0, 2, 2, 2, 0, 0, 2, 2, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 4665804584541527399) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 0).val (column 4665804584541527399 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 13852017836588745945) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 13852017836588745945 c) r =
          column 4665804584541527399 c r) c)
    refine Check.cons (b := 4324511225313574916) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 4324511225313574916 c) r =
          column 13852017836588745945 c r) c)
    refine Check.cons (b := 216801875371016320) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 216801875371016320 c) r =
          column 4324511225313574916 c r) c)
    refine Check.cons (b := 216522517224152645) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 0).val (column 216522517224152645 c) r =
          column 216801875371016320 c r) c)
    refine Check.cons (b := 216805178217784763) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 0).val (column 216805178217784763 c) r =
          column 216522517224152645 c r) c)
    refine Check.cons (b := 153125901328990170) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 153125901328990170 c) r =
          column 216805178217784763 c r) c)
    refine Check.cons (b := 2341874177872495420) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 2341874177872495420 c) r =
          column 153125901328990170 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 9241421688590303745 c) r =
          column 2341874177872495420 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_4_0_1_1 : word (representative 4 0 1) [0, 2, 2, 2, 0, 0, 2, 2, 1, 2, 2] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 9268479298589312221) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 0).val (column 9268479298589312221 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 11590717639064109060) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 11590717639064109060 c) r =
          column 9268479298589312221 c r) c)
    refine Check.cons (b := 15753486978122547392) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 15753486978122547392 c) r =
          column 11590717639064109060 c r) c)
    refine Check.cons (b := 11467248985203449888) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 11467248985203449888 c) r =
          column 15753486978122547392 c r) c)
    refine Check.cons (b := 11510348888112389116) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 0).val (column 11510348888112389116 c) r =
          column 11467248985203449888 c r) c)
    refine Check.cons (b := 11467085554921889445) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 0).val (column 11467085554921889445 c) r =
          column 11510348888112389116 c r) c)
    refine Check.cons (b := 2522753602571879835) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 2522753602571879835 c) r =
          column 11467085554921889445 c r) c)
    refine Check.cons (b := 153161085701103578) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 153161085701103578 c) r =
          column 2522753602571879835 c r) c)
    refine Check.cons (b := 153125901328990170) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 1).val (column 153125901328990170 c) r =
          column 153161085701103578 c r) c)
    refine Check.cons (b := 2341874177872495420) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 2341874177872495420 c) r =
          column 153125901328990170 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 4 0 1) 2).val (column 9241421688590303745 c) r =
          column 2341874177872495420 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_5_1_0_0 : word (representative 5 1 0) [0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 1, 2, 1] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 4647930906259028386) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 4647930906259028386 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 14193446431437340924) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 2).val (column 14193446431437340924 c) r =
          column 4647930906259028386 c r) c)
    refine Check.cons (b := 14140661991580312066) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 14140661991580312066 c) r =
          column 14193446431437340924 c r) c)
    refine Check.cons (b := 13340441137037506978) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 2).val (column 13340441137037506978 c) r =
          column 14140661991580312066 c r) c)
    refine Check.cons (b := 13374537332988591932) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 13374537332988591932 c) r =
          column 13340441137037506978 c r) c)
    refine Check.cons (b := 13374421884267709244) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 1).val (column 13374421884267709244 c) r =
          column 13374537332988591932 c r) c)
    refine Check.cons (b := 13340478520440772932) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 13340478520440772932 c) r =
          column 13374421884267709244 c r) c)
    refine Check.cons (b := 16634530616982739815) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 2).val (column 16634530616982739815 c) r =
          column 13340478520440772932 c r) c)
    refine Check.cons (b := 16591086140060886783) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 16591086140060886783 c) r =
          column 16634530616982739815 c r) c)
    refine Check.cons (b := 6946492949481511236) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 2).val (column 6946492949481511236 c) r =
          column 16591086140060886783 c r) c)
    refine Check.cons (b := 6946380799295438916) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 1).val (column 6946380799295438916 c) r =
          column 6946492949481511236 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 2).val (column 9241492057334482433 c) r =
          column 6946380799295438916 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_5_1_0_1 : word (representative 5 1 0) [0, 1, 2, 0, 1, 0, 1, 2, 0] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 9268479298589312221) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 9268479298589312221 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 9268655220449754845) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 1).val (column 9268655220449754845 c) r =
          column 9268479298589312221 c r) c)
    refine Check.cons (b := 16158493423159156866) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 2).val (column 16158493423159156866 c) r =
          column 9268655220449754845 c r) c)
    refine Check.cons (b := 16203597925194628359) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 16203597925194628359 c) r =
          column 16158493423159156866 c r) c)
    refine Check.cons (b := 16203494571101586951) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 1).val (column 16203494571101586951 c) r =
          column 16203597925194628359 c r) c)
    refine Check.cons (b := 16158561592865440572) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 16158561592865440572 c) r =
          column 16203494571101586951 c r) c)
    refine Check.cons (b := 16158493423144517692) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 1).val (column 16158493423144517692 c) r =
          column 16158561592865440572 c r) c)
    refine Check.cons (b := 9277662281737232027) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 2).val (column 9277662281737232027 c) r =
          column 16158493423144517692 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 1 0) 0).val (column 9241421688590303745 c) r =
          column 9277662281737232027 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

private theorem recover_5_0_1_0 : word (representative 5 0 1) [2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 2] = cubicActor := by
  apply check_eq (a := 4665733663881429251)
  · refine Check.cons (b := 289708481837777148) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 289708481837777148 c) r =
          column 4665733663881429251 c r) c)
    refine Check.cons (b := 289713979395906556) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 1).val (column 289713979395906556 c) r =
          column 289708481837777148 c r) c)
    refine Check.cons (b := 5034466142087808350) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 5034466142087808350 c) r =
          column 289713979395906556 c r) c)
    refine Check.cons (b := 5015843230449418044) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 0).val (column 5015843230449418044 c) r =
          column 5034466142087808350 c r) c)
    refine Check.cons (b := 15773089731398703975) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 15773089731398703975 c) r =
          column 5015843230449418044 c r) c)
    refine Check.cons (b := 15726465380349926143) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 0).val (column 15726465380349926143 c) r =
          column 15773089731398703975 c r) c)
    refine Check.cons (b := 11599823699238010627) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 11599823699238010627 c) r =
          column 15726465380349926143 c r) c)
    refine Check.cons (b := 11599619190075228675) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 1).val (column 11599619190075228675 c) r =
          column 11599823699238010627 c r) c)
    refine Check.cons (b := 2315589675449580231) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 2315589675449580231 c) r =
          column 11599619190075228675 c r) c)
    refine Check.cons (b := 2306549068282970940) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 0).val (column 2306549068282970940 c) r =
          column 2315589675449580231 c r) c)
    refine Check.cons (b := 2306546869259714620) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 1).val (column 2306546869259714620 c) r =
          column 2306549068282970940 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 9241421688590303745 c) r =
          column 2306546869259714620 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      cubicActor.val (basisVector c) r = column 4665733663881429251 c r) c)

private theorem recover_5_0_1_1 : word (representative 5 0 1) [2, 0, 0, 0, 1, 2, 1] = movingActor := by
  apply check_eq (a := 9232484858079610369)
  · refine Check.cons (b := 6946380799295430690) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 6946380799295430690 c) r =
          column 9232484858079610369 c r) c)
    refine Check.cons (b := 6919470825674465029) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 0).val (column 6919470825674465029 c) r =
          column 6946380799295430690 c r) c)
    refine Check.cons (b := 6946486378288889539) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 0).val (column 6946486378288889539 c) r =
          column 6919470825674465029 c r) c)
    refine Check.cons (b := 6919365660615624572) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 0).val (column 6919365660615624572 c) r =
          column 6946486378288889539 c r) c)
    refine Check.cons (b := 6919359063545856124) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 1).val (column 6919359063545856124 c) r =
          column 6919365660615624572 c r) c)
    refine Check.cons (b := 9241492057334482433) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 2).val (column 9241492057334482433 c) r =
          column 6919359063545856124 c r) c)
    refine Check.cons (b := 9241421688590303745) ?_ ?_
    · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
        (letter (representative 5 0 1) 1).val (column 9241421688590303745 c) r =
          column 9241492057334482433 c r) c)
    exact Check.nil
  · exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
      movingActor.val (basisVector c) r = column 9232484858079610369 c r) c)

/-- Cell 3 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_3 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 3 a b) (hg : representative 3 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 3 0 0) hab)
  · constructor
    · rw [← recover_3_0_1_0]
      exact word_mem K hP hg _
    · rw [← recover_3_0_1_1]
      exact word_mem K hP hg _
  · constructor
    · rw [← recover_3_1_0_0]
      exact word_mem K hP hg _
    · rw [← recover_3_1_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 3 1 1) hab)

/-- Cell 4 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_4 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 4 a b) (hg : representative 4 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 4 0 0) hab)
  · constructor
    · rw [← recover_4_0_1_0]
      exact word_mem K hP hg _
    · rw [← recover_4_0_1_1]
      exact word_mem K hP hg _
  · constructor
    · rw [← recover_4_1_0_0]
      exact word_mem K hP hg _
    · rw [← recover_4_1_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 4 1 1) hab)

/-- Cell 5 recovers both actors from the actual derived Sylow subgroup. -/
theorem recover_cell_5 (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (a b : Fin 2) (hab : allowed 5 a b) (hg : representative 5 a b ∈ K) :
    cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases a <;> fin_cases b
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 5 0 0) hab)
  · constructor
    · rw [← recover_5_0_1_0]
      exact word_mem K hP hg _
    · rw [← recover_5_0_1_1]
      exact word_mem K hP hg _
  · constructor
    · rw [← recover_5_1_0_0]
      exact word_mem K hP hg _
    · rw [← recover_5_1_0_1]
      exact word_mem K hP hg _
  · exact False.elim ((by unfold allowed; decide : ¬ allowed 5 1 1) hab)

end Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
