module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.SpecificGroups.PSL3.CubicComponentAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# The cubic linear action in the source A.3.18 specialization

For the original SQTK group H and its component L with central two-kernel,
an even-degree PSL₃ model forces L normal. The actual conjugation action on
L/Z(L) has three-prime kernel and sends every generator of theta(H) into the
inner-diagonal image. Thus the entire original theta(H) acts through PGL₃.

This supplies the cubic field-exclusion prerequisite in the use of A.3.18 on
N_G(Dˣ) in the proof of 2.5.7, printed p.556. It does not identify theta(H),
its three-prime-core quotient, or the full A.3.18 alternatives.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.CubicLinearAction

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- Full cubic rank makes the original component normal, including central covers. -/
theorem component_normal (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {L : Subgroup H} (hL : IsComponent H L) (hZ : IsPGroup 2 (center L))
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hd : 3 ∣ 2 ^ n - 1)
    (e : L ⧸ center L ≃* PSL(3,F)) : L.Normal := by
  have heven := (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp hd
  have hr := Matrix.PSL3.CubicComponentAction.component_rank hZ hF heven e
  have hz : Nat.Coprime 3 (Nat.card (center L)) := by
    obtain ⟨m, hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  apply hL.normal_of_coprime_center_primeRank 3 hz
  have hu := hH.stronglyQuasithin 3 Nat.prime_three (by decide)
  omega

/-- Conjugation by the original ambient H on the marked central quotient. -/
def ambientAction (L : Subgroup H) [L.Normal] (e : L ⧸ center L ≃* PSL(3,F)) :
    H →* MulAut PSL(3,F) :=
  (action L e).comp ((MonoidHom.id H).codRestrict (normalizer (L : Set H))
    (fun x => by rw [L.normalizer_eq_top]; trivial))

/-- Every actual theta generator acts inner-diagonally in the same coordinates. -/
theorem ambient_cubic_innerDiagonal (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {L : Subgroup H} (hL : IsComponent H L) (hZ : IsPGroup 2 (center L))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hd : 3 ∣ 2 ^ n - 1)
    (e : L ⧸ center L ≃* PSL(3,F)) (x : H) (hx : orderOf x = 3) :
    let _ := component_normal hH hL hZ hF hd e
    ambientAction L e x ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F := by
  let := component_normal hH hL hZ hF hd e
  exact Matrix.PSL3.CubicComponentAction.cubic_innerDiagonal hL hZ
    (hH.stronglyQuasithin 3 Nat.prime_three (by decide)) hn hF
    ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp hd) e
    ⟨x, by rw [L.normalizer_eq_top]; trivial⟩
    (Subtype.ext (hx ▸ pow_orderOf_eq_one x))

/-- The actual theta(H), with the source order-three convention, has only
inner-diagonal image. Neither normality nor field exclusion is assumed. -/
theorem theta_image_le (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {L : Subgroup H} (hL : IsComponent H L) (hZ : IsPGroup 2 (center L))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hd : 3 ∣ 2 ^ n - 1)
    (e : L ⧸ center L ≃* PSL(3,F)) :
    let _ := component_normal hH hL hZ hF hd e
    (theta H).map (ambientAction L e) ≤ Matrix.PSL3.OuterSolvable.innerDiagonal F := by
  let := component_normal hH hL hZ hF hd e
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  intro x hx
  exact ambient_cubic_innerDiagonal hH hL hZ hn hF hd e x hx

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.CubicLinearAction
