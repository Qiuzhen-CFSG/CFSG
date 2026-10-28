module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LocalFactorEmbedding
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal

/-!
# Recognizing the actual linear local groups

The canonical simple root has the order of the original even field, so
its injective original quotient projection covers the entire quotient
Sylow. LocalFactorEmbedding then identifies R_i itself with PSL₂ over
that same field, without using a Schur multiplier classification.

The full panel-action kernel on R_i is central. Centerlessness of this
concrete PSL₂ makes the kernel trivial, while the proved linear (2B)
containment gives surjectivity onto the Fong--Seitz local permutation group.
Thus the original lifted root group, R_i and the actual local permutation
group all have compatible equivalences to the original L_i/O₂(L_i).
The equations retain the original factor projection and panel action.

Source: Fong--Seitz I (2B), p.9, and (5C)(b), pp.25--26; the original
perfect local-factor input is Aschbacher--Smith F.1.1--3, pp.259--260.
Only this local factor is required to be perfect. The existing cubic
recognition retains the nonperfect PSL₂(2) case. No arbitrary full endpoint
quotient or seven-row rank-two recognition is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  [Finite (L i)] (hp : Group.IsPerfect (L i))
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))

include μ in
theorem linear_simpleRootSylowProjection_surjective :
    Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT) := by
  have hc : Nat.card (quotientSylow T) = Nat.card F :=
    (Nat.card_congr (linearSylowEquiv i T μ).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μ)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))
  exact ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨simpleRootSylowProjection_injective Q e h split i hp T hT,
      (simpleRoot_card_linear Q e h split i T hT μ).trans hc.symm⟩).2

def linearRankOneEquiv : rankOne Q split i ≃* PSL(2,F) :=
  (rankOneQuotientEquiv Q e h split i hp T hT
    (linear_simpleRootSylowProjection_surjective Q e h split i hp T hT μ)).trans μ

@[simp] theorem linearRankOneEquiv_apply (r : rankOne Q split i) :
    linearRankOneEquiv Q e h split i hp T hT μ r =
      μ (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) := by
  rw [linearRankOneEquiv, MulEquiv.trans_apply, rankOneQuotientEquiv_apply]

@[simp] theorem linearRankOneEquiv_simpleRoot (r : simpleRoot Q split i) :
    linearRankOneEquiv Q e h split i hp T hT μ
      (inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) r) =
      μ (simpleRootProjection Q e h split i hp r) := by
  rw [linearRankOneEquiv, MulEquiv.trans_apply, rankOneQuotientEquiv_projection,
    rankOneProjection_simpleRoot]

include e h hp hT μ in
theorem linear_root_local_projection_injective :
    Function.Injective (RootLocalCover.projection Q split i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  let a := linearRankOneEquiv Q e h split i hp T hT μ
  have hz := MulEquivClass.apply_mem_center a (RootLocalCover.projection_ker_central Q split i hr)
  change a r ∈ center PSL(2,F) at hz
  rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot, mem_bot] at hz
  exact a.injective (hz.trans a.map_one.symm)

def linearLocalEquiv : localGroup Q split i ≃* PSL(2,F) :=
  (MulEquiv.ofBijective (RootLocalCover.projection Q split i)
    ⟨linear_root_local_projection_injective Q e h split i hp T hT μ,
      (RootLocalCover.central_odd_cover Q split i
        (linear_remainder_le_kernel Q e h split i T hT μ)).1⟩).symm.trans
          (linearRankOneEquiv Q e h split i hp T hT μ)

@[simp] theorem linearLocalEquiv_projection (r : rankOne Q split i) :
    linearLocalEquiv Q e h split i hp T hT μ (RootLocalCover.projection Q split i r) =
      μ (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) := by
  let a := MulEquiv.ofBijective (RootLocalCover.projection Q split i)
    ⟨linear_root_local_projection_injective Q e h split i hp T hT μ,
      (RootLocalCover.central_odd_cover Q split i
        (linear_remainder_le_kernel Q e h split i T hT μ)).1⟩
  change linearRankOneEquiv Q e h split i hp T hT μ (a.symm (a r)) = _
  rw [MulEquiv.symm_apply_apply, linearRankOneEquiv_apply]

def originalLinearRankOneEquiv : originalRankOne Q e split i ≃* PSL(2,F) :=
  (originalRankOneEquiv Q e split i).trans (linearRankOneEquiv Q e h split i hp T hT μ)

@[simp] theorem originalLinearRankOneEquiv_projection (r : originalRankOne Q e split i) :
    originalLinearRankOneEquiv Q e h split i hp T hT μ r =
      linearLocalEquiv Q e h split i hp T hT μ (originalRootProjection Q e split i r) := by
  have hr : originalRootProjection Q e split i r =
      RootLocalCover.projection Q split i (originalRankOneEquiv Q e split i r) := by
    apply Subtype.ext
    rw [originalRootProjection_apply, RootLocalCover.projection_apply]
  rw [hr]
  change linearRankOneEquiv Q e h split i hp T hT μ (originalRankOneEquiv Q e split i r) = _
  rw [linearLocalEquiv_projection, linearRankOneEquiv_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include h in
theorem linear_original_local_identification_of_model (i : Fin 2)
    (hp : Group.IsPerfect (L i)) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    ∃ a : originalRankOne Q e split i ≃* (L i) ⧸ pCore 2 (L i),
      ∃ b : localGroup Q split i ≃* (L i) ⧸ pCore 2 (L i),
        ∀ r, a r = b (originalRootProjection Q e split i r) := by
  let := h.finite_local i
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨T,hT⟩ := h.sylow i
  refine ⟨(originalLinearRankOneEquiv Q e h split i hp T hT μ).trans μ.symm,
    (linearLocalEquiv Q e h split i hp T hT μ).trans μ.symm, ?_⟩
  intro r
  exact congrArg μ.symm (originalLinearRankOneEquiv_projection Q e h split i hp T hT μ r)

include e h in
theorem linear_originalRootProjection_bijective (i : Fin 2)
    (hp : Group.IsPerfect (L i)) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    Function.Bijective (originalRootProjection Q e split i) := by
  obtain ⟨a,b,he⟩ := linear_original_local_identification_of_model Q e h split i hp hmodel
  constructor
  · intro r s hrs
    apply a.injective
    rw [he,he,hrs]
  · intro z
    obtain ⟨r,hr⟩ := a.surjective (b z)
    exact ⟨r,b.injective ((he r).symm.trans hr)⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
