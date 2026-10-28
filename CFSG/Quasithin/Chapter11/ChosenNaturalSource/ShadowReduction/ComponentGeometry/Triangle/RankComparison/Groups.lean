module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Symplectic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Transport

/-!
# The symplectic side of the literal mutual-action comparison

An actual equivariant multiplicative marking identifies the ambient commutator
with the fixed binary four-space. The reverse induced automizer therefore has
rank four. The initial lower bound on the forward automizer is supplied by the
weak-closure selection theorem, not assumed as a conclusion of the comparison.

Source: Aschbacher--Smith, 11.4.1(2), printed p.776.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
variable {G F : Type*} [Group G] [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- The same plane marking computes the actual commutator and reverse automizer. -/
theorem mutual_plane_ranks (hF : Nat.card F = 4)
    (H A U : Subgroup G) (hAH : A ≤ H)
    (hHU : H ≤ normalizer (U : Set G)) (hUA : U ≤ normalizer (A : Set G))
    (α : H →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hact : ∀ (a : H) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hHU a.property) u.val).mp u.property⟩).toAdd =
        α a • (e u).toAdd)
    (himage : α.range ≤ Plane.radical.map planeLocal.subtype)
    (hlarge : 4 ≤ rank (ChapterE.inducedAutomizer U A)) :
    ⁅U,A⁆ = U ⊓ centralizer (A : Set G) ∧
      rank (⁅U,A⁆ : Subgroup G) = 4 ∧
      rank (ChapterE.inducedAutomizer A U) = 4 := by
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  let β : A →* Sp F := α.comp (inclusion hAH)
  let j : Multiplicative (Vector F) →* G := U.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := U.subtype_injective.comp e.symm.injective
  have hjr : j.range = U := by
    change (U.subtype.comp e.symm.toMonoidHom).range = U
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, U.range_subtype]
  have hβ (a : A) (v : Vector F) : j (Multiplicative.ofAdd (σ (β a) v)) =
      a.val * j (Multiplicative.ofAdd v) * a.val⁻¹ := by
    have hh := hact (inclusion hAH a) (e.symm (Multiplicative.ofAdd v))
    simp only [e.apply_symm_apply, toAdd_ofAdd] at hh
    have he := congrArg (fun w => (e.symm (Multiplicative.ofAdd w)).val) hh
    change (e.symm (Multiplicative.ofAdd (α (inclusion hAH a) • v))).val = _
    simpa only [ofAdd_toAdd, e.symm_apply_apply, inclusion, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, MonoidHom.mk'_apply, j] using he.symm
  have hfaith : Function.Injective σ := by
    intro a b hab
    apply Subtype.ext
    ext i k
    have hh := LinearMap.congr_fun hab (Pi.single k (1 : F))
    have hk := congrFun hh i
    change (Matrix.mulVec a.val (Pi.single k (1 : F))) i =
      (Matrix.mulVec b.val (Pi.single k (1 : F))) i at hk
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hk
  have hr := marked_action_rank σ hfaith U A (hAH.trans hHU) j hj hjr β hβ
  have hc : 4 < Nat.card β.range := by
    have hl : 4 ≤ rank β.range := hr.symm ▸ hlarge
    change 4 ≤ Nat.log 2 (Nat.card β.range) at hl
    have hh := (Nat.le_log_iff_pow_le (by decide : 1 < 2)
      (Nat.card_pos (α := β.range)).ne').mp hl
    exact lt_of_lt_of_le (by decide : 4 < 2 ^ 4) hh
  obtain ⟨he, hd, hq⟩ := plane_fixed_moved hF β.range
    (by rintro _ ⟨a,rfl⟩; exact himage ⟨inclusion hAH a,rfl⟩) hc
  have hcomm := embedded_moved σ U A j hjr β hβ
  have hfixed := embedded_fixed σ U A j hj hjr β hβ
  have hcfix : Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) = 16 := by
    rw [← hfixed, embeddedSpace_card j hj, hd]
    norm_num
  have heq : ⁅U,A⁆ = U ⊓ centralizer (A : Set G) := by
    rw [← hcomm, he, hfixed]
  refine ⟨heq, ?_, ?_⟩
  · rw [heq, rank, hcfix]
    rfl
  · rw [ChapterE.rank_inducedAutomizer A U hUA]
    unfold ChapterE.subgroupCorank
    rw [inf_relIndex_left, embedded_centralizer_index σ U A j hj hjr β hβ, hq]
    rfl
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
