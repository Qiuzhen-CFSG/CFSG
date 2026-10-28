module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangles
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFaithfulness
import Mathlib.Tactic.FinCases
/-!
# The faithful source rectangle normalizer actions

Commuting with the six rectangle roots forces all off-rectangle entries to
vanish and all diagonal entries to be one. Hence each rectangle is its own
centralizer in SL₅(2). Since the marked rectangle contains z, its ambient
centralizer lies in C_G(z), where the full marking transports this calculation.
The resulting literal normalizer quotients act faithfully by conjugation.

This supplies the faithful normalizer actions used in Aschbacher, *Sporadic
Groups* (1994), 40.2–40.4, printed pp.217–218. Identification of the quotient
image, the splittings, and the §41 local comparison remain source obligations.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear

private theorem root_commuting_row (g : SL) (i j : Fin 5) (hij : i < j)
    (hg : root hij * g = g * root hij) (k : Fin 5) :
    g j k = if k = j then g i i else 0 := by
  have he := congrArg (fun a : SL => a i k) hg
  change ((1 + Matrix.single i j 1) * g.val : Matrix (Fin 5) (Fin 5) (ZMod 2)) i k = (g.val * (1 + Matrix.single i j 1) : Matrix (Fin 5) (Fin 5) (ZMod 2)) i k at he
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_apply, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
      one_mul, mul_one, add_right_inj, ite_true] using he
  · simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_apply, Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ hk,
      one_mul, add_zero, add_eq_left, if_neg hk] using he

private theorem root_commuting_column (g : SL) (i j : Fin 5) (hij : i < j)
    (hg : root hij * g = g * root hij) (k : Fin 5) :
    g k i = if k = i then g j j else 0 := by
  have he := congrArg (fun a : SL => a k j) hg
  change ((1 + Matrix.single i j 1) * g.val : Matrix (Fin 5) (Fin 5) (ZMod 2)) k j = (g.val * (1 + Matrix.single i j 1) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k j at he
  by_cases hk : k = i
  · subst k
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_apply, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
      one_mul, mul_one, add_right_inj, ite_true] using he.symm
  · simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_apply, Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hk,
      mul_one, add_zero, add_eq_left, if_neg hk] using he.symm

private theorem rectangle_centralizer_entries (c : ℕ) (hc : c = 2 ∨ c = 3)
    (g : SL) (hg : g ∈ Subgroup.centralizer (rectangle c : Set SL)) :
    ∀ i j : Fin 5, ¬ (i.val < c ∧ c ≤ j.val) → g i j = if i = j then 1 else 0 := by
  have hroot (i j : Fin 5) (hij : i < j) (hi : i.val < c) (hj : c ≤ j.val) :
      root hij * g = g * root hij :=
    mem_centralizer_iff.mp hg _ (subset_closure ⟨i, j, hij, hi, hj, rfl⟩)
  have hc0 : 0 < c := by omega
  have hc4 : c ≤ 4 := by omega
  have hcol (k : Fin 5) : g k 0 = if k = 0 then g 4 4 else 0 :=
    root_commuting_column g 0 4 (by decide) (hroot 0 4 (by decide) hc0 hc4) k
  have h44 : g 4 4 = 1 := by
    have hn : g 4 4 ≠ 0 := by
      intro he
      apply g.det_ne_zero
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro k
      simp [hcol k, he]
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn
  have h00 : g 0 0 = 1 := by simpa [h44] using hcol 0
  intro i j hij
  by_cases hj : j.val < c
  · have hj4 : j < 4 := by omega
    rw [root_commuting_column g j 4 hj4 (hroot j 4 hj4 hj hc4), h44]
  · have hi : c ≤ i.val := by omega
    have h0i : 0 < i := by omega
    rw [root_commuting_row g 0 i h0i (hroot 0 i h0i hc0 hi), h00]
    simp only [eq_comm]

/-- The plane rectangle centralizes only itself in the actual binary model. -/
theorem model_plane_centralizer : Subgroup.centralizer (Model.plane : Set SL) = Model.plane := by
  apply le_antisymm
  · intro g hg
    exact (RectangleCoordinates.mem2_iff g).mpr (rectangle_centralizer_entries 2 (Or.inl rfl) g hg)
  · let := model_rectangle_commutative 2
    exact (rectangle 2).le_centralizer

/-- The three-space rectangle is likewise self-centralizing. -/
theorem model_threeSpace_centralizer :
    Subgroup.centralizer (Model.threeSpace : Set SL) = Model.threeSpace := by
  apply le_antisymm
  · intro g hg
    exact (RectangleCoordinates.mem3_iff g).mpr (rectangle_centralizer_entries 3 (Or.inr rfl) g hg)
  · let := model_rectangle_commutative 3
    exact (rectangle 3).le_centralizer


variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private theorem marked_self_centralizer (A : Subgroup SL) (hAC : A ≤ centralizer)
    (hzA : z ∈ F.pullback A) (hself : Subgroup.centralizer (A : Set SL) = A) :
    Subgroup.centralizer (F.pullback A : Set G) = F.pullback A := by
  have image_mem (a : A) :
      (F.equiv.symm ⟨a, hAC a.property⟩ : G) ∈ F.pullback A := by
    apply (F.mem_pullback_iff A _).mpr
    simpa only [F.equiv.apply_symm_apply] using a.property
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ Subgroup.centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx z hzA).symm
    apply (F.mem_pullback_iff A ⟨x, hxC⟩).mpr
    rw [← hself]
    apply mem_centralizer_iff.mpr
    intro a ha
    let b := F.equiv.symm ⟨a, hAC ha⟩
    have he : b * ⟨x, hxC⟩ = ⟨x, hxC⟩ * b :=
      Subtype.ext (mem_centralizer_iff.mp hx b (image_mem ⟨a, ha⟩))
    have him := congrArg (fun q => (F.equiv q : SL)) he
    simpa only [map_mul, Subgroup.coe_mul, b, F.equiv.apply_symm_apply] using him
  · intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    let xc : Subgroup.centralizer ({z} : Set G) := ⟨x, F.pullback_le A hx⟩
    let yc : Subgroup.centralizer ({z} : Set G) := ⟨y, F.pullback_le A hy⟩
    have hm : (F.equiv xc : SL) ∈ Subgroup.centralizer (A : Set SL) := by
      rw [hself]
      exact (F.mem_pullback_iff A xc).mp hx
    have he : F.equiv yc * F.equiv xc = F.equiv xc * F.equiv yc :=
      Subtype.ext (mem_centralizer_iff.mp hm _ ((F.mem_pullback_iff A yc).mp hy))
    have hxy : yc * xc = xc * yc := F.equiv.injective (by simpa only [map_mul] using he)
    exact congrArg Subtype.val hxy

/-- The source plane group is self-centralizing in the entire ambient group. -/
theorem source_plane_centralizer : Subgroup.centralizer (F.plane : Set G) = F.plane :=
  marked_self_centralizer F Model.plane Model.plane_le_centralizer
    (point_mem_plane F) model_plane_centralizer

/-- The source three-space group is self-centralizing in the entire ambient group. -/
theorem source_threeSpace_centralizer :
    Subgroup.centralizer (F.threeSpace : Set G) = F.threeSpace :=
  marked_self_centralizer F Model.threeSpace Model.threeSpace_le_centralizer
    (point_mem_threeSpace F) model_threeSpace_centralizer

/-- The actual plane normalizer. -/
abbrev sourcePlaneNormalizer := normalizer (F.plane : Set G)
/-- The actual three-space normalizer. -/
abbrev sourceThreeSpaceNormalizer := normalizer (F.threeSpace : Set G)
/-- Quotient by the plane as a normal subgroup of its own normalizer. -/
abbrev sourcePlaneQuotient :=
  sourcePlaneNormalizer F ⧸ F.plane.subgroupOf (sourcePlaneNormalizer F)
/-- Quotient by the three-space group inside its own normalizer. -/
abbrev sourceThreeSpaceQuotient :=
  sourceThreeSpaceNormalizer F ⧸ F.threeSpace.subgroupOf (sourceThreeSpaceNormalizer F)

/-- Conjugation on the original plane, descended through its exact kernel. -/
def sourcePlaneQuotientAction : sourcePlaneQuotient F →* MulAut F.plane :=
  QuotientGroup.lift _ F.plane.normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker, source_plane_centralizer F])

/-- The action kernel has been fully removed in the literal quotient. -/
theorem sourcePlaneQuotientAction_injective : Function.Injective (sourcePlaneQuotientAction F) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, source_plane_centralizer F]

/-- The quotient action retains ambient left-conjugation on each marked element. -/
theorem sourcePlaneQuotientAction_mk (n : sourcePlaneNormalizer F) (a : F.plane) :
    (sourcePlaneQuotientAction F (QuotientGroup.mk n) a : G) = (n : G) * a * (n : G)⁻¹ := by
  exact normalizerMonoidHom_apply_apply_coe F.plane n a

/-- The second source quotient action on its actual marked group. -/
def sourceThreeSpaceQuotientAction : sourceThreeSpaceQuotient F →* MulAut F.threeSpace :=
  QuotientGroup.lift _ F.threeSpace.normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker, source_threeSpace_centralizer F])

/-- Faithfulness for the literal three-space quotient. -/
theorem sourceThreeSpaceQuotientAction_injective :
    Function.Injective (sourceThreeSpaceQuotientAction F) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, source_threeSpace_centralizer F]

/-- This action uses the same ambient conjugation and marking as source fusion. -/
theorem sourceThreeSpaceQuotientAction_mk (n : sourceThreeSpaceNormalizer F) (a : F.threeSpace) :
    (sourceThreeSpaceQuotientAction F (QuotientGroup.mk n) a : G) = (n : G) * a * (n : G)⁻¹ := by
  exact normalizerMonoidHom_apply_apply_coe F.threeSpace n a

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
