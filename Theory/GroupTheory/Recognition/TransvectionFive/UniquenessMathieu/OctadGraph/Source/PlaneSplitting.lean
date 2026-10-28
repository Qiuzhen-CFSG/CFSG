module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CubicLift
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Boundary
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Complement
public import Theory.GroupTheory.SplitExtensionCoordinates.Marked

/-!
# Splitting the actual source plane normalizer

The cubic lift of the six-point kernel acts without nonidentity fixed
points on the 45-point rectangle. The checked six-bit action proves this
on every rectangle element. The join of the rectangle and the cubic lift
is normal of order 192. Frattini's argument supplies generation by the
rectangle and the cubic normalizer; their intersection is trivial because
normalizing the cubic while lying in the rectangle forces centralization.
Thus that normalizer is an actual complement.

Apply this to the opposite marking without changing the 21/45 orientation.
The resulting isomorphism identifies N_G(A₂) with the semidirect product
for its original quotient action on A₂. It preserves each kernel element
and the literal quotient map. The quotient is retained in full: the
normal cubic extension of S₆ is not replaced by S₆.

This proves the splitting used for the plane-group comparison in Aschbacher,
*Sporadic Groups* (1994), 41.4, p.222, from the source 40.4 cubic action,
pp.218–219. The native quotient-action comparison and agreement with the
row map on their common subgroup remain to be constructed.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer UniquenessLinear.PlaneTensor

private theorem normalizer_complement {K : Type*} [Group K] [Finite K]
    (A X : Subgroup K) [A.Normal] [(A ⊔ X).Normal]
    (hdis : Disjoint A X) (P : Sylow 3 ↥(A ⊔ X))
    (hP : P.toSubgroup.map (A ⊔ X).subtype = X)
    (hfixed : A ⊓ centralizer (X : Set K) = ⊥) :
    A.IsComplement' (normalizer (X : Set K)) := by
  have hgen := P.normalizer_sup_eq_top
  change normalizer ((P.toSubgroup.map (A ⊔ X).subtype : Subgroup K) : Set K) ⊔ (A ⊔ X) = ⊤ at hgen
  rw [hP, sup_comm A X, ← sup_assoc, sup_eq_left.mpr X.le_normalizer, sup_comm] at hgen
  have htriv : Disjoint A (normalizer (X : Set K)) := by
    apply disjoint_iff_inf_le.mpr
    rintro a ⟨ha, hn⟩
    have hc : a ∈ centralizer (X : Set K) := by
      intro x hx
      have haX : a * x * a⁻¹ ∈ X := (mem_normalizer_iff.mp hn x).mp hx
      have hX : a * x * a⁻¹ * x⁻¹ ∈ X := X.mul_mem haX (X.inv_mem hx)
      have hA : a * x * a⁻¹ * x⁻¹ ∈ A := by
        have hh := A.mul_mem ha ((inferInstance : A.Normal).conj_mem a⁻¹ (A.inv_mem ha) x)
        simpa only [mul_assoc] using hh
      have he : a * x * a⁻¹ * x⁻¹ = 1 :=
        mem_bot.mp (disjoint_iff_inf_le.mp hdis ⟨hA,hX⟩)
      have he' : a * x * a⁻¹ = x := mul_inv_eq_one.mp he
      exact ((mul_inv_eq_iff_eq_mul).mp he').symm
    rw [← hfixed]
    exact ⟨ha,hc⟩
  apply isComplement'_of_disjoint_and_mul_eq_univ htriv
  rw [← normal_mul, hgen, coe_top]

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- A nonidentity cubic kernel element fixes no nonidentity rectangle element. -/
theorem plane_cubic_fixed_free (hc : (F.fusion F.plane).ncard = 45)
    (n : planeNormalizer F)
    (hn : QuotientGroup.mk n ∈ (planeSextetAction F hc).ker)
    (hne : (QuotientGroup.mk n : planeQuotient F) ≠ 1)
    (a : F.plane) (hfix : (n : G) * (a : G) * (n : G)⁻¹ = a) : a = 1 := by
  obtain ⟨x, hx⟩ := (sourceEquiv F).surjective a
  have hxa : element F x = (a : G) := congrArg Subtype.val hx
  by_contra ha
  have hx0 : x ≠ 0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [← hxa, he, element_zero]
    rfl
  let q : planeQuotient F := QuotientGroup.mk n
  let f : Sextet.action.ker := ⟨planeSextetRepresentation F hc q, by
    change Sextet.action (planeSextetRepresentation F hc q) = 1
    rw [← planeSextetAction_apply]
    exact hn⟩
  have hf : f.val.val x = x := by
    apply element_injective F
    change element F ((planeSextetRepresentation F hc q).val x) = _
    rw [planeSextetRepresentation_val, quotientCodeAction_mk, normalizerAction_element,
      hxa, hfix]
  have hf1 := Sextet.kernel_fix_nonzero f x hx0 hf
  have hq : planeSextetRepresentation F hc q = 1 := congrArg Subtype.val hf1
  exact hne ((planeSextetRepresentation_injective F hc)
    (hq.trans (map_one _).symm))

/-- The full 45-point rectangle normalizer splits over its literal rectangle.
The complement is the normalizer of an actual cubic lift. -/
theorem plane_splits_of_forty_five (hc : (F.fusion F.plane).ncard = 45) :
    ∃ X : Subgroup (planeNormalizer F), Nat.card X = 3 ∧
      (F.plane.subgroupOf (planeNormalizer F)).IsComplement' (normalizer (X : Set (planeNormalizer F))) := by
  let A := F.plane.subgroupOf (planeNormalizer F)
  let q := QuotientGroup.mk' A
  obtain ⟨X,hX,himage,hjoin⟩ := exists_plane_cubic_lift F hc
  have hA : Nat.card A = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe F.plane.le_normalizer).toEquiv]
    exact plane_card F
  have hdis : Disjoint A X := disjoint_of_coprime_natCard (by rw [hA,hX]; decide)
  let N := A ⊔ X
  have hN : N = (planeSextetAction F hc).ker.comap q := by
    change A ⊔ X = _
    rw [sup_comm]
    exact hjoin
  let : N.Normal := hN ▸ inferInstance
  have hNc : Nat.card N = 192 := by
    rw [show N = A ⊔ X from rfl,
      card_sup_eq_mul_of_normalizes_of_disjoint A X
        (by rw [normalizer_eq_top]; exact le_top) hdis, hA, hX]
  have hXn : Nat.card (X.subgroupOf N) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show X ≤ N from le_sup_right)).toEquiv, hX]
  have hi : (X.subgroupOf N).index = 64 := by
    have hh := (X.subgroupOf N).card_mul_index
    rw [hXn, hNc] at hh
    omega
  let P : Sylow 3 N := (IsPGroup.of_card (p := 3) (n := 1)
    (by simpa only [pow_one] using hXn)).toSylow (by rw [hi]; decide)
  have hP : P.toSubgroup.map N.subtype = X := by
    change (X.subgroupOf N).map N.subtype = X
    rw [subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right]
  have hfixed : A ⊓ centralizer (X : Set (planeNormalizer F)) = ⊥ := by
    apply bot_unique
    rintro a ⟨ha,hac⟩
    have hex : ∃ n : planeNormalizer F, n ∈ X ∧ n ≠ 1 := by
      by_contra hh
      push Not at hh
      have he : X = ⊥ := eq_bot_iff.mpr (fun n hn => mem_bot.mpr (hh n hn))
      rw [he, card_bot] at hX
      omega
    obtain ⟨n, hn, hn1⟩ := hex
    have hnq : q n ≠ 1 := by
      intro he
      have hnA : n ∈ A := (QuotientGroup.eq_one_iff n).mp he
      exact hn1 (mem_bot.mp (disjoint_iff_inf_le.mp hdis ⟨hnA,hn⟩))
    have hnK : q n ∈ (planeSextetAction F hc).ker := himage ▸ mem_map_of_mem q hn
    have he : (a : G) = 1 := congrArg Subtype.val
      (plane_cubic_fixed_free F hc n hnK hnq (⟨a,ha⟩ : F.plane) (by
        have hh := hac n hn
        change n * a = a * n at hh
        have he : n * a * n⁻¹ = a := by rw [hh, mul_inv_cancel_right]
        exact congrArg (fun b : planeNormalizer F => (b : G)) he))
    exact mem_bot.mpr (Subtype.ext he)
  exact ⟨X,hX,normalizer_complement A X hdis P hP hfixed⟩

/-- The oriented source plane group has an actual complement to A₂. -/
theorem threeSpace_splits (D : LocalData F) :
    ∃ K : Subgroup (threeSpaceNormalizer F),
      (F.threeSpace.subgroupOf (threeSpaceNormalizer F)).IsComplement' K := by
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using D.orientation.2
  obtain ⟨X,_,hX⟩ := plane_splits_of_forty_five (oppositeMarking F) hc
  have h : ∃ K : Subgroup (normalizer ((oppositeMarking F).plane : Set G)),
      ((oppositeMarking F).plane.subgroupOf
        (normalizer ((oppositeMarking F).plane : Set G))).IsComplement' K := ⟨_, hX⟩
  rw [oppositeMarking_plane] at h
  exact h

/-- The actual plane normalizer is the semidirect product for its original
quotient action, with every rectangle element retained. -/
theorem exists_threeSpace_semidirect_equiv (D : LocalData F) :
    ∃ e : threeSpaceNormalizer F ≃*
        F.threeSpace ⋊[threeSpaceQuotientAction F] threeSpaceQuotient F,
      ∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
        SemidirectProduct.inl a := by
  obtain ⟨K, hK⟩ := threeSpace_splits F D
  obtain ⟨e, he, _⟩ := exists_marked_semidirect_equiv_of_split_coordinates
    (F.threeSpace.subgroupOf (threeSpaceNormalizer F)) K hK
    (MulEquiv.refl _) (subgroupOfEquivOfLe F.threeSpace.le_normalizer)
    (threeSpaceQuotientAction F) (by
      intro g a
      apply Subtype.ext
      exact (threeSpaceQuotientAction_mk_apply F g
        ((subgroupOfEquivOfLe F.threeSpace.le_normalizer) a)).symm)
  exact ⟨e, fun a => he ⟨inclusion F.threeSpace.le_normalizer a, a.property⟩⟩

omit [Finite G] in
/-- Marking the rectangle forces the semidirect quotient coordinate to be
the original quotient map, by faithfulness of its conjugation action. -/
theorem threeSpace_semidirect_quotient
    (e : threeSpaceNormalizer F ≃*
      F.threeSpace ⋊[threeSpaceQuotientAction F] threeSpaceQuotient F)
    (he : ∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
      SemidirectProduct.inl a) (n : threeSpaceNormalizer F) :
    (e n).right = (QuotientGroup.mk n : threeSpaceQuotient F) := by
  apply threeSpaceQuotientAction_injective F
  apply MulEquiv.ext
  intro a
  have hc : inclusion F.threeSpace.le_normalizer
      (threeSpaceQuotientAction F (QuotientGroup.mk n) a) =
      n * inclusion F.threeSpace.le_normalizer a * n⁻¹ := by
    apply Subtype.ext
    exact threeSpaceQuotientAction_mk_apply F n a
  have hh := congrArg e hc
  rw [he, map_mul, map_mul, map_inv, he] at hh
  have hl := congrArg SemidirectProduct.left hh
  simp only [SemidirectProduct.left_inl, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one,
    SemidirectProduct.inv_left, ← MulAut.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, MulAut.one_apply] at hl
  have hcomm : (e n).left * threeSpaceQuotientAction F (e n).right a =
      threeSpaceQuotientAction F (e n).right a * (e n).left :=
    (marked_rectangle_elementary F 3).is_comm.comm _ _
  rw [hcomm, mul_inv_cancel_right] at hl
  exact hl.symm

/-- Full source plane coordinates with both the kernel and the literal
successive quotient action retained. -/
theorem exists_threeSpace_semidirect_equiv_quotient (D : LocalData F) :
    ∃ e : threeSpaceNormalizer F ≃*
        F.threeSpace ⋊[threeSpaceQuotientAction F] threeSpaceQuotient F,
      (∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
        SemidirectProduct.inl a) ∧
      ∀ n, (e n).right = (QuotientGroup.mk n : threeSpaceQuotient F) := by
  obtain ⟨e, he⟩ := exists_threeSpace_semidirect_equiv F D
  exact ⟨e, he, threeSpace_semidirect_quotient F e he⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
