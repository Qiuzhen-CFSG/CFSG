module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneImage
public import Theory.GroupTheory.OddSubgroupLift
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Sylow

/-!
# Splitting the source rectangle normalizers

The normal order-three subgroup of the symmetric tensor factor acts without
nonidentity fixed points on the original rectangle. Lift that subgroup
through the literal normalizer quotient. Its inverse image is normal, and
the Sylow Frattini argument makes the lifted subgroup's normalizer a
supplement to the rectangle. The fixed-point calculation makes their
intersection trivial, giving an actual internal complement.

The opposite marking supplies the second rectangle splitting. Both apply
inside the normalizer-generated subgroup without assuming it is simple.
This proves the rectangle splitting used in Aschbacher, *Sporadic Groups*
(1994), 40.3 and 41.4, printed pp.218,222. Source generation, geometry,
and compatible local comparison remain separate obligations.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open PlaneCensus
variable {M B : Type*} [Group M] [Finite M] [Group B] [Finite B]
private theorem cubic_split (f : M →* B) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (q : B) (hq : orderOf q = 3)
    [(zpowers q).Normal]
    (hfix : ∀ c : M, f c = q → ∀ a ∈ f.ker, c * a = a * c → a = 1) :
    ∃ C : Subgroup M, Nat.card C = 3 ∧ C.map f = zpowers q ∧
      f.ker.IsComplement' (normalizer (C : Set M)) := by
  have hqcard : Nat.card (zpowers q) = 3 := by rw [Nat.card_zpowers, hq]
  obtain ⟨C, hC, hinj, hcard, hcover⟩ := f.exists_odd_subgroup_lift hf hker
    (zpowers q) (by rw [hqcard]; decide)
  rw [hqcard] at hcard
  have hd : Disjoint f.ker C := by
    apply disjoint_def.mpr
    intro x hx hxC
    exact congrArg Subtype.val (hinj (a₁ := ⟨x, hxC⟩) (a₂ := 1)
      (show f x = f 1 from (show f x = 1 from hx).trans f.map_one.symm))
  obtain ⟨c, hc, hfc⟩ := (show q ∈ C.map f from hC.symm ▸ mem_zpowers q)
  have hdisj : Disjoint f.ker (normalizer (C : Set M)) := by
    apply disjoint_def.mpr
    intro a ha han
    have hac : a*c*a⁻¹*c⁻¹ ∈ C := C.mul_mem
      ((mem_normalizer_iff.mp han c).mp hc) (C.inv_mem hc)
    have hak : a*c*a⁻¹*c⁻¹ ∈ f.ker := by
      change f (a*c*a⁻¹*c⁻¹) = 1
      simp only [map_mul, map_inv, show f a = 1 from ha, one_mul, inv_one, mul_one,
        mul_inv_cancel]
    have he : a*c*a⁻¹*c⁻¹ = 1 := disjoint_def.mp hd hak hac
    have he' : a*c = c*a := mul_inv_eq_one.mp (by
      simpa only [mul_inv_rev, mul_assoc] using he)
    exact hfix c hfc a ha he'.symm
  let R := (zpowers q).comap f
  change f.ker ⊔ C = R at hcover
  have hCR : C ≤ R := le_sup_right.trans_eq hcover
  have hRcard : Nat.card R = Nat.card f.ker * 3 := by
    rw [← hcover, card_sup_eq_mul_of_normalizes_of_disjoint f.ker C
      (by rw [f.ker.normalizer_eq_top]; exact le_top) hd, hcard]
  let C' := C.subgroupOf R
  have hCcard : Nat.card C' = 3 := (Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv).trans hcard
  have hi : C'.index = Nat.card f.ker := by
    have hh := C'.card_mul_index
    rw [hCcard, hRcard] at hh
    omega
  have hn : ¬ 3 ∣ C'.index := by
    rw [hi]
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 R := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hCcard)).toSylow hn
  have hs : normalizer (C : Set M) ⊔ f.ker = ⊤ := by
    have hh := P.normalizer_sup_eq_top
    change normalizer ((C.subgroupOf R).map R.subtype : Set M) ⊔ R = ⊤ at hh
    rw [map_subgroupOf_eq_of_le hCR, ← hcover, ← sup_assoc,
      sup_eq_left.mpr (C.le_normalizer.trans le_sup_left)] at hh
    exact hh
  refine ⟨C, hcard, hC, isComplement'_of_card_mul_and_disjoint ?_ hdisj⟩
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint f.ker (normalizer (C : Set M))
    (by rw [f.ker.normalizer_eq_top]; exact le_top) hdisj
  rw [sup_comm, hs, Nat.card_congr Subgroup.topEquiv.toEquiv] at hh
  exact hh.symm

private abbrev ThreeAut := (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)
private abbrev TensorGroup := ThreeAut × Equiv.Perm (Fin 3)
private def rotation : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private def cubic : TensorGroup := (1, rotation)
private theorem rotation_cube : rotation ^ 3 = 1 := by decide
private theorem rotation_ne : rotation ≠ 1 := by decide
private theorem cubic_order : orderOf cubic = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · exact Prod.ext (by simp [cubic]) rotation_cube
  · intro h
    exact rotation_ne (congrArg Prod.snd h)
private theorem rotation_conj : ∀ p : Equiv.Perm (Fin 3),
    ∃ i : Fin 3, p * rotation * p⁻¹ = rotation ^ i.val := by decide
private theorem cubic_normal : (zpowers cubic).Normal := by
  constructor
  intro x hx g
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  have hg : g * cubic * g⁻¹ ∈ zpowers cubic := by
    obtain ⟨i, hi⟩ := rotation_conj g.2
    have he : g * cubic * g⁻¹ = cubic ^ i.val := by
      apply Prod.ext
      · simp [cubic]
      · exact hi
    rw [he]
    exact pow_mem (mem_zpowers cubic) _
  have he : g * cubic ^ n * g⁻¹ = (g * cubic * g⁻¹) ^ n :=
    map_zpow (MulAut.conj g) cubic n
  rw [he]
  exact zpow_mem hg _

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)
private def tensorMap (hlinear : F.LinearFusion) : sourcePlaneNormalizer F →* TensorGroup :=
  ((PlaneTensor.quotientRankOneEquiv F hlinear).trans rankOneGroupEquivLinearSymmetric).toMonoidHom.comp (QuotientGroup.mk' _)
private theorem tensorMap_surjective (hlinear : F.LinearFusion) : Function.Surjective (tensorMap F hlinear) :=
  ((PlaneTensor.quotientRankOneEquiv F hlinear).trans rankOneGroupEquivLinearSymmetric).surjective.comp (QuotientGroup.mk'_surjective _)
private theorem tensorMap_ker (hlinear : F.LinearFusion) :
    (tensorMap F hlinear).ker = F.plane.subgroupOf (sourcePlaneNormalizer F) := by
  ext n
  change ((PlaneTensor.quotientRankOneEquiv F hlinear).trans rankOneGroupEquivLinearSymmetric) (QuotientGroup.mk n) = 1 ↔ _
  rw [((PlaneTensor.quotientRankOneEquiv F hlinear).trans rankOneGroupEquivLinearSymmetric).map_eq_one_iff, QuotientGroup.eq_one_iff]

private theorem tensorMap_cubic_fixed (hlinear : F.LinearFusion)
    (c : sourcePlaneNormalizer F) (hc : tensorMap F hlinear c = cubic)
    (a : sourcePlaneNormalizer F) (ha : a ∈ (tensorMap F hlinear).ker)
    (hca : c * a = a * c) : a = 1 := by
  rw [tensorMap_ker] at ha
  obtain ⟨x, hx⟩ := (PlaneTensor.sourceEquiv F).surjective ⟨a, ha⟩
  have hxe : PlaneTensor.element F x = (a : G) := congrArg Subtype.val hx
  let g := PlaneTensor.quotientRankOneEquiv F hlinear (QuotientGroup.mk c)
  have hg : rankOneGroupEquivLinearSymmetric g = cubic := hc
  have he : g.val x = x := by
    apply PlaneTensor.element_injective F
    rw [PlaneTensor.quotientRankOneEquiv_action, hxe]
    have hh := congrArg Subtype.val hca
    change (c : G)*(a : G) = (a : G)*(c : G) at hh
    rw [hh, mul_inv_cancel_right]
  have hz := rankOneGroup_cubic_fixed g hg x he
  apply Subtype.ext
  rw [← hxe, hz, PlaneTensor.element_zero]
  rfl

/-- The order-three tensor factor lifts to a subgroup whose actual normalizer
complements the marked plane in its full ambient normalizer. -/
theorem linear_plane_cubic_complement (hlinear : F.LinearFusion) :
    ∃ C : Subgroup (sourcePlaneNormalizer F), Nat.card C = 3 ∧
      (F.plane.subgroupOf (sourcePlaneNormalizer F)).IsComplement'
        (normalizer (C : Set (sourcePlaneNormalizer F))) := by
  let f := tensorMap F hlinear
  have hk : IsPGroup 2 f.ker := by
    apply IsPGroup.of_card (n := 6)
    rw [tensorMap_ker]
    exact (Nat.card_congr (subgroupOfEquivOfLe F.plane.le_normalizer).toEquiv).trans
      (source_plane_card F)
  let : Finite TensorGroup := Finite.of_surjective _ (tensorMap_surjective F hlinear)
  let := cubic_normal
  obtain ⟨C, hC, _, hs⟩ := cubic_split f (tensorMap_surjective F hlinear) hk
    cubic cubic_order (tensorMap_cubic_fixed F hlinear)
  rw [tensorMap_ker] at hs
  exact ⟨C, hC, hs⟩

/-- Source 40.3 gives an internal complement in the literal plane normalizer. -/
theorem linear_plane_normalizer_splits (hlinear : F.LinearFusion) :
    ∃ K : Subgroup (sourcePlaneNormalizer F),
      (F.plane.subgroupOf (sourcePlaneNormalizer F)).IsComplement' K := by
  obtain ⟨C, _, hC⟩ := linear_plane_cubic_complement F hlinear
  exact ⟨normalizer (C : Set _), hC⟩

/-- Opposite marking gives the original three-space splitting with its own denominator. -/
theorem linear_threeSpace_normalizer_splits (hlinear : F.LinearFusion) :
    ∃ K : Subgroup (sourceThreeSpaceNormalizer F),
      (F.threeSpace.subgroupOf (sourceThreeSpaceNormalizer F)).IsComplement' K := by
  have h := linear_plane_normalizer_splits (oppositeMarking F) (oppositeMarking_linearFusion F hlinear)
  change ∃ K : Subgroup (normalizer ((oppositeMarking F).plane : Set G)),
    ((oppositeMarking F).plane.subgroupOf (normalizer ((oppositeMarking F).plane : Set G))).IsComplement' K at h
  rw [oppositeMarking_plane F] at h
  exact h

/-- The 41.1 induction subgroup inherits both rectangle splittings. Its
simplicity is neither assumed nor needed. -/
theorem normalizerSpan_rectangle_splittings (hlinear : F.LinearFusion) :
    (∃ K : Subgroup (sourcePlaneNormalizer (normalizerSpanMarking F)),
      ((normalizerSpanMarking F).plane.subgroupOf
        (sourcePlaneNormalizer (normalizerSpanMarking F))).IsComplement' K) ∧
    (∃ K : Subgroup (sourceThreeSpaceNormalizer (normalizerSpanMarking F)),
      ((normalizerSpanMarking F).threeSpace.subgroupOf
        (sourceThreeSpaceNormalizer (normalizerSpanMarking F))).IsComplement' K) :=
  ⟨linear_plane_normalizer_splits (normalizerSpanMarking F) (normalizerSpan_linearFusion F hlinear),
    linear_threeSpace_normalizer_splits (normalizerSpanMarking F) (normalizerSpan_linearFusion F hlinear)⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
