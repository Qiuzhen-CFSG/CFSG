module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.Nonfusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionConstruction.LocalGeometry
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# An order-three stabilizer of the intersection in the order-168 branch

Put V = E ∩ F and S = N_G(E) ∩ N_G(V). The eight local conjugates of
printed z₂ exhaust its N_G(E)-orbit. Their complement is therefore
invariant. In the binary model it contains exactly seven multiplicatively
closed four-point sets containing the identity, one of which is V.
Transporting this finite geometry through the actual model equivalence
gives [N_G(E) : S] ≤ 7, hence |S| ≥ 2688 / 7 = 384.

The conjugation action of S on the four elements of V has kernel C_G(V),
of order 64 and contained in S. Its image is a subgroup of the permutation
group of degree four, so |S| divides 64 · 24. It also divides |N_G(E)| =
2688, and gcd(64 · 24, 2688) = 384. Thus |S| = 384, and Cauchy's theorem
supplies an actual element of order three normalizing E and V.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.7. This constructs the
intersection-stabilizing actor used there directly from the quotient order;
its fixed subgroup on E is treated separately. The model enumerations
below are checked by kernel reduction.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))

private def oddPoints : Finset modelE := Finset.univ.filter fun x =>
  ∃ s : SymmetricFour,
    (x : TwistedModel) = (SemidirectProduct.inr s : TwistedModel) * z 1 *
      (SemidirectProduct.inr s)⁻¹

private def evenPoints : Finset modelE := Finset.univ \ oddPoints

private def planes : Finset (Finset modelE) :=
  (evenPoints.powersetCard 4).filter fun s =>
    1 ∈ s ∧ ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s

private theorem oddPoints_card : oddPoints.card = 8 := by decide +kernel

private theorem planes_card : planes.card = 7 := by decide +kernel

private def intersectionPoints : Finset modelE :=
  Finset.univ.filter fun x => (x : TwistedModel) * d = d * x

private theorem intersectionPoints_mem_planes : intersectionPoints ∈ planes := by decide +kernel

private theorem mem_intersectionPoints (x : modelE) :
    x ∈ intersectionPoints ↔ (x : TwistedModel) ∈ modelF := by
  simp only [intersectionPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_centralizer_singleton_iff.symm

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

private noncomputable def coordinates : modelE ≃* E D k :=
  (modelE.equivMapOfInjective (into D k) (into_injective D k)).trans
    (MulEquiv.subgroupCongr (modelE_map D k))

private noncomputable def action : normalizer (E D k : Set G) →* MulAut modelE :=
  (MulAut.congr (coordinates D k).symm).toMonoidHom.comp (E D k).normalizerMonoidHom

private noncomputable local instance : MulDistribMulAction (normalizer (E D k : Set G)) modelE :=
  MulDistribMulAction.compHom modelE (action D k)

private theorem coordinates_smul (g : normalizer (E D k : Set G)) (x : modelE) :
    coordinates D k (g • x) = g • coordinates D k x := by
  change coordinates D k ((coordinates D k).symm (_)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem smul_apply (g : normalizer (E D k : Set G)) (x : modelE) :
    into D k ((g • x : modelE) : TwistedModel) =
      (g : G) * into D k x * (g : G)⁻¹ :=
  congrArg Subtype.val (coordinates_smul D k g x)

private theorem oddPoints_subset_orbit : (oddPoints : Set modelE) ⊆
    MulAction.orbit (normalizer (E D k : Set G)) (⟨z 1, z_mem_modelE 1⟩ : modelE) := by
  intro x hx
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hx).2
  let a := (SemidirectProduct.inr s : TwistedModel)
  let g : normalizer (E D k : Set G) :=
    ⟨into D k a, centralizer_le_normalizer_E D k (k a).property⟩
  refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
  apply Subtype.ext
  apply into_injective D k
  rw [smul_apply]
  change into D k a * into D k (z 1) * (into D k a)⁻¹ = into D k x
  rw [hs]
  simp only [map_mul, map_inv]
  rfl

variable [Finite G]

private theorem oddPoints_eq_orbit
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    (oddPoints : Set modelE) =
      MulAction.orbit (normalizer (E D k : Set G)) (⟨z 1, z_mem_modelE 1⟩ : modelE) := by
  apply Set.eq_of_subset_of_ncard_le (oddPoints_subset_orbit D k)
  let N := normalizer (E D k : Set G)
  let O := MulAction.orbit N (⟨z 1, z_mem_modelE 1⟩ : modelE)
  let O' := MulAction.orbit N (eNormalizerZOnePoint D k)
  let f : O → O' := fun x => ⟨coordinates D k x, by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp x.property
    refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
    rw [← hg, coordinates_smul]
    rfl⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext ((coordinates D k).injective (congrArg Subtype.val h))
  have hc := Nat.card_le_card_of_injective f hf
  change O.ncard ≤ O'.ncard at hc
  rw [eNormalizerZOnePoint_orbit_card_of_168 D k h168] at hc
  simpa only [Set.ncard_coe_finset, oddPoints_card] using hc

private theorem evenPoints_invariant
    (h168 : Nat.card (eNormalizerQuotient D k) = 168)
    (g : normalizer (E D k : Set G)) : g • evenPoints = evenPoints := by
  have ho : g • oddPoints = oddPoints := by
    apply Finset.coe_injective
    rw [Finset.coe_smul_finset, oddPoints_eq_orbit D k h168, MulAction.smul_orbit]
  rw [evenPoints, Finset.smul_finset_sdiff, Finset.smul_finset_univ, ho]

private theorem planes_invariant
    (h168 : Nat.card (eNormalizerQuotient D k) = 168)
    (g : normalizer (E D k : Set G)) {s : Finset modelE} (hs : s ∈ planes) :
    g • s ∈ planes := by
  obtain ⟨hs', h1, hmul⟩ := (Finset.mem_filter.mp hs)
  obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hs'
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← evenPoints_invariant D k h168 g]
    exact Finset.smul_finset_subset_smul_finset_iff.mpr hsub
  · rw [Finset.card_smul_finset, hc]
  · simpa only [smul_one] using (Finset.smul_mem_smul_finset_iff g).mpr h1
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.mp hy
    rw [← smul_mul']
    exact (Finset.smul_mem_smul_finset_iff g).mpr (hmul a ha b hb)

private theorem plane_stabilizer_index_le
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    (MulAction.stabilizer (normalizer (E D k : Set G)) intersectionPoints).index ≤ 7 := by
  rw [MulAction.index_stabilizer]
  have hs : MulAction.orbit (normalizer (E D k : Set G)) intersectionPoints ⊆
      (planes : Set (Finset modelE)) := by
    intro s hs
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hs
    exact planes_invariant D k h168 g intersectionPoints_mem_planes
  have hc := Set.ncard_le_ncard hs
  simpa only [Set.ncard_coe_finset, planes_card] using hc

omit [Finite G] in
private theorem mem_intersectionPoints_iff (x : modelE) :
    x ∈ intersectionPoints ↔ into D k x ∈ E D k ⊓ F D k := by
  rw [mem_intersectionPoints]
  have he : into D k x ∈ E D k := (coordinates D k x).property
  simp only [mem_inf, he, true_and]
  rw [← modelF_map D k]
  exact (mem_map_iff_mem (into_injective D k)).symm

omit [Finite G] in
private theorem plane_stabilizer_eq :
    MulAction.stabilizer (normalizer (E D k : Set G)) intersectionPoints =
      (normalizer ((E D k ⊓ F D k : Subgroup G) : Set G)).subgroupOf
        (normalizer (E D k : Set G)) := by
  ext n
  rw [MulAction.mem_stabilizer_iff]
  change n • intersectionPoints = intersectionPoints ↔
    (n : G) ∈ normalizer ((E D k ⊓ F D k : Subgroup G) : Set G)
  constructor
  · intro hn
    have hm (x : modelE) : x ∈ intersectionPoints ↔ n • x ∈ intersectionPoints := by
      have h := Finset.smul_mem_smul_finset_iff n (b := x) (s := intersectionPoints)
      rw [hn] at h
      exact h.symm
    apply mem_normalizer_iff.mpr
    intro y
    by_cases hy : y ∈ E D k
    · obtain ⟨x, hx⟩ := (coordinates D k).surjective ⟨y, hy⟩
      have hx' : into D k x = y := congrArg Subtype.val hx
      have h := hm x
      rw [mem_intersectionPoints_iff D k, mem_intersectionPoints_iff D k,
        smul_apply D k, hx'] at h
      exact h
    · have hy' : (n : G) * y * (n : G)⁻¹ ∉ E D k :=
        fun h => hy ((mem_normalizer_iff.mp n.property y).mpr h)
      simp only [mem_inf, hy, hy', false_and]
  · intro hn
    apply Finset.ext
    intro y
    obtain ⟨x, rfl⟩ := MulAction.surjective n y
    rw [Finset.smul_mem_smul_finset_iff, mem_intersectionPoints_iff D k,
      mem_intersectionPoints_iff D k, smul_apply D k]
    exact mem_normalizer_iff.mp hn _

private theorem intersection_stabilizer_card_dvd :
    Nat.card (normalizer (E D k : Set G) ⊓
      normalizer ((E D k ⊓ F D k : Subgroup G) : Set G) : Subgroup G) ∣ 1536 := by
  let V := E D k ⊓ F D k
  let N := normalizer (E D k : Set G)
  let S := N ⊓ normalizer (V : Set G)
  let C := centralizer (V : Set G)
  have hCS : C ≤ S := le_inf
    ((l27_intersection_centralizer_le D k).trans (caseIISylow_le_normalizer_E D k))
    (centralizer_le_normalizer _)
  let r : S →* MulAut V := V.normalizerMonoidHom.comp (inclusion inf_le_right)
  let f : S →* Equiv.Perm V := (MulAut.toPerm V).comp r
  have hk : f.ker = C.subgroupOf S := by
    rw [MonoidHom.ker_comp_of_injective _ _ MulEquiv.toEquiv_injective]
    ext s
    change V.normalizerMonoidHom (inclusion (show S ≤ normalizer (V : Set G) from
      inf_le_right) s) = 1 ↔ (s : G) ∈ C
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  have hc : Nat.card f.ker = 64 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hCS).toEquiv]
    exact l27_intersection_centralizer_card D k
  have hd := f.range.card_subgroup_dvd_card
  rw [Nat.card_perm, show Nat.card V = 4 from l27_intersection_card D k] at hd
  have he := f.ker.card_mul_index
  rw [index_ker, hc] at he
  change Nat.card S ∣ 1536
  rw [← he]
  exact Nat.mul_dvd_mul_left 64 hd

/-- The stabilizer of the actual intersection inside N(E) has order 384. -/
public theorem l27_intersection_stabilizer_card
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    Nat.card (normalizer (E D k : Set G) ⊓
      normalizer ((E D k ⊓ F D k : Subgroup G) : Set G) : Subgroup G) = 384 := by
  let N := normalizer (E D k : Set G)
  let H := normalizer ((E D k ⊓ F D k : Subgroup G) : Set G)
  let S := N ⊓ H
  have he : Nat.card (H.subgroupOf N) = Nat.card S := by
    rw [← inf_subgroupOf_left H N]
    exact Nat.card_congr (subgroupOfEquivOfLe (show S ≤ N from inf_le_left)).toEquiv
  have hi : (H.subgroupOf N).index ≤ 7 := by
    rw [← plane_stabilizer_eq D k]
    exact plane_stabilizer_index_le D k h168
  have hm := (H.subgroupOf N).card_mul_index
  rw [he, eNormalizer_card_of_168 D k h168] at hm
  have hl : 2688 ≤ Nat.card S * 7 := by
    rw [← hm]
    exact Nat.mul_le_mul_left _ hi
  have hdN : Nat.card S ∣ 2688 := by
    rw [← eNormalizer_card_of_168 D k h168]
    exact card_dvd_of_le (show S ≤ N from inf_le_left)
  have hd := Nat.dvd_gcd hdN (intersection_stabilizer_card_dvd D k)
  norm_num at hd
  have hu := Nat.le_of_dvd (by decide : 0 < 384) hd
  change Nat.card S = 384
  omega

/-- The order-168 branch supplies an element of order three normalizing
both E and its actual intersection with F. -/
public theorem l27_exists_intersection_actor
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    ∃ q : G, q ∈ normalizer (E D k : Set G) ∧
      q ∈ normalizer ((E D k ⊓ F D k : Subgroup G) : Set G) ∧ orderOf q = 3 := by
  let S := normalizer (E D k : Set G) ⊓
    normalizer ((E D k ⊓ F D k : Subgroup G) : Set G)
  have hd : 3 ∣ Nat.card S := by
    rw [l27_intersection_stabilizer_card D k h168]
    decide
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 hd
  exact ⟨q, q.property.1, q.property.2,
    (orderOf_injective S.subtype Subtype.val_injective q).trans hq⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
