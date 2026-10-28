module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.AmbientElementary
public import Theory.GroupTheory.FusedFourTransport

/-!
# Central involution fusion and the two possible normalizer orders

A conjugate of the marked involution lying in E is central in an ambient
Sylow two-subgroup containing E. Janko's elementary-sixteen normality
lemma places that Sylow subgroup inside N(E). Sylow conjugacy in N(E)
and uniqueness of the involution in its cyclic Sylow center therefore
realize the conjugacy inside N(E).

The six distinct local conjugates of printed z₃ then lie in the marked
N(E)-orbit. The existing orbit-stabilizer and divisibility calculation
excludes the orders 24, 72, and 120, leaving 168 or 360. This does not
identify either remaining abstract quotient. It replaces the source's
small-order exclusions with its concrete Case II action and Sylow data.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemmas 1 and 6, pp.4–6.
-/

open Subgroup
open scoped Pointwise

private theorem fuse_centers {K : Type*} [Group K] [Finite K] (S T : Sylow 2 K)
    [IsCyclic (center S)] (z : center S) (hz : orderOf z = 2)
    (x : center T) (hx : orderOf x = 2) :
    IsConj ((z : S) : K) ((x : T) : K) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K S T
  let f := centerCongr (S.equivSMul g)
  have heq : f.symm x = z := IsCyclic.eq_of_orderOf_eq_two
    ((f.symm.orderOf_eq x).trans hx) hz
  exact isConj_iff.mpr ⟨g, congrArg
    (fun a : center ↥(g • S : Sylow 2 K) => ((a : ↥(g • S : Sylow 2 K)) : K))
    ((f.symm_apply_eq.mp heq).symm)⟩

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Ambient conjugacy of the marked involution into E is realized in N(E). -/
public theorem E_normalizer_fusion_of_isConj (x : E D k) (hx : IsConj D.z (x : G)) :
    ∃ n : normalizer (E D k : Set G), (n : G) * D.z * (n : G)⁻¹ = x := by
  let N := normalizer (E D k : Set G)
  have hTN : (D.sylow : Subgroup G) ≤ N :=
    D.sylow_le_centralizer.trans (centralizer_le_normalizer_E D k)
  let := E_elementary D k
  have hEC : E D k ≤ centralizer ({(x : G)} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy x.property)
  have hp : IsPGroup 2 (E D k) := IsPGroup.of_card (n := 4) (by simpa using E_card D k)
  obtain ⟨g, hgT, hgx⟩ := D.sylow.transport_centralizing_two_subgroup
    (D.involution : D.sylow) D.involution.property x hx.symm (E D k) hp hEC
  change (MulAut.conj g) (x : G) = D.z at hgx
  let P : Sylow 2 G := g⁻¹ • D.sylow
  have hEP : E D k ≤ P := by
    intro y hy
    change y ∈ (D.sylow : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom
    refine ⟨(MulAut.conj g) y, hgT (mem_map_of_mem _ hy), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hPC : (P : Subgroup G) ≤ centralizer ({(x : G)} : Set G) := by
    rintro y ⟨t, ht, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have htC := mem_centralizer_singleton_iff.mp (D.sylow_le_centralizer ht)
    have hh := congrArg (MulAut.conj g⁻¹) htC
    have hgx' : (MulAut.conj g⁻¹) D.z = x := by
      rw [← hgx]; simp [MulAut.conj_apply, mul_assoc]
    change (MulAut.conj g⁻¹) t * (x : G) = (x : G) * (MulAut.conj g⁻¹) t
    simpa only [map_mul, hgx'] using hh
  have hPN : (P : Subgroup G) ≤ N := (normal_subgroupOf_iff_le_normalizer hEP).mp
    (elementary_sixteen_normal_in_sylow D k P (E D k) hEP (E_elementary D k) (E_card D k))
  let S := D.sylow.subtype hTN
  let R := P.subtype hPN
  let e : S ≃* D.sylow := subgroupOfEquivOfLe hTN
  let : IsCyclic (center S) := by
    let := D.cyclic_center
    exact isCyclic_of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  let zS : center S := (centerCongr e).symm D.involution
  let xR : center R := ⟨⟨⟨x, (E D k).le_normalizer x.property⟩, hEP x.property⟩,
    mem_center_iff.mpr (fun y => Subtype.ext (Subtype.ext
      (mem_centralizer_singleton_iff.mp (hPC y.property))))⟩
  have hx2 : orderOf (x : G) = 2 := by
    rw [← (MulAut.conj g).orderOf_eq, hgx, D.z_order]
  have hc := fuse_centers S R zS (by
    rw [MulEquiv.orderOf_eq]; exact D.involution_order) xR (by
    let f : center R →* G := N.subtype.comp
      ((R : Subgroup N).subtype.comp (center R).subtype)
    have hf : Function.Injective f := Subtype.coe_injective.comp
      (Subtype.coe_injective.comp Subtype.coe_injective)
    exact (orderOf_injective f hf xR).symm.trans hx2)
  obtain ⟨n, hn⟩ := isConj_iff.mp hc
  exact ⟨n, congrArg Subtype.val hn⟩

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))

private def z3Conjugate : Fin 6 → TwistedModel :=
  ![z 2, z 3, z 2 * z 3, z 0 * z 2, z 0 * z 3, z 0 * z 2 * z 3]

private theorem z3Conjugate_injective : Function.Injective z3Conjugate := by
  decide +kernel

private theorem z3Conjugate_mem : ∀ i, z3Conjugate i ∈ modelE := by
  decide +kernel

private theorem z3Conjugate_witness : ∀ i, ∃ s : SymmetricFour,
    (SemidirectProduct.inr s : TwistedModel) * z 2 *
      (SemidirectProduct.inr s : TwistedModel)⁻¹ = z3Conjugate i := by
  decide +kernel

/-- Printed z₃ has six distinct conjugates already in the marked centralizer. -/
public theorem eNormalizerPoint_orbit_card_ge_six
    (hz3 : IsConj D.z (into D k (z 2))) :
    6 ≤ (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k)).ncard := by
  let y : E D k := ⟨into D k (z 2), by
    rw [← modelE_map D k]; exact mem_map_of_mem _ (z_mem_modelE 2)⟩
  obtain ⟨n, hn⟩ := E_normalizer_fusion_of_isConj D k y hz3
  let v (i : Fin 6) : E D k := ⟨into D k (z3Conjugate i), by
    rw [← modelE_map D k]; exact mem_map_of_mem _ (z3Conjugate_mem i)⟩
  have hv (i : Fin 6) : v i ∈
      MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) := by
    obtain ⟨s, hs⟩ := z3Conjugate_witness i
    let t : normalizer (E D k : Set G) := ⟨into D k (SemidirectProduct.inr s),
      centralizer_le_normalizer_E D k (k (SemidirectProduct.inr s)).property⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨t * n, Subtype.ext ?_⟩
    change ((t : G) * (n : G)) * D.z * ((t : G) * (n : G))⁻¹ = into D k (z3Conjugate i)
    calc
      _ = (t : G) * ((n : G) * D.z * (n : G)⁻¹) * (t : G)⁻¹ := by group
      _ = into D k (SemidirectProduct.inr s) * into D k (z 2) *
          (into D k (SemidirectProduct.inr s))⁻¹ := by rw [hn]
      _ = into D k (z3Conjugate i) := by rw [← map_inv, ← map_mul, ← map_mul, hs]
  let f (i : Fin 6) : MulAction.orbit (normalizer (E D k : Set G))
      (eNormalizerPoint D k) := ⟨v i, hv i⟩
  have hf : Function.Injective f := by
    intro i j h
    apply z3Conjugate_injective
    apply into_injective D k
    exact congrArg (fun a : MulAction.orbit (normalizer (E D k : Set G))
      (eNormalizerPoint D k) => ((a : E D k) : G)) h
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

/-- The genuine initial fusion reduces the quotient orders to 168 and 360. -/
public theorem eNormalizerQuotient_card_cases_of_z3
    (hz3 : IsConj D.z (into D k (z 2))) :
    Nat.card (eNormalizerQuotient D k) = 168 ∨
      Nat.card (eNormalizerQuotient D k) = 360 := by
  have hge := eNormalizerPoint_orbit_card_ge_six D k hz3
  have hc := eNormalizerQuotient_card D k
  rcases eNormalizerQuotient_card_cases D k with h | h | h | h | h <;> omega

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
