module

public import Theory.ElementaryAbelian.ExtraspecialCommutatorPairing
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Splitting off an extraspecial two-subgroup

An extraspecial two-subgroup whose commutators with the ambient group lie in
its own center generates the ambient group together with its centralizer.
For each ambient element, its commutator homomorphism on the extraspecial
subgroup descends to the central quotient. Commutator duality represents this
functional by an inner element; dividing by that element gives the required
centralizing factor.

This is the binary case of Gorenstein, *Finite Groups*, Lemma 5.4.6.
-/

open Subgroup
open scoped commutatorElement

namespace Subgroup

private theorem central_of_sq_eq_one_in_normal_cyclic
    {G : Type*} [Group G] (Z : Subgroup G) [Finite Z] [Z.Normal] [IsCyclic Z]
    {z : G} (hz : z ∈ Z) (hz2 : z ^ 2 = 1) : z ∈ center G := by
  by_cases hz1 : z = 1
  · simpa only [hz1] using (center G).one_mem
  let a : Z := ⟨z, hz⟩
  have ha2 : orderOf a = 2 := orderOf_eq_prime (Subtype.ext hz2)
    (fun h => hz1 (congrArg Subtype.val h))
  apply mem_center_iff.mpr
  intro g
  let b : Z := ⟨g * z * g⁻¹, (inferInstance : Z.Normal).conj_mem z hz g⟩
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    change (g * z * g⁻¹) ^ 2 = 1
    have h := congrArg (MulAut.conj g) hz2
    simpa only [map_pow, map_one, MulAut.conj_apply] using h
  have hb1 : b ≠ 1 := by
    intro h
    have hval : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    have he : MulAut.conj g z = MulAut.conj g 1 := by
      simpa only [map_one, MulAut.conj_apply] using hval
    exact hz1 ((MulAut.conj g).injective he)
  have heq := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (orderOf_eq_prime hb2 hb1) ha2)
  change g * z * g⁻¹ = z at heq
  exact (mul_inv_eq_iff_eq_mul.mp heq)

/-- If an extraspecial binary subgroup has ambient commutators in a cyclic
normal subgroup which centralizes it and contains its center, those
commutators already lie in its own center. -/
public theorem commutator_le_center_image_of_extraspecial_two
    {G : Type*} [Group G] (E Z : Subgroup G)
    [IsExtraspecial 2 E] [Finite Z] [IsCyclic Z] [Z.Normal]
    (hEZ : (center E).map E.subtype ≤ Z)
    (hZE : Z ≤ centralizer (E : Set G))
    (hcomm : ⁅(⊤ : Subgroup G), E⁆ ≤ Z) :
    ⁅(⊤ : Subgroup G), E⁆ ≤ (center E).map E.subtype := by
  have hcenterPow (a : center E) : ((a : E) : G) ^ 2 = 1 := by
    have h := congrArg (fun x : center E => ((x : E) : G)) (pow_card_eq_one' (x := a))
    change ((a : E) : G) ^ Nat.card (center E) = 1 at h
    simpa only [IsExtraspecial.center_order_p 2 E] using h
  have hcenterCentral : (center E).map E.subtype ≤ center G := by
    rintro _ ⟨a, ha, rfl⟩
    exact central_of_sq_eq_one_in_normal_cyclic Z (hEZ (mem_map_of_mem E.subtype ha))
      (hcenterPow ⟨a, ha⟩)
  obtain ⟨z, hzne, _⟩ := (Nat.card_eq_two_iff' (1 : center E)).mp
    (IsExtraspecial.center_order_p 2 E)
  let zZ : Z := ⟨((z : E) : G), hEZ (mem_map_of_mem E.subtype z.property)⟩
  have hz2 : orderOf zZ = 2 := orderOf_eq_prime (Subtype.ext (hcenterPow z)) (by
    intro h
    have hval : ((z : E) : G) = 1 := congrArg Subtype.val h
    apply hzne
    exact Subtype.ext (Subtype.ext hval))
  apply commutator_le.mpr
  intro g _ e he
  let c : G := ⁅g, e⁆
  have hcZ : c ∈ Z := hcomm (commutator_mem_commutator (mem_top g) he)
  have hce : Commute c e := (hZE hcZ e he).symm
  have he2 : e ^ 2 ∈ (center E).map E.subtype := by
    let _ := IsExtraspecial.quotient_elementary_abelian 2 E
    have hq := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (E ⧸ center E))
      (QuotientGroup.mk' (center E) ⟨e, he⟩)
    rw [← map_pow] at hq
    have hm := (QuotientGroup.eq_one_iff (N := center E) _).mp hq
    exact mem_map_of_mem E.subtype hm
  have hconj : MulAut.conj g e = c * e := conj_eq_commutatorElement_mul
  have hconjSq : MulAut.conj g (e ^ 2) = e ^ 2 := by
    change g * e ^ 2 * g⁻¹ = e ^ 2
    rw [mem_center_iff.mp (hcenterCentral he2) g, mul_inv_cancel_right]
  have hc2 : c ^ 2 = 1 := by
    have hp : c ^ 2 * e ^ 2 = e ^ 2 := by
      rw [← hce.mul_pow, ← hconj, ← map_pow, hconjSq]
    exact mul_right_cancel (hp.trans (one_mul (e ^ 2)).symm)
  by_cases hc1 : c = 1
  · change c ∈ (center E).map E.subtype
    rw [hc1]
    exact ((center E).map E.subtype).one_mem
  · let cZ : Z := ⟨c, hcZ⟩
    have hcOrder : orderOf cZ = 2 := orderOf_eq_prime (Subtype.ext hc2)
      (fun h => hc1 (congrArg Subtype.val h))
    have heq : c = ((z : E) : G) := congrArg Subtype.val
      (IsCyclic.eq_of_orderOf_eq_two hcOrder hz2)
    change c ∈ (center E).map E.subtype
    rw [heq]
    exact mem_map_of_mem E.subtype z.property

/-- An extraspecial binary subgroup with central ambient commutators has its
centralizer as a supplement. Only the extraspecial subgroup need be finite. -/
public theorem sup_centralizer_eq_top_of_extraspecial_two
    {G : Type*} [Group G] (E : Subgroup G) [Finite E] [IsExtraspecial 2 E]
    (hcomm : ⁅(⊤ : Subgroup G), E⁆ ≤ (center E).map E.subtype) :
    E ⊔ centralizer (E : Set G) = ⊤ := by
  let Z : Subgroup G := (center E).map E.subtype
  let : E.Normal := normalizer_eq_top_iff.mp (top_unique
    (le_normalizer_iff_commutator_le_right.mpr (hcomm.trans (map_subtype_le _))))
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcard : Nat.card Z = 2 :=
    (card_map_of_injective E.subtype_injective).trans (IsExtraspecial.center_order_p 2 E)
  have hZcentral : Z ≤ center G := central_of_normal_card_two Z hZcard
  let eZ : center E ≃* Z := (center E).equivMapOfInjective E.subtype E.subtype_injective
  apply top_unique
  intro g _
  have hmem (e : E) : ⁅g, (e : G)⁆ ∈ Z :=
    hcomm (commutator_mem_commutator (mem_top g) e.property)
  let raw : E →* Z := {
    toFun e := ⟨⁅g, (e : G)⁆, hmem e⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅g, (a : G) * (b : G)⁆ = ⁅g, (a : G)⁆ * ⁅g, (b : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj,
        mul_assoc ⁅g, (a : G)⁆ (a : G) ⁅g, (b : G)⁆,
        mem_center_iff.mp (hZcentral (hmem b)) (a : G)]
      simp only [← mul_assoc, mul_inv_cancel_right] }
  let discrepancy : E →* center E := eZ.symm.toMonoidHom.comp raw
  have hkill : center E ≤ discrepancy.ker := by
    intro z hz
    have hzZ : (z : G) ∈ Z := mem_map_of_mem E.subtype hz
    have heq : raw z = 1 := by
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_center_iff.mp (hZcentral hzZ) g)
    change eZ.symm (raw z) = 1
    rw [heq, map_one]
  let functional : (E ⧸ center E) →* center E :=
    QuotientGroup.lift (center E) discrepancy hkill
  obtain ⟨r, hr⟩ := extraspecial_two_commutator_represents_hom functional
  have hmatch (e : E) : ⁅g, (e : G)⁆ = ⁅(r : G), (e : G)⁆ := by
    have h := congrArg (fun x : E => (x : G)) (hr e)
    have heval : ((eZ.symm (raw e) : center E) : G) = ⁅g, (e : G)⁆ := by
      exact congrArg (fun z : Z => (z : G)) (eZ.apply_symm_apply (raw e))
    exact heval.symm.trans h
  have hc : (r : G)⁻¹ * g ∈ centralizer (E : Set G) := by
    intro e he
    have h := hmatch ⟨e, he⟩
    have hconj : g * e * g⁻¹ = (r : G) * e * (r : G)⁻¹ := by
      have hh := congrArg (fun x : G => x * e) h
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    have hh := congrArg (fun x : G => (r : G)⁻¹ * x * g) hconj
    have heq : (r : G)⁻¹ * g * e = e * ((r : G)⁻¹ * g) := by
      simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, inv_mul_cancel_left,
        mul_one, one_mul] using hh
    exact heq.symm
  have hm := (E ⊔ centralizer (E : Set G)).mul_mem
    ((le_sup_left : E ≤ E ⊔ centralizer (E : Set G)) r.property)
    ((le_sup_right : centralizer (E : Set G) ≤ E ⊔ centralizer (E : Set G)) hc)
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hm

/-- An extraspecial normal subgroup with central ambient commutators and
cyclic quotient supplements the ambient center. -/
public theorem sup_center_eq_top_of_extraspecial_two_of_cyclic_quotient
    {G : Type*} [Group G] (E : Subgroup G) [Finite E] [E.Normal]
    [IsExtraspecial 2 E] [IsCyclic (G ⧸ E)]
    (hcomm : ⁅(⊤ : Subgroup G), E⁆ ≤ (center E).map E.subtype) :
    E ⊔ center G = ⊤ := by
  let C := centralizer (E : Set G)
  have hsup : E ⊔ C = ⊤ := sup_centralizer_eq_top_of_extraspecial_two E hcomm
  let f : C →* G ⧸ E := (QuotientGroup.mk' E).comp C.subtype
  have hker : f.ker ≤ center C := by
    intro x hx
    have hxE : (x : G) ∈ E := (QuotientGroup.eq_one_iff (N := E) _).mp hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (y.property (x : G) hxE).symm
  have hCcomm : IsMulCommutative C :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have hCC : C ≤ centralizer (C : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr hCcomm
  have hCZ : C ≤ center G := by
    have ht : (⊤ : Subgroup G) ≤ centralizer (C : Set G) := by
      rw [← hsup]
      exact sup_le (le_centralizer_iff.mp le_rfl) hCC
    have hct := le_centralizer_iff.mp ht
    simpa only [coe_top, centralizer_univ] using hct
  exact top_unique (hsup ▸ sup_le_sup_left hCZ E)

end Subgroup
