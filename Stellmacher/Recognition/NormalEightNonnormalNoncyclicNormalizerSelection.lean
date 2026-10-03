module

public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicRotationSetup
public import Theory.GroupTheory.SymmetricThreeQuotientInverter
public import Theory.GroupTheory.PGroup.LargeHallOrderThreeFactors
public import Theory.GroupTheory.SylowIndexThreeNormalizerCover

/-!
# Odd subgroups adapted to an outside involution

The odd automorphism bound makes the actual quotient Sylow have index three.
Since its two-core has relative index two, the quotient by that core is S₃.
The product-of-involutions construction then supplies a subgroup of order
three inverted by the supplied outside involution. Thus choosing an adapted
odd subgroup does not require changing that involution or assuming that the
original central-product factors are invariant.

The adapted Hall factor is exactly the fixed subgroup of the order-three
action. Transporting this identity through the actual core equivalence
identifies its extension by the outside involution with the odd-subgroup
normalizer in the Sylow group. The index-three normalizer cover then captures
every outside involution up to conjugacy inside that Sylow group.

This assembles the local normalizer selection of Janko–Thompson, Math. Z. 113
(1970), §4, Case 1, printed p.392 (PDF page 8), after “Choose z₁”.
Source: refs/original/n-group-global/odd-core-rank-two-source/
janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- In the large noncyclic case the actual quotient Sylow has index three,
and the quotient by its two-core is S₃. -/
public theorem omegaQuotient_symmetric_three_of_large_noncyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2) :
    (omegaQuotientSylow S : Subgroup (OmegaQuotient S)).index = 3 ∧
      Nonempty ((OmegaQuotient S ⧸ pCore 2 (OmegaQuotient S)) ≃*
        Equiv.Perm (Fin 3)) := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  have hdvd := omegaQuotientSylow_index_dvd_three_of_odd_automorphisms hN S hZ
    (odd_automorphism_card_dvd_three_of_large_hall_central_product
      pCore_isPGroup B D hB hD hn hc hg hlarge)
  have hle : pCore 2 (OmegaQuotient S) ≤ omegaQuotientSylow S :=
    pCore_isPGroup.le_sylow_of_normal _
  have hproper : pCore 2 (OmegaQuotient S) <
      (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) := by
    apply lt_of_le_of_ne hle
    intro he
    rw [index_omegaCorePreimage, he, relIndex_self] at hi
    contradiction
  have hindex : (omegaQuotientSylow S : Subgroup (OmegaQuotient S)).index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · have ht : (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) = ⊤ :=
        index_eq_one.mp h
      have hnormalT : (omegaQuotientSylow S : Subgroup (OmegaQuotient S)).Normal :=
        ht ▸ inferInstance
      exact (hproper.not_ge (le_sSup ⟨hnormalT, (omegaQuotientSylow S).isPGroup'⟩)).elim
    · exact h
  exact ⟨hindex, sylow_index_three_core_quotient (omegaQuotientSylow S) hindex hproper⟩

/-- The supplied outside involution inverts a subgroup of order three in
the actual odd-core quotient. -/
public theorem exists_inverted_three_in_omegaQuotient
    (S : Sylow 2 G)
    (he : Nonempty ((OmegaQuotient S ⧸ pCore 2 (OmegaQuotient S)) ≃*
      Equiv.Perm (Fin 3)))
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S) :
    ∃ Q : Subgroup (OmegaQuotient S), Nat.card Q = 3 ∧
      ∀ q ∈ Q, omegaQuotientHom S t * q * (omegaQuotientHom S t)⁻¹ = q⁻¹ := by
  apply exists_inverted_three_of_symmetric_three_quotient
    (pCore 2 (OmegaQuotient S)) pCore_isPGroup he (omegaQuotientHom S t)
  · exact (orderOf_injective (omegaQuotientHom S) (omegaQuotientHom_injective S) t).trans ht
  · exact hout

/-- The inverted three-subgroup acts faithfully on the actual two-core,
so its generator gives an automorphism of order three. -/
public theorem exists_inverted_three_automorphism_in_omegaQuotient
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (he : Nonempty ((OmegaQuotient S ⧸ pCore 2 (OmegaQuotient S)) ≃*
      Equiv.Perm (Fin 3)))
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S) :
    ∃ q : OmegaQuotient S, orderOf q = 3 ∧
      orderOf ((MulAut.conjNormal : OmegaQuotient S →*
        MulAut (pCore 2 (OmegaQuotient S))) q) = 3 ∧
      omegaQuotientHom S t * q * (omegaQuotientHom S t)⁻¹ = q⁻¹ := by
  obtain ⟨Q, hQ, hinv⟩ := exists_inverted_three_in_omegaQuotient S he t ht hout
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [hQ])
  have hinj := odd_subgroup_conj_twoCore_injective
    (omegaQuotient_centralizer_pCore_le hN S hZ) Q
    (by rw [hQ]; decide)
  exact ⟨q, (Subgroup.orderOf_coe q).trans hq,
    (orderOf_injective _ hinj q).trans hq, hinv q q.property⟩

/-- Any quaternion factor and large Hall tail in the actual core already
generate the rotation quotient together with an outside element. This uses
no invariance of the chosen factors under that element. -/
public theorem noncyclicRotationPreimage_sup_hall_extension_eq_top
    (S : Sylow 2 G) (hi : (omegaCorePreimage S).index = 2)
    (B D : Subgroup (omegaCorePreimage S))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (hc : D ≤ centralizer (B : Set (omegaCorePreimage S))) (hg : B ⊔ D = ⊤)
    (v : S) (hout : v ∉ omegaCorePreimage S) :
    noncyclicRotationPreimage S ⊔ (D.map (omegaCorePreimage S).subtype ⊔ zpowers v) = ⊤ := by
  let H := omegaCorePreimage S
  let K := closure {x : H | x ^ 4 ≠ 1}
  obtain ⟨r, hr, -⟩ := IsBinaryHallFactor.exists_large_rotation
    ((S.isPGroup'.to_subgroup H).to_subgroup D) hD hn hlarge
  have hr4 : (r : H) ^ 4 ≠ 1 := by
    intro heq
    have hd : orderOf r ∣ 4 := orderOf_dvd_of_pow_eq_one (Subtype.ext heq)
    have : 8 ∣ 4 := hr.trans hd
    norm_num at this
  have hBK : B ≤ K := by
    obtain ⟨e⟩ := hB
    intro b hb
    have hb4 : b ^ 4 = 1 := by
      have he4 : e ⟨b, hb⟩ ^ 4 = 1 := by
        exact (by decide : ∀ q : QuaternionGroup 2, q ^ 4 = 1) _
      have hh : (⟨b, hb⟩ : B) ^ 4 = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        exact he4
      exact congrArg Subtype.val hh
    have hcomm : Commute b (r : H) := hc r.property b hb
    have hbr : b * (r : H) ∈ K := subset_closure (by
      change (b * (r : H)) ^ 4 ≠ 1
      rwa [hcomm.mul_pow, hb4, one_mul])
    have hrK : (r : H) ∈ K := subset_closure hr4
    simpa using K.mul_mem hbr (K.inv_mem hrK)
  have hH : H ≤ noncyclicRotationPreimage S ⊔ D.map H.subtype := by
    have hKD : K ⊔ D = ⊤ := top_unique (hg ▸ sup_le_sup_right hBK D)
    have hm := congrArg (fun U : Subgroup H => U.map H.subtype) hKD
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, H.range_subtype] at hm
    exact hm.ge
  let L := noncyclicRotationPreimage S ⊔ (D.map H.subtype ⊔ zpowers v)
  have hHL : H ≤ L := hH.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  have hvL : v ∈ L :=
    ((le_sup_right : zpowers v ≤ D.map H.subtype ⊔ zpowers v).trans le_sup_right)
      (mem_zpowers v)
  have hvH : v ∉ H := hout
  apply top_unique
  intro x _
  by_cases hx : x ∈ H
  · exact hHL hx
  · have hxv : x * v⁻¹ ∈ H := (H.mul_mem_iff_of_index_two hi).mpr (by
      simp only [hx, inv_mem_iff, hvH])
    simpa using L.mul_mem (hHL hxv) hvL

/-- Choose quaternion and large Hall factors adapted to an odd complement.
The supplied outside involution can be retained. Its Hall extension generates
the rotation quotient and contains a Sylow conjugate of every outside
involution. No invariance of the originally supplied factors is assumed. -/
public theorem exists_noncyclic_hall_normalizer_cover
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2)
    (z t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G)) :
    ∃ v : S, ∃ B₀ D₀ : Subgroup (omegaCorePreimage S),
      orderOf v = 2 ∧ v ∉ omegaCorePreimage S ∧ IsConj (z : G) (v : G) ∧
      B₀.Normal ∧ D₀.Normal ∧ Nonempty (B₀ ≃* QuaternionGroup 2) ∧
      IsBinaryHallFactor D₀ ∧ ¬ IsCyclic D₀ ∧ 16 ≤ Nat.card D₀ ∧
      D₀ ≤ centralizer (B₀ : Set (omegaCorePreimage S)) ∧ B₀ ⊔ D₀ = ⊤ ∧
      let D₁ := D₀.map (omegaCorePreimage S).subtype
      let L := D₁ ⊔ zpowers v
      v ∈ normalizer (D₁ : Set S) ∧ noncyclicRotationPreimage S ⊔ L = ⊤ ∧
        ∀ u : S, orderOf u = 2 → u ∉ omegaCorePreimage S →
          ∃ w : L, IsConj u (w : S) := by
  let H := omegaCorePreimage S
  -- Restrict the canonical quotient map, retaining its pointwise specification.
  let e : H ≃* pCore 2 (OmegaQuotient S) := MulEquiv.ofBijective
    ((omegaQuotientHom S).subgroupComap (pCore 2 (OmegaQuotient S))) (by
      constructor
      · intro x y h
        exact Subtype.ext (omegaQuotientHom_injective S (congrArg Subtype.val h))
      · intro x
        have hx : (x : OmegaQuotient S) ∈ H.map (omegaQuotientHom S) := by
          rw [omegaCorePreimage_map]
          exact x.property
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩)
  let f := omegaQuotientSylowEquiv S
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  obtain ⟨hindex, he⟩ := omegaQuotient_symmetric_three_of_large_noncyclic_tail
    hN S hZ hno W hunique hnormal B D hB hD hn hc hg hlarge hi
  obtain ⟨q, hq, ha, hinv⟩ :=
    exists_inverted_three_automorphism_in_omegaQuotient hN S hZ he t ht hout
  obtain ⟨BQ, DQ, hBQn, hDQn, ⟨eBQ⟩, hDQ, hnQ, hlargeQ, hcQ, hgQ, hfix⟩ :=
    exists_quaternion_large_hall_factors_fixed_by_order_three
      pCore_isPGroup B D hB hD hn hlarge hc hg (MulAut.conjNormal q) ha
  let B₀ := BQ.map e.symm.toMonoidHom
  let D₀ := DQ.map e.symm.toMonoidHom
  let eB : BQ ≃* B₀ := e.symm.subgroupMap BQ
  let eD : DQ ≃* D₀ := e.symm.subgroupMap DQ
  have hB₀ : Nonempty (B₀ ≃* QuaternionGroup 2) := ⟨eB.symm.trans eBQ⟩
  have hD₀ : IsBinaryHallFactor D₀ := hDQ.of_mulEquiv eD
  have hn₀ : ¬ IsCyclic D₀ := fun h => hnQ (eD.isCyclic.mpr h)
  have hlarge₀ : 16 ≤ Nat.card D₀ := (Nat.card_congr eD.toEquiv) ▸ hlargeQ
  have hc₀ : D₀ ≤ centralizer (B₀ : Set H) := by
    rintro d ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    exact (map_mul e.symm y x).symm.trans
      ((congrArg e.symm (hcQ hx y hy)).trans (map_mul e.symm x y))
  have hg₀ : B₀ ⊔ D₀ = ⊤ := by
    rw [← Subgroup.map_sup, hgQ, map_top_of_surjective _ e.symm.surjective]
  let DC := (pCore 2 (OmegaQuotient S) ⊓ centralizer ({q} : Set (OmegaQuotient S))).comap
    (omegaQuotientSylow S : Subgroup (OmegaQuotient S)).subtype
  let LC := DC ⊔ zpowers (f t)
  have hf (x : S) : (f x : OmegaQuotient S) = omegaQuotientHom S x :=
    omegaQuotientSylowEquiv_apply S x
  have heval (x : H) : (e x : OmegaQuotient S) = omegaQuotientHom S x := rfl
  have htout : (f t : OmegaQuotient S) ∉ pCore 2 (OmegaQuotient S) := by
    rw [hf]
    exact hout
  obtain ⟨htnorm, -, hcover⟩ := sylow_index_three_normalizer_cover
    (omegaQuotientSylow S) hindex ((index_omegaCorePreimage S).symm.trans hi)
    he q hq (f t) htout (by simpa only [hf] using hinv)
  -- The exact fixed-subgroup identity identifies the Hall image with the core centralizer.
  have hDC : D₀.map H.subtype = DC.comap f.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyQ : e y ∈ DQ := mem_map_equiv.mp hy
      have heq := congrArg Subtype.val ((hfix (e y)).mp hyQ)
      change q * (e y : OmegaQuotient S) * q⁻¹ = (e y : OmegaQuotient S) at heq
      change (f (y : S) : OmegaQuotient S) ∈ pCore 2 (OmegaQuotient S) ∧
        (f (y : S) : OmegaQuotient S) ∈ centralizer ({q} : Set (OmegaQuotient S))
      rw [hf, ← heval]
      exact ⟨(e y).property, mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp heq).symm⟩
    · intro hx
      change (f x : OmegaQuotient S) ∈ pCore 2 (OmegaQuotient S) ∧
        (f x : OmegaQuotient S) ∈ centralizer ({q} : Set (OmegaQuotient S)) at hx
      rw [hf] at hx
      let y : H := ⟨x, hx.1⟩
      refine ⟨y, ?_, rfl⟩
      apply mem_map_equiv.mpr
      apply (hfix (e y)).mpr
      apply Subtype.ext
      change q * (e y : OmegaQuotient S) * q⁻¹ = (e y : OmegaQuotient S)
      rw [heval]
      have hcomm := mem_centralizer_singleton_iff.mp hx.2
      change q * omegaQuotientHom S x * q⁻¹ = omegaQuotientHom S x
      rw [← hcomm, mul_inv_cancel_right]
  have hLC : D₀.map H.subtype ⊔ zpowers t = LC.comap f.toMonoidHom := by
    rw [show LC = DC ⊔ zpowers (f t) from rfl,
      ← Subgroup.comap_sup_eq f.toMonoidHom _ _ f.surjective, ← hDC]
    congr 1
    change zpowers t = (zpowers (f.toMonoidHom t)).comap f.toMonoidHom
    rw [← MonoidHom.map_zpowers f.toMonoidHom t,
      comap_map_eq_self_of_injective f.injective]
  refine ⟨t, B₀, D₀, ht, hout, hconj,
    e.symm.normal_map_iff.mpr hBQn, e.symm.normal_map_iff.mpr hDQn,
    hB₀, hD₀, hn₀, hlarge₀, hc₀, hg₀, ?_,
    noncyclicRotationPreimage_sup_hall_extension_eq_top S hi B₀ D₀
      hB₀ hD₀ hn₀ hlarge₀ hc₀ hg₀ t hout, ?_⟩
  · change t ∈ normalizer (D₀.map H.subtype : Set S)
    rw [hDC]
    exact le_normalizer_comap f.toMonoidHom htnorm
  · intro u hu huout
    have hfu : (f u : OmegaQuotient S) ∉ pCore 2 (OmegaQuotient S) := by
      rw [hf]
      exact huout
    obtain ⟨w, hw⟩ := hcover (f u) ((f.orderOf_eq u).trans hu) hfu
    have hwmem : f.symm (w : omegaQuotientSylow S) ∈ D₀.map H.subtype ⊔ zpowers t := by
      rw [hLC]
      change f (f.symm (w : omegaQuotientSylow S)) ∈ LC
      rw [f.apply_symm_apply]
      exact w.property
    refine ⟨⟨f.symm w, hwmem⟩, ?_⟩
    have hh : IsConj (f.symm (f u)) (f.symm (w : omegaQuotientSylow S)) :=
      f.symm.toMonoidHom.map_isConj hw
    simpa only [f.symm_apply_apply] using hh

end Stellmacher.Recognition.NormalEightNonnormalImage
