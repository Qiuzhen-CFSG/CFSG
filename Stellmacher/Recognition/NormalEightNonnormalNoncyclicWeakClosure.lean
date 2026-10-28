module

public import Stellmacher.Recognition.NormalEightNonnormalLargeTailSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicRotationSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicInvolutionSelection
public import Theory.GroupTheory.PGroup.LargeHallRotationFusion
public import Theory.GroupTheory.CharacteristicSylowCentralizerFusion
public import Theory.GroupTheory.PGroup.LargeHallInvolutionCentralizer

/-!
# Rotation-product fusion under the normal-only elementary bound

For a large noncyclic Hall tail, the core preimage has index at most two.
Its squares lie in a cyclic subgroup. Every element of its intrinsic rotation
product commutes with a fourth root of the central Sylow involution, so the
fourth-power fusion theorem excludes distinct fusion into that product.

The remaining branch is fusion into the complement of the rotation product.
The conditional assembly below keeps that premise explicit; its discharge
requires the characteristic line in the involution centralizer.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, printed p.392.
No bound on nonnormal elementary subgroups is used.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- A central Sylow involution cannot fuse distinctly into the intrinsic
rotation product of a core with a large noncyclic Hall tail. -/
public theorem eq_of_isConj_in_core_rotation_product_of_large_noncyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (z t : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (ht : t ∈ (closure {x : omegaCorePreimage S | x ^ 4 ≠ 1}).map
      (omegaCorePreimage S).subtype)
    (hconj : IsConj (z : G) (t : G)) : t = z := by
  let H := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  have hi := omegaCorePreimage_index_le_two_of_large_noncyclic_tail
    hN S hZ hno W hunique hnormal B D hB hD hn hc hg hlarge
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  obtain ⟨_, Q, hQ, hsquares, hroots⟩ :=
    cyclic_squares_and_intrinsic_rotation_roots_of_large_hall
      pCore_isPGroup B D hD hn hc hg hlarge
  let : IsCyclic Q := hQ
  have hzW : z ∈ W := by
    apply omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    refine ⟨⟨z, hzC⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z
  let zH : H := ⟨z, four_le_omegaCorePreimage hN S hZ W hW hno hzW⟩
  obtain ⟨tH, htH, rfl⟩ := ht
  have hzHC : e zH ∈ center (pCore 2 (OmegaQuotient S)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (mem_center_iff.mp hzC (u : S)))
  have hzHO : orderOf (e zH) = 2 := by
    rw [e.orderOf_eq, ← orderOf_coe]
    exact hz
  have htrot : e tH ∈ closure {x : pCore 2 (OmegaQuotient S) | x ^ 4 ≠ 1} := by
    have hle : closure {x : H | x ^ 4 ≠ 1} ≤
        (closure {x : pCore 2 (OmegaQuotient S) | x ^ 4 ≠ 1}).comap e.toMonoidHom := by
      apply (closure_le _).mpr
      intro x hx
      apply Subgroup.subset_closure
      change (e x) ^ 4 ≠ 1
      intro he
      apply hx
      apply e.injective
      simpa only [map_pow, map_one] using he
    exact hle htH
  obtain ⟨x, hx, hxt⟩ := hroots (e zH) (e tH) hzHC hzHO htrot
  let Q' := Q.comap e.toMonoidHom
  let : IsCyclic Q' := isCyclic_of_injective (e.toMonoidHom.subgroupComap Q) (by
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h)))
  have hsq (u : H) : u ^ 2 ∈ Q' := by
    change e (u ^ 2) ∈ Q
    rw [map_pow]
    exact hsquares (e u)
  have hroot : ∃ u : H, u ^ 4 = zH ∧ Commute u tH := by
    refine ⟨e.symm x, ?_, ?_⟩
    · apply e.injective
      rw [map_pow, e.apply_symm_apply, hx]
    · have hh := hxt.map e.symm.toMonoidHom
      change Commute (e.symm x) (e.symm (e tH)) at hh
      rwa [e.symm_apply_apply] at hh
  have heq := S.eq_of_isConj_of_index_le_two_of_squares_mem_cyclic H hi Q' hsq
    zH hzC ((orderOf_coe zH).symm.trans hz) tH hroot hconj
  exact congrArg Subtype.val heq

/-- Core weak closure reduces to nonfusion in the complement of the intrinsic
rotation product. The rotation branch is discharged by fourth powers. -/
public theorem omegaCorePreimage_weakly_closed_of_large_noncyclic_tail_of_outside_nonfusion
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (houtside : ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S →
      t ∉ (closure {x : omegaCorePreimage S | x ^ 4 ≠ 1}).map
        (omegaCorePreimage S).subtype → ¬ IsConj (z : G) (t : G)) :
    ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  intro z t hzC hz ht hconj
  by_cases hrot : t ∈ (closure {x : omegaCorePreimage S | x ^ 4 ≠ 1}).map
      (omegaCorePreimage S).subtype
  · exact eq_of_isConj_in_core_rotation_product_of_large_noncyclic_tail
      hN S hZ hno W hW hunique hnormal B D hB hD hn hc hg hlarge z t hzC hz hrot hconj
  · exact (houtside z t hzC hz ht hrot hconj).elim

/-- The outside-rotation involutions are excluded by the characteristic
centralizer line.  Together with the fourth-power argument this gives weak
closure of the whole core preimage. -/
public theorem omegaCorePreimage_weakly_closed_of_large_noncyclic_tail
    [IsSimpleGroup G] (_hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (_hwidth : ∀ B' D' : Subgroup (pCore 2 (OmegaQuotient S)),
      B'.Normal → D'.Normal → IsExtraspecial 2 B' → IsBinaryHallFactor D' →
      D' ≤ centralizer (B' : Set (pCore 2 (OmegaQuotient S))) →
      B' ⊔ D' = ⊤ → Nat.card B' = 8) :
    ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  let H := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  have hi : H.index = 2 := omegaCorePreimage_index_eq_two_of_large_noncyclic_tail
    hN S hZ hno W hW hunique hnormal B D hB hD hn hc hg hlarge
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  have houtside : ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ H → t ∉ noncyclicRotationPreimage S → ¬ IsConj (z : G) (t : G) := by
    intro z t hzC hz ht htr hconj
    have hzW : z ∈ W := by
      apply omega_one_center_le_normal_four_of_no_normal_eight hno W hW
      refine ⟨⟨z, hzC⟩, subset_closure ?_, rfl⟩
      apply Subtype.ext
      change z ^ (2 ^ 1) = 1
      simpa only [pow_one, hz] using pow_orderOf_eq_one z
    have hzHmem : z ∈ H := four_le_omegaCorePreimage hN S hZ W hW hno hzW
    let zH : H := ⟨z, hzHmem⟩
    let X : Set S := {u | u ∈ H ∧ u ∉ noncyclicRotationPreimage S ∧ orderOf u = 2}
    have hstable : ∀ u : S, u ∈ X → ∀ g : G, Commute g (z : G) →
        ∀ v : S, (MulAut.conj g) (u : G) = (v : G) → v ∈ X := by
      intro u hu g hgz v huv
      have hzcg : g ∈ centralizer ({(z : G)} : Set G) :=
        mem_centralizer_singleton_iff.mpr hgz
      rw [← omegaNormalizer_eq_centralizer_of_central_involution S hZ z hz hzC]
        at hzcg
      let gu : omegaNormalizer S :=
        ⟨g, hzcg⟩
      let uu : omegaNormalizer S :=
        ⟨(u : G), sylow_le_omegaNormalizer S u.property⟩
      let vv : omegaNormalizer S :=
        ⟨(v : G), sylow_le_omegaNormalizer S v.property⟩
      have huv' : IsConj uu vv := by
        apply isConj_iff.mpr
        refine ⟨gu, ?_⟩
        apply Subtype.ext
        simpa [gu, uu, vv] using huv
      have hv := outside_noncyclicRotationPreimage_of_omegaNormalizer_isConj
        S u v hu.1 hu.2.1 huv'
      have hvo : orderOf v = 2 := by
        rw [← orderOf_coe, ← huv, MulEquiv.orderOf_eq, orderOf_coe, hu.2.2]
      exact ⟨hv.1, hv.2, hvo⟩
    have hproper : ∀ u : S, u ∈ X → IsConj (z : G) (u : G) →
        centralizer ({u} : Set S) ≠ ⊤ := by
      intro u hu huconj
      let uH : H := ⟨u, hu.1⟩
      let A := B.comap e.toMonoidHom
      let D' := D.comap e.toMonoidHom
      let eA : A ≃* B := MulEquiv.ofBijective (e.toMonoidHom.subgroupComap B) (by
        constructor
        · intro a b hab; exact Subtype.ext (e.injective (congrArg Subtype.val hab))
        · intro b
          refine ⟨⟨e.symm b, ?_⟩, ?_⟩
          change e (e.symm (b : pCore 2 (OmegaQuotient S))) ∈ B
          simpa only [e.apply_symm_apply] using b.property
          exact Subtype.ext (e.apply_symm_apply b))
      let eD : D' ≃* D := MulEquiv.ofBijective (e.toMonoidHom.subgroupComap D) (by
        constructor
        · intro a b hab; exact Subtype.ext (e.injective (congrArg Subtype.val hab))
        · intro d
          refine ⟨⟨e.symm d, ?_⟩, ?_⟩
          change e (e.symm (d : pCore 2 (OmegaQuotient S))) ∈ D
          simpa only [e.apply_symm_apply] using d.property
          exact Subtype.ext (e.apply_symm_apply d))
      let : A.Normal := (inferInstance : B.Normal).comap e.toMonoidHom
      let : D'.Normal := (inferInstance : D.Normal).comap e.toMonoidHom
      let : IsExtraspecial 2 A := IsExtraspecial.of_mulEquiv eA.symm inferInstance
      let hD' : IsBinaryHallFactor D' := hD.of_mulEquiv eD.symm
      let : IsCyclic (center H) :=
        (centerCongr e).isCyclic.mpr inferInstance
      have hAc : Nat.card A = 8 := by
        exact (Nat.card_congr eA.toEquiv).trans hB
      have hDc : D' ≤ centralizer (A : Set H) := by
        intro d hd
        apply mem_centralizer_iff.mpr
        intro a ha
        change a * d = d * a
        have hcd : ((eD ⟨d, hd⟩ : D) : pCore 2 (OmegaQuotient S)) ∈
            centralizer (B : Set (pCore 2 (OmegaQuotient S))) :=
          hc (eD ⟨d, hd⟩).property
        have hh := (mem_centralizer_iff.mp hcd)
          ((eA ⟨a, ha⟩ : B) : pCore 2 (OmegaQuotient S))
          (by exact (eA ⟨a, ha⟩).property)
        have hAeq : e.symm ((eA ⟨a, ha⟩ : B) : pCore 2 (OmegaQuotient S)) = a := by
          apply e.injective
          exact e.apply_symm_apply (e a)
        have hDeq : e.symm ((eD ⟨d, hd⟩ : D) : pCore 2 (OmegaQuotient S)) = d := by
          apply e.injective
          exact e.apply_symm_apply (e d)
        have hh' := congrArg e.symm hh
        rw [map_mul, map_mul, hAeq, hDeq] at hh'
        exact hh'
      have hgc : A ⊔ D' = ⊤ := by
        have hm : (A ⊔ D').map e.toMonoidHom = ⊤ := by
          rw [Subgroup.map_sup, map_comap_eq_self_of_surjective e.surjective,
            map_comap_eq_self_of_surjective e.surjective, hg]
        have hm' := congrArg (fun K : Subgroup (pCore 2 (OmegaQuotient S)) =>
          K.comap e.toMonoidHom) hm
        simpa only [Subgroup.comap_map_eq_self_of_injective
          (f := e.toMonoidHom) e.injective, Subgroup.comap_top] using hm'
      have hn' : ¬ IsCyclic D' := by
        intro hcyc
        apply hn
        exact isCyclic_of_surjective eD.toMonoidHom eD.surjective
      have hlarge' : 16 ≤ Nat.card D' := by
        exact (Nat.card_congr eD.toEquiv).symm ▸ hlarge
      have hline := large_hall_involution_centralizer_line H hi
        (S.isPGroup'.to_subgroup H) A D' hAc hD' hn' hDc hgc hlarge'
        zH uH hzC (by simpa [zH] using hz) (by simpa [uH] using hu.2.2)
        (by
          intro huR
          apply hu.2.1
          change u ∈ (closure {x : H | x ^ 4 ≠ 1}).map H.subtype
          exact mem_map_of_mem H.subtype huR)
      exact hline.1
    have hline : ∀ u : S, u ∈ X → IsConj (z : G) (u : G) →
        (_root_.commutator (centralizer ({u} : Set S)) ⊓
          center (centralizer ({u} : Set S))).map
            (centralizer ({u} : Set S)).subtype = zpowers z := by
      intro u hu huconj
      let uH : H := ⟨u, hu.1⟩
      let A := B.comap e.toMonoidHom
      let D' := D.comap e.toMonoidHom
      let eA : A ≃* B := MulEquiv.ofBijective (e.toMonoidHom.subgroupComap B) (by
        constructor
        · intro a b hab; exact Subtype.ext (e.injective (congrArg Subtype.val hab))
        · intro b; refine ⟨⟨e.symm b, ?_⟩, ?_⟩
          · change e (e.symm (b : pCore 2 (OmegaQuotient S))) ∈ B
            simpa only [e.apply_symm_apply] using b.property
          exact Subtype.ext (e.apply_symm_apply b))
      let eD : D' ≃* D := MulEquiv.ofBijective (e.toMonoidHom.subgroupComap D) (by
        constructor
        · intro a b hab; exact Subtype.ext (e.injective (congrArg Subtype.val hab))
        · intro d; refine ⟨⟨e.symm d, ?_⟩, ?_⟩
          · change e (e.symm (d : pCore 2 (OmegaQuotient S))) ∈ D
            simpa only [e.apply_symm_apply] using d.property
          exact Subtype.ext (e.apply_symm_apply d))
      let : A.Normal := (inferInstance : B.Normal).comap e.toMonoidHom
      let : D'.Normal := (inferInstance : D.Normal).comap e.toMonoidHom
      let : IsExtraspecial 2 A := IsExtraspecial.of_mulEquiv eA.symm inferInstance
      let hD' : IsBinaryHallFactor D' := hD.of_mulEquiv eD.symm
      let : IsCyclic (center H) :=
        (centerCongr e).isCyclic.mpr inferInstance
      have hAc : Nat.card A = 8 := (Nat.card_congr eA.toEquiv).trans hB
      have hDc : D' ≤ centralizer (A : Set H) := by
        intro d hd
        apply mem_centralizer_iff.mpr
        intro a ha
        change a * d = d * a
        have hcd : ((eD ⟨d, hd⟩ : D) : pCore 2 (OmegaQuotient S)) ∈
            centralizer (B : Set (pCore 2 (OmegaQuotient S))) :=
          hc (eD ⟨d, hd⟩).property
        have hh := (mem_centralizer_iff.mp hcd)
          ((eA ⟨a, ha⟩ : B) : pCore 2 (OmegaQuotient S))
          (by exact (eA ⟨a, ha⟩).property)
        have hAeq : e.symm ((eA ⟨a, ha⟩ : B) : pCore 2 (OmegaQuotient S)) = a := by
          apply e.injective
          exact e.apply_symm_apply (e a)
        have hDeq : e.symm ((eD ⟨d, hd⟩ : D) : pCore 2 (OmegaQuotient S)) = d := by
          apply e.injective
          exact e.apply_symm_apply (e d)
        have hh' := congrArg e.symm hh
        rw [map_mul, map_mul, hAeq, hDeq] at hh'
        exact hh'
      have hgc : A ⊔ D' = ⊤ := by
        have hm : (A ⊔ D').map e.toMonoidHom = ⊤ := by
          rw [Subgroup.map_sup, map_comap_eq_self_of_surjective e.surjective,
            map_comap_eq_self_of_surjective e.surjective, hg]
        have hm' := congrArg (fun K : Subgroup (pCore 2 (OmegaQuotient S)) =>
          K.comap e.toMonoidHom) hm
        simpa only [Subgroup.comap_map_eq_self_of_injective
          (f := e.toMonoidHom) e.injective, Subgroup.comap_top] using hm'
      have hn' : ¬ IsCyclic D' := by
        intro hcyc
        apply hn
        exact isCyclic_of_surjective eD.toMonoidHom eD.surjective
      have hlarge' : 16 ≤ Nat.card D' := by
        exact (Nat.card_congr eD.toEquiv).symm ▸ hlarge
      exact (large_hall_involution_centralizer_line H hi
        (S.isPGroup'.to_subgroup H) A D' hAc hD' hn' hDc hgc hlarge'
        zH uH hzC (by simpa [zH] using hz) (by simpa [uH] using hu.2.2)
        (by
          intro huR
          apply hu.2.1
          change u ∈ (closure {x : H | x ^ 4 ≠ 1}).map H.subtype
          exact mem_map_of_mem H.subtype huR)).2
    have hnf := Sylow.not_isConj_of_stable_derived_center_lines S z hzC hz X
      hstable hproper hline
    exact (hnf t ⟨ht, htr, by
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      calc
        orderOf t = orderOf (g * (z : G) * g⁻¹) := by
          rw [← orderOf_coe, hg]
        _ = orderOf (z : G) := by simpa using (MulAut.conj g).orderOf_eq (z : G)
        _ = 2 := (orderOf_coe z).trans hz⟩ hconj).elim
  intro z t hzC hz ht hconj
  apply omegaCorePreimage_weakly_closed_of_large_noncyclic_tail_of_outside_nonfusion
    hN S hZ hno W hW hunique hnormal B D hB hD hn hc hg hlarge houtside
    z t hzC hz ht hconj

end Stellmacher.Recognition.NormalEightNonnormalImage
