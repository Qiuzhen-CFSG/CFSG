module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Reduction
public import Theory.SpecificGroups.SL3.InvolutionDerived
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.SpecificGroups.ProjectiveLinearInvolutions
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import GorensteinWalter.PSL2CoprimeSylowCyclic

/-!
# An upper bound for the elementary split PSL₃ intersection

Choose an involution z in the intrinsic center of a Sylow two-subgroup S.
Then C_Q(Z(S))′ lies in C_Q(z)′. In the actual PSL₃ model, lift z to SL₃
and conjugate it to diag(-1,-1,1). The scalar kernel has order dividing
three; involutions lift by cubing, and their centralizers lift because the
kernel is central of odd order. No normality of the involution subgroup
is required.

The GL₂ block determinant kills the commutator subgroup. Its kernel is
SL₂ and embeds in PSL₃: the last diagonal entry of a determinant-one
block is one, so a scalar block in the projective kernel is the identity.
Finally, elementary three-subgroups of SL₂ have order at most three,
using the existing cyclic odd Sylow theorem for the actual PSL₂ quotient.
Thus the intersection with any elementary three-subgroup has order at most
three. Nontriviality, needed for the exact order-nine-complement calculation,
is a separate result.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), using the involution block
calculation in A.3.21(a), printed p.55 (PDF p.66). The finite-field scalar
kernel count is reused through the attributed ATLAS port in
`Theory.SpecificGroups.PSL3.ProjectionKernel`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement

private theorem sl2_elementary_bound (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] (hF : Nat.card F = p) (hseven : 7 ≤ p)
    (D : Subgroup SL(2,F)) [IsElementaryAbelian 3 D] : Nat.card D ≤ 3 := by
  let q : SL(2,F) →* PSL(2,F) := QuotientGroup.mk' (center SL(2,F))
  have hker : Nat.Coprime 3 (Nat.card q.ker) := by
    have hd : Nat.card q.ker ∣ 2 := by
      rw [show q.ker = center SL(2,F) from QuotientGroup.ker_mk' _,
        Atlas.ExceptionalSupport.card_sl_center]
      exact Nat.gcd_dvd_left 2 _
    exact (show Nat.Coprime 3 2 by decide).of_dvd_right hd
  have hcop : Nat.Coprime 3 (Nat.card F) := by
    rw [hF]
    exact Nat.prime_three.coprime_iff_not_dvd.mpr (fun hd => by
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with hn | hn <;> omega)
  obtain ⟨U, hU⟩ := ((IsElementaryAbelian.isPGroup 3 D).map q).exists_le_sylow
  have hcyc : IsCyclic U :=
    GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F
      (p := p) (f := 1) (by simpa using hF) (by omega) 3 (by decide) hcop U
  let _ := hcyc
  have hcycD : IsCyclic (D.map q) := Subgroup.isCyclic_of_le hU
  let _ := hcycD
  have hi := Subgroup.injective_comp_subtype_of_coprime_ker q hker D
    (IsElementaryAbelian.isPGroup 3 D)
  let _ : IsCyclic D := isCyclic_of_injective (q.subgroupMap D) (by
    intro x y hxy
    exact hi (congrArg Subtype.val hxy))
  apply Nat.le_of_dvd (by decide : 0 < 3)
  simpa only [IsCyclic.exponent_eq_card] using IsElementaryAbelian.exponent_dvd_p 3 D

private theorem projection_involution_lift (F : Type*) [Field F] [Finite F]
    (z : PSL(3,F)) (hz : orderOf z = 2) :
    ∃ u : SL(3,F), orderOf u = 2 ∧ Matrix.PSL3.projection F u = z := by
  let q := Matrix.PSL3.projection F
  obtain ⟨x, hx⟩ := Matrix.PSL3.projection_surjective F z
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hk : x ^ 2 ∈ q.ker := by
    change q (x ^ 2) = 1
    rw [map_pow, hx, hz2]
  have hcube : (x ^ 2) ^ 3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (q.ker.orderOf_dvd_natCard hk).trans (by
      rw [Matrix.PSL3.card_projectionKernel]
      exact Nat.gcd_dvd_left _ _)
  have hm : q (x ^ 3) = z := by
    rw [map_pow, hx, pow_succ, hz2, one_mul]
  refine ⟨x ^ 3, orderOf_eq_prime ?_ ?_, hm⟩
  · simpa only [← pow_mul] using hcube
  · intro h
    have hz1 : z = 1 := by rw [← hm, h, map_one]
    simp [hz1] at hz

private theorem projection_centralizer (F : Type*) [Field F] [Finite F]
    (u : SL(3,F)) (hu : orderOf u = 2) :
    (centralizer ({u} : Set SL(3,F))).map (Matrix.PSL3.projection F) =
      centralizer ({Matrix.PSL3.projection F u} : Set PSL(3,F)) := by
  let q := Matrix.PSL3.projection F
  apply le_antisymm
  · simpa using map_centralizer_le_centralizer_image ({u} : Set SL(3,F)) q
  · intro y hy
    obtain ⟨x, rfl⟩ := Matrix.PSL3.projection_surjective F y
    refine ⟨x, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    have hker : Nat.Coprime 2 (Nat.card q.ker) := by
      apply (show Nat.Coprime 2 3 by decide).of_dvd_right
      rw [Matrix.PSL3.card_projectionKernel]
      exact Nat.gcd_dvd_left _ _
    have hm : q (MulAut.conj x u) = q u := by
      simp only [MulAut.conj_apply, map_mul, map_inv]
      rw [mem_centralizer_singleton_iff.mp hy, mul_inv_cancel_right]
    obtain ⟨k, hk⟩ := Subgroup.involutions_same_image_conj_ker q hker
      ((MulAut.conj x).orderOf_eq u |>.trans hu) hu hm
    have hkZ : (k : SL(3,F)) ∈ center SL(3,F) := by
      simpa only [q, Matrix.PSL3.projection_ker] using k.property
    have hconj : MulAut.conj x u = u := by
      rwa [← mem_center_iff.mp hkZ (MulAut.conj x u), mul_inv_cancel_right] at hk
    exact mul_inv_eq_iff_eq_mul.mp hconj

private theorem standard_derived_embedding (F : Type*) [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) :
    ∃ f : (⁅centralizer ({Matrix.PSL3.projection F (Matrix.SL3.standardInvolution F)} :
          Set PSL(3,F)), centralizer
          ({Matrix.PSL3.projection F (Matrix.SL3.standardInvolution F)} : Set PSL(3,F))⁆ : Subgroup PSL(3,F)) →*
        SL(2,F), Function.Injective f := by
  let C := Matrix.SL3.standardCentralizer F
  let K := (Matrix.SL3.centralizerDet F h2).ker
  let q := Matrix.PSL3.projection F
  let f : C →* PSL(3,F) := q.comp C.subtype
  have hlast (a : C) (ha : a ∈ K) : (a : SL(3,F)) 2 2 = 1 := by
    let e := Matrix.SL3.standardInvolutionCentralizerEquiv F h2
    let B := e.symm a
    have hdet : Matrix.GeneralLinearGroup.det B = 1 := by
      change Matrix.SL3.centralizerDet F h2 a = 1 at ha
      rw [Matrix.SL3.centralizerDet_apply] at ha
      exact ha
    have hm : (e B).val = a.val := congrArg Subtype.val (e.apply_symm_apply a)
    rw [Matrix.SL3.standardInvolutionCentralizerEquiv_apply_val] at hm
    have hh := congrArg (fun M : SL(3,F) => M 2 2) hm
    change (↑((Matrix.GeneralLinearGroup.det B)⁻¹) : F) = (a : SL(3,F)) 2 2 at hh
    rw [hdet, inv_one, Units.val_one] at hh
    exact hh.symm
  have hi : Function.Injective (f.comp K.subtype) := by
    apply (f.comp K.subtype).ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    change a = 1
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hz : (a.val : SL(3,F)) ∈ center SL(3,F) := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact ha
    rw [← Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (2 : Fin 3),
      hlast a.val a.property]
    simp
  let I := K.map f
  let eKI : K ≃* I := MulEquiv.ofBijective (f.subgroupMap K)
    ⟨fun a b hab => hi (congrArg Subtype.val hab), f.subgroupMap_surjective K⟩
  have hd : ⁅centralizer ({q (Matrix.SL3.standardInvolution F)} : Set PSL(3,F)),
      centralizer ({q (Matrix.SL3.standardInvolution F)} : Set PSL(3,F))⁆ ≤ I := by
    have hh := map_mono (f := f) (Matrix.SL3.centralizer_commutator_le_detKernel F h2)
    change (commutator C).map (q.comp C.subtype) ≤ I at hh
    rw [← map_map, map_subtype_commutator, map_commutator] at hh
    change ⁅(centralizer ({Matrix.SL3.standardInvolution F} : Set SL(3,F))).map q,
      (centralizer ({Matrix.SL3.standardInvolution F} : Set SL(3,F))).map q⁆ ≤ I at hh
    rwa [projection_centralizer F _ (Matrix.SL3.standardInvolution_orderOf F h2)] at hh
  let eK := Matrix.SL3.centralizerDetKernelEquiv F h2
  exact ⟨eK.toMonoidHom.comp (eKI.symm.toMonoidHom.comp (inclusion hd)),
    eK.injective.comp (eKI.symm.injective.comp (inclusion_injective hd))⟩

private theorem projective_involution_to_standard (F : Type*) [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (z : PSL(3,F)) (hz : orderOf z = 2) :
    ∃ a : MulAut PSL(3,F), a z =
      Matrix.PSL3.projection F (Matrix.SL3.standardInvolution F) := by
  obtain ⟨u, hu, hmap⟩ := projection_involution_lift F z hz
  obtain ⟨s, hs⟩ := isConj_iff.mp (Matrix.SL3.involution_isConj_standard F u hu h2)
  refine ⟨MulAut.conj (Matrix.PSL3.projection F s), ?_⟩
  rw [← hmap]
  simpa only [MulAut.conj_apply, map_mul, map_inv] using congrArg (Matrix.PSL3.projection F) hs

private theorem elementary_of_injective {A B : Type*} [Group A] [Group B]
    [IsElementaryAbelian 3 B] (f : A →* B) (hi : Function.Injective f) :
    IsElementaryAbelian 3 A where
  toIsMulCommutative := ⟨⟨fun x y => hi (by
    simp only [map_mul]
    exact mul_comm' _ _)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => hi (by
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 B) (f a)))

private theorem elementary_card_le_of_injective_sl2
    (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime]
    (hF : Nat.card F = p) (hseven : 7 ≤ p)
    {A : Type*} [Group A] [IsElementaryAbelian 3 A]
    (f : A →* SL(2,F)) (hi : Function.Injective f) : Nat.card A ≤ 3 := by
  let _ : IsElementaryAbelian 3 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  rw [Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  exact sl2_elementary_bound F p hF hseven f.range

private theorem centralizer_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) :
    (centralizer ({z} : Set G)).map e.toMonoidHom = centralizer ({e z} : Set H) := by
  apply le_antisymm
  · simpa using map_centralizer_le_centralizer_image ({z} : Set G) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, mem_centralizer_singleton_iff.mpr ?_, e.apply_symm_apply x⟩
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

private theorem projective_derived_elementary_bound
    (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime]
    (hF : Nat.card F = p) (hseven : 7 ≤ p) (h2 : (2 : F) ≠ 0)
    (z : PSL(3,F)) (hz : orderOf z = 2)
    (D : Subgroup PSL(3,F)) [IsElementaryAbelian 3 D]
    (hD : D ≤ ⁅centralizer ({z} : Set PSL(3,F)), centralizer ({z} : Set PSL(3,F))⁆) :
    Nat.card D ≤ 3 := by
  obtain ⟨a, ha⟩ := projective_involution_to_standard F h2 z hz
  have hmap : D.map a.toMonoidHom ≤
      ⁅centralizer ({Matrix.PSL3.projection F (Matrix.SL3.standardInvolution F)} : Set PSL(3,F)),
        centralizer ({Matrix.PSL3.projection F (Matrix.SL3.standardInvolution F)} : Set PSL(3,F))⁆ := by
    have hh := map_mono (f := a.toMonoidHom) hD
    rwa [map_commutator, centralizer_map_equiv a z, ha] at hh
  obtain ⟨f, hf⟩ := standard_derived_embedding F h2
  let _ : IsElementaryAbelian 3 (D.map a.toMonoidHom) := IsElementaryAbelian.map a.toMonoidHom
  rw [← card_map_of_injective (f := a.toMonoidHom) a.injective (K := D)]
  exact elementary_card_le_of_injective_sl2 F p hF hseven
    (f.comp (inclusion hmap)) (hf.comp (inclusion_injective hmap))

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split

private theorem exists_intrinsic_central_involution {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (hQ : 2 ∣ Nat.card Q) :
    ∃ z : Q, orderOf z = 2 ∧ z ∈ (S : Subgroup Q) ⊓ centralizer (S : Set Q) := by
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot _).mpr (S.ne_bot_of_dvd_card hQ)
  let _ := S.isPGroup'.center_nontrivial
  have hZ : IsPGroup 2 (center S) := S.isPGroup'.to_subgroup _
  obtain ⟨n, hn, hc⟩ := hZ.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2
    (hc ▸ dvd_pow_self 2 (by omega : n ≠ 0))
  refine ⟨z.val.val, ?_, z.val.property, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using hz
  · intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp z.property (⟨x, hx⟩ : S))

-- Retain the pair and order-nine hypotheses of the source interface, although
-- this upper bound holds for every elementary three-subgroup.
set_option linter.unusedVariables false in
/-- The elementary intersection with the derived centralizer of the Sylow
center has order at most three in the actual split PSL₃ model. -/
theorem projective_elementary_intersection_le_three
    {Q : Type*} [Group Q] [Finite Q] (S : Sylow 2 Q) (R : Subgroup Q)
    (h : PairInput S R) (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hlarge : 3 < p) (hmod : p % 3 = 1) (hm : ClassicalGroup.IsPSL Q 3 p)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9) :
    Nat.card ((centralizerDerived (S : Subgroup Q)).subgroupOf R) ≤ 3 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ : Fact p.Prime := ⟨hp⟩
  let _ := he
  have hseven : 7 ≤ p := by
    obtain ⟨k, hk⟩ := ho
    omega
  have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (by rwa [hF])
  have heven : 2 ∣ Nat.card Q := by
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.two_dvd_card_fin_three F h2
  obtain ⟨z, hz, hzZ⟩ := exists_intrinsic_central_involution S heven
  have hC : centralizer ((S : Subgroup Q) ⊓ centralizer (S : Set Q) : Set Q) ≤
      centralizer ({z} : Set Q) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx z hzZ).symm
  have hd : centralizerDerived (S : Subgroup Q) ≤
      ⁅centralizer ({z} : Set Q), centralizer ({z} : Set Q)⁆ :=
    commutator_mono hC hC
  let A := (centralizerDerived (S : Subgroup Q)).subgroupOf R
  let g : A →* PSL(3,F) := e.toMonoidHom.comp (R.subtype.comp A.subtype)
  have hi : Function.Injective g := e.injective.comp
    (R.subtype_injective.comp A.subtype_injective)
  let _ : IsElementaryAbelian 3 A := elementary_of_injective A.subtype A.subtype_injective
  let _ : IsElementaryAbelian 3 g.range :=
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hD : g.range ≤
      ⁅centralizer ({e z} : Set PSL(3,F)), centralizer ({e z} : Set PSL(3,F))⁆ := by
    have hh := map_mono (f := e.toMonoidHom) hd
    rw [map_commutator, centralizer_map_equiv e z] at hh
    rintro x ⟨a, rfl⟩
    exact hh ⟨a.val.val, a.property, rfl⟩
  change Nat.card A ≤ 3
  rw [Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  exact projective_derived_elementary_bound F p hF hseven h2 (e z)
    ((e.orderOf_eq z).trans hz) g.range hD

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
