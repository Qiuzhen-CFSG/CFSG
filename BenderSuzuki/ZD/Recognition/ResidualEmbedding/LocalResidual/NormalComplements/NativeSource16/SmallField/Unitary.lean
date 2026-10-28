module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.FieldSource
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.FixedCircle
public import Theory.SpecificGroups.SU3.OddThreeLocal.CyclicSylow

/-!
# The unitary terminal circle in the smallest paired-field case

Let an involutory conjugation action fix a distinguished involution of a
unitary local circle. The unitary fixed-involution theorem fixes the whole
first Omega subgroup of a Sylow containing that involution. Its elements are
distinguished, so this subgroup embeds into the actor's actual circle.
When that circle is PSL₂(4), divisibility of its order 60 forces the unitary
field order to be four. The possible special cover has odd field exponent,
so it is excluded. Sylow three-subgroups of the remaining PSU₃(4) are cyclic.
This argument includes inner and outer actions without assuming either one.

Source: GLS IV, Chapter 2, Proposition 16.5, smallest paired-field case;
Chapter 4, Lemmas 3.2(b) and 3.4(f).
-/

noncomputable section
namespace BenderSuzuki.ZD.Source16SmallField
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem fixed_omega_card_dvd_small_circle
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M) (v : F)
    (eSmall : localCircle Z (centralizer ({(v : G)} : Set G)) ≃* PSL2BinaryMatrixGroup 2)
    (P : Sylow 2 (localCircle Z F))
    (hfix : omegaOneAmbient (P : Subgroup (localCircle Z F)) ≤
      (source16_circleAction h F hFM hne v).fixedSubgroup) :
    Nat.card (omegaOneAmbient (P : Subgroup (localCircle Z F))) ∣ 60 := by
  let C := localCircle Z F
  let f := localCircleHom Z F
  let V := centralizer ({(v : G)} : Set G)
  have hle : (omegaOneAmbient (P : Subgroup C)).map f ≤ localCircleIn Z V := by
    rw [map_le_iff_le_comap]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    have hxf := (MulAut.mem_fixedSubgroup _ x).mp
      (hfix ((omegaOneAmbient_le_iff _ _).mp le_rfl x hx hx2))
    have hc := congrArg f hxf
    rw [source16_circleAction_apply] at hc
    rw [mem_comap,localCircleIn_eq_closure]
    exact subset_closure ⟨localCircle_involution_mem h r F hF hFM hne ⟨hx1,hx2⟩,
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc).symm⟩
  have hcard : Nat.card (localCircleIn Z V) = 60 := by
    change Nat.card ((localCircle Z V).map V.subtype) = 60
    rw [← Nat.card_congr ((localCircle Z V).equivMapOfInjective V.subtype V.subtype_injective).toEquiv,
      Nat.card_congr eSmall.toEquiv]
    have hh := External.huppert614_card_psl_mul_center (K := BinaryGaloisField 2)
    rw [External.huppert614_card_center_of_neg_one_eq_one (by simp only [CharTwo.neg_eq]),
      show Nat.card (BinaryGaloisField 2) = 4 from GaloisField.card 2 2 (by decide)] at hh
    norm_num at hh ⊢
    exact hh
  have hd := card_dvd_of_le hle
  rw [card_map_of_injective (localCircleHom_injective Z F),hcard] at hd
  exact hd

private theorem exponent_two_of_divides_sixty {n : ℕ} (hn : 2 ≤ n)
    (hd : 2 ^ n ∣ 60) : n = 2 := by
  have hn3 : ¬ 3 ≤ n := by
    intro hh
    have h8 : 8 ∣ 60 := (pow_dvd_pow 2 hh).trans hd
    norm_num at h8
  omega

omit [Finite G] in
/-- Every three-subgroup in an actual PSU₃(4) circle is cyclic. The map
uses the literal ambient circle inclusion. -/
public theorem three_subgroup_cyclic_in_projective_four_circle
    (F R : Subgroup G) (hRF : R ≤ localCircleIn Z F) (hR : IsPGroup 3 R)
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = 4 ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 4)
    (e : localCircle Z F ≃* ProjectiveSpecialUnitaryMatrixGroup J) : IsCyclic R := by
  let eC : localCircle Z F ≃* localCircleIn Z F :=
    (localCircle Z F).equivMapOfInjective F.subtype F.subtype_injective
  let f : R →* ProjectiveSpecialUnitaryMatrixGroup J :=
    e.toMonoidHom.comp (eC.symm.toMonoidHom.comp (inclusion hRF))
  have hf : Function.Injective f := e.injective.comp
    (eC.symm.injective.comp (inclusion_injective hRF))
  have hp : IsPGroup 3 f.range := hR.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  let : IsCyclic P := HermitianForm.OddThreeLocal.cyclic_three_sylow_of_mod_one
    J 4 (by decide) (by decide) hcard hfixed P
  let g : R →* P := f.codRestrict (P : Subgroup _) (fun x => hP ⟨x,rfl⟩)
  exact isCyclic_of_injective g (fun x y he => hf (congrArg Subtype.val he))

/-- A unitary central quotient with an actual marked square-one action and
an actor circle PSL₂(4) has exponent two and is itself the projective model. -/
public theorem unitary_degree_two_of_small_actor_circle_models
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M)
    (v : F) (hv2 : (v : G) ^ 2 = 1)
    (eSmall : localCircle Z (centralizer ({(v : G)} : Set G)) ≃* PSL2BinaryMatrixGroup 2)
    {t : G} (ht : t ∈ Z) (htF : t ∈ F) (htv : Commute t (v : G))
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hmodels : Nonempty (localCircle Z F ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      (Odd n ∧ Nonempty (localCircle Z F ≃* J.specialSubgroup))) :
    n = 2 ∧ Nonempty (localCircle Z F ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let C := localCircle Z F
  let a := source16_circleAction h F hFM hne v
  let tC : C := ⟨⟨t,htF⟩,subset_closure ht⟩
  have htC : PFAppendixIII.IsInvolution tC :=
    IsInvolution.subtype (IsInvolution.subtype (h.involutions t ht) htF) _
  have ha : a ^ 2 = 1 := by
    change (source16_circleAction h F hFM hne v) ^ 2 = 1
    rw [← map_pow,show v ^ 2 = 1 from Subtype.ext hv2,map_one]
  have hat : a tC = tC := by
    apply localCircleHom_injective Z F
    rw [source16_circleAction_apply]
    exact mul_inv_eq_iff_eq_mul.mpr htv.symm.eq
  obtain ⟨P,hP⟩ := (isPGroup_zpowers_of_involution htC).exists_le_sylow
  have htP : tC ∈ P := hP (mem_zpowers tC)
  rcases hmodels with hep | ⟨hnodd,⟨es⟩⟩
  · obtain ⟨ep⟩ := hep
    have hfix := unitary_projective_omega_fixed J hn hJ hcard hfixed ep P tC htP htC.ne_one htC.sq_eq_one a ha hat
    have hq := (unitary_projective_omega_geometry J hn hJ hcard hfixed ep P).2.2.1
    have hd := fixed_omega_card_dvd_small_circle h r F hF hFM hne v eSmall P hfix
    rw [hq] at hd
    exact ⟨exponent_two_of_divides_sixty hn hd,⟨ep⟩⟩
  · have hfix := unitary_special_omega_fixed J hn hJ hcard hfixed es P tC htP htC.ne_one htC.sq_eq_one a ha hat
    have hq := (unitary_special_omega_geometry J hn hJ hcard hfixed es P).2.2.1
    have hd := fixed_omega_card_dvd_small_circle h r F hF hFM hne v eSmall P hfix
    rw [hq] at hd
    have hn2 := exponent_two_of_divides_sixty hn hd
    simp only [hn2] at hnodd
    norm_num at hnodd

end BenderSuzuki.ZD.Source16SmallField
