module
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryElementBounds
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.EvenTwoRank

/-!
# Involutions in large quadratic unitary actors

Every nonidentity element of an elementary quadratic actor of order at least
four moves at least two field degrees in a nontrivial binary representation
of SU₃(q) or PSU₃(q), q ≥ 4. Conjugate the actor into the standard central
root subgroup and apply the root-element bound. For a special unitary action,
the possible odd scalar kernel is retained; for a projective actor, lift
through that same scalar quotient without changing its order or fixed space.

Source: DGS85, Groups and Graphs, (5.10)(b), pp.110–112. The critical
constituent application is in DGS85/CommutingNontrivial/UnitaryEndingBounds.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open Representation.SU3.CubicDegree.InnerActors
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open HermitianForm.BorelTorus.EvenCenterAction
open scoped IsMulCommutative
namespace Representation.RankOne.QuadraticRecognition

private theorem special_action_kernel_dichotomy
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1) :
    Function.Injective ρ ∨ J.specialToProjective.ker ≤ ρ.ker := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  let := J.special_isQuasisimple_of_fixed_card hq hK hfixed
  have hz := HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hK hconj
  have hker := J.specialToProjective_ker_eq_center hz
  have hle : ρ.ker ≤ J.specialToProjective.ker := by
    rw [hker]
    rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top ρ.ker with he | he
    · exact he
    · obtain ⟨g,hg⟩ := hnt
      exact (hg (show g ∈ ρ.ker from he.symm ▸ mem_top g)).elim
  by_cases hf : Function.Injective ρ
  · exact Or.inl hf
  · right
    have hdiv := (card_dvd_of_le hle).trans J.card_specialToProjective_ker_dvd_three
    have hc : Nat.card ρ.ker = 3 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv with hc | hc
      · exact (hf (ρ.ker_eq_bot_iff.mp ((eq_bot_iff_card _).mpr hc))).elim
      · exact hc
    have hu : Nat.card J.specialToProjective.ker ≤ 3 :=
      Nat.le_of_dvd (by decide) J.card_specialToProjective_ker_dvd_three
    exact (eq_of_le_of_card_ge hle (by omega)).ge

private theorem special_large_root_element_index_nontrivial
    {K W : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup J.specialSubgroup) (hA : A ≤ central J hJ)
    (hAc : 4 ≤ Nat.card A) (hq : IsQuadratic ρ A)
    (t : J.specialSubgroup) (ht : t ∈ A) (ht1 : t ≠ 1) :
    (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  have hcentral : (central J hJ).map J.specialToProjective = centralImage J hJ := by
    rw [central,MonoidHom.map_range,centralImage]
    apply congrArg MonoidHom.range
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (J.specialToProjective (BenderSuzuki.External.hermitianUnipotentSU J hJ (centralCoord J x)) :
      Matrix.ProjGenLinGroup (Fin 3) K) =
      (BenderSuzuki.External.hermitianUnipotentPSU J hJ (centralCoord J x) : Matrix.ProjGenLinGroup (Fin 3) K)
    rw [J.specialToProjective_apply_val,BenderSuzuki.External.hermitianUnipotentPSU_val]
    rfl
  rcases special_action_kernel_dichotomy J hn hK hconj ρ hnt with hf | hk
  · simpa only [←pow_mul,Nat.mul_comm n 2] using
      su3_root_element_field_index J hJ hn hK hconj ρ hf A hA hAc hq t ht ht1
  · have hkU : J.specialToProjective.ker ≤ ρ.asGroupHom.ker := by
      intro g hg
      apply Units.ext
      exact hk hg
    let τ := J.specialToProjective.liftOfSurjective J.specialToProjective_surjective ⟨ρ.asGroupHom,hkU⟩
    let σ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W := (Units.coeHom _).comp τ
    have he (g : J.specialSubgroup) : σ (J.specialToProjective g) = ρ g :=
      congrArg Units.val (J.specialToProjective.liftOfRightInverse_comp_apply
        (Function.surjInv J.specialToProjective_surjective)
        (Function.rightInverse_surjInv J.specialToProjective_surjective) ⟨ρ.asGroupHom,hkU⟩ g)
    have hσ : ∃ g, σ g ≠ 1 := by
      obtain ⟨g,hg⟩ := hnt
      exact ⟨J.specialToProjective g,by rwa [he]⟩
    let := BenderSuzuki.External.huppert_II_10_13 J (2^n)
      ((by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)) hK hfixed
    have hf : Function.Injective σ := by
      apply σ.ker_eq_bot_iff.mp
      rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | hb
      · exact hb
      · obtain ⟨g,hg⟩ := hσ
        exact (hg (show g ∈ σ.ker from hb.symm ▸ mem_top g)).elim
    have heq (g : J.specialSubgroup) (v : W) :
        (LinearEquiv.refl (ZMod 2) W) (ρ g v) =
          σ (J.specialToProjective g) ((LinearEquiv.refl (ZMod 2) W) v) := by
      exact LinearMap.congr_fun (he g).symm v
    have hquad : IsQuadratic σ (A.map J.specialToProjective) :=
      quadratic_map_equivariant ρ σ J.specialToProjective (LinearEquiv.refl _ _) heq hq
    have hAc' : 4 ≤ Nat.card (A.map J.specialToProjective) := by
      have hi : Function.Injective (J.specialToProjective.comp A.subtype) := by
        apply (J.specialToProjective.comp A.subtype).ker_eq_bot_iff.mp
        apply bot_unique
        intro x hx
        have hx3 : (x : J.specialSubgroup)^3 = 1 :=
          congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩)
        obtain ⟨R,hR⟩ := exists_sylowCenter_containing_central J hJ hn hK hfixed
        have hw := HermitianForm.SylowOmega.special_sylow_omega J hn hK hfixed hJ R
        let : IsElementaryAbelian 2 (sylowCenter R) := by
          change IsElementaryAbelian 2 ((center R).map (R : Subgroup J.specialSubgroup).subtype)
          rw [←hw.1]
          exact hw.2.1
        have hx2 : (x : J.specialSubgroup)^2 = 1 :=
          elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : J.specialSubgroup) (hR (hA x.property))
        have he : (x : J.specialSubgroup) = 1 := by
          simpa only [pow_succ,hx2,one_mul] using hx3
        exact Subtype.ext he
      have hc : Nat.card (A.map J.specialToProjective) = Nat.card A := by
        have hr : (J.specialToProjective.comp A.subtype).range = A.map J.specialToProjective := by
          rw [MonoidHom.range_comp,range_subtype]
        rw [←hr]
        exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm
      rwa [hc]
    have ht2 : t^2=1 := by
      obtain ⟨R,hR⟩ := exists_sylowCenter_containing_central J hJ hn hK hfixed
      have hw := HermitianForm.SylowOmega.special_sylow_omega J hn hK hfixed hJ R
      let : IsElementaryAbelian 2 (sylowCenter R) := by
        change IsElementaryAbelian 2 ((center R).map (R : Subgroup J.specialSubgroup).subtype)
        rw [←hw.1]
        exact hw.2.1
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) t (hR (hA ht))
    have htq : J.specialToProjective t ≠ 1 := by
      intro hh
      have ht3 : t^3=1 := congrArg Subtype.val (J.specialToProjective_ker_cube ⟨t,hh⟩)
      have : t=1 := by simpa only [pow_succ,ht2,one_mul] using ht3
      exact ht1 this
    have hi := psu3_root_element_field_index J hJ hn hK hconj σ hf (A.map J.specialToProjective)
      ((map_mono hA).trans_eq hcentral) hAc' hquad
      (J.specialToProjective t) (mem_map_of_mem J.specialToProjective ht) htq
    have hecomp : σ.comp J.specialToProjective = ρ := by ext g v; exact LinearMap.congr_fun (he g) v
    rw [←MonoidHom.map_zpowers,←fixedSpace_comp_map,hecomp] at hi
    simpa only [←pow_mul,Nat.mul_comm n 2] using hi

/-- Every nonidentity element of a large elementary quadratic actor moves q² vectors.
The representation may have a scalar kernel. -/
theorem su3_elementary_element_field_square
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup J.specialSubgroup) [IsElementaryAbelian 2 A] (hAc : 4 ≤ Nat.card A)
    (hq : IsQuadratic ρ A) (t : J.specialSubgroup) (ht : t ∈ A) (ht1 : t ≠ 1) :
    (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)) := by
  let : CharP K 2 := charTwo_of_card hK
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  let J₀ := standardForm J
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hK hfixed
  let e := specialEquiv J C hC
  let A₀ := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map _
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A₀).exists_le_sylow
  have hAZ : A₀ ≤ sylowCenter P := by
    rw [sylowCenter,←(HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl P).1]
    rw [←omegaOneAmbient_eq_self A₀]
    exact omegaOneAmbient_mono hAP
  obtain ⟨R,hR⟩ := exists_sylowCenter_containing_central J₀ rfl hn hK hfixed
  have hcentralcard : Nat.card (central J₀ rfl) = 2^n := by
    let f := (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl).comp
      (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J₀)
    have hu : Function.Injective (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl) := by
      intro z w he
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 1) he)
        (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 2) he)
    have hf : Function.Injective f := hu.comp
      (HermitianForm.BorelTorus.EvenCenterAction.centralCoord_injective J₀)
    change Nat.card f.range = 2^n
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    exact hfixed
  have hRcard : Nat.card (sylowCenter R) = 2^n := by
    rw [sylowCenter,←(HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R).1]
    exact (HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R).2.2
  have hReq : sylowCenter R = central J₀ rfl :=
    (eq_of_le_of_card_ge hR (hRcard.trans hcentralcard.symm).le).symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J₀.specialSubgroup P R
  let f := e.trans (MulAut.conj g)
  have hAf : A.map f.toMonoidHom ≤ central J₀ rfl := by
    have hz : (sylowCenter P).map (MulAut.conj g).toMonoidHom = sylowCenter R := by
      rw [sylowCenter,map_embeddedCenter _ _ (MulAut.conj g).injective]
      exact congrArg (fun T : Subgroup J₀.specialSubgroup => (center T).map T.subtype)
        (congrArg Sylow.toSubgroup hg)
    rw [show f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,←map_map]
    exact (map_mono hAZ).trans_eq (hz.trans hReq)
  let σ := ρ.comp f.symm.toMonoidHom
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨x,hx⟩ := hnt
    refine ⟨f x,?_⟩
    change ρ (f.symm (f x)) ≠ 1
    simpa only [f.symm_apply_apply] using hx
  have hqσ : IsQuadratic σ (A.map f.toMonoidHom) := by
    apply quadratic_map_equivariant ρ σ f.toMonoidHom (LinearEquiv.refl _ _) _ hq
    intro x v
    change ρ x v = ρ (f.symm (f x)) v
    rw [f.symm_apply_apply]
  have hb := special_large_root_element_index_nontrivial J₀ rfl hn hK hconj σ hσ
    (A.map f.toMonoidHom) hAf (by rwa [card_map_of_injective f.injective])
    hqσ (f t) (mem_map_of_mem _ ht) (fun he => ht1 (f.map_eq_one_iff.mp he))
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hb
  simpa only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,f.symm_apply_apply] using hb

/-- The same involution bound on the projective carrier, using an elementary
lift through its canonical odd scalar kernel. -/
theorem psu3_elementary_element_field_square
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W)
    (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    [IsElementaryAbelian 2 A] (hAc : 4 ≤ Nat.card A)
    (hq : IsQuadratic ρ A)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : t ∈ A) (ht1 : t ≠ 1) :
    (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)) := by
  let σ := ρ.comp J.specialToProjective
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨x,hx⟩ := hnt
    obtain ⟨y,rfl⟩ := J.specialToProjective_surjective x
    exact ⟨y,hx⟩
  obtain ⟨D,hD,hDA,hDc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    J.specialToProjective J.specialToProjective_surjective
    (Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker) A
  let : IsElementaryAbelian 2 D := hD
  obtain ⟨s,hs,hst⟩ := hDA.symm ▸ ht
  have hs1 : s ≠ 1 := fun he => ht1 (by rw [←hst,he,map_one])
  have hqD : IsQuadratic σ D := by
    intro x hx y hy v
    exact hq (J.specialToProjective x) (hDA ▸ mem_map_of_mem _ hx)
      (J.specialToProjective y) (hDA ▸ mem_map_of_mem _ hy) v
  have hb := su3_elementary_element_field_square J hn hK hconj σ hσ D
    (hDc.symm ▸ hAc) hqD s hs hs1
  rwa [fixedSpace_comp_map,MonoidHom.map_zpowers,hst] at hb

end Representation.RankOne.QuadraticRecognition
