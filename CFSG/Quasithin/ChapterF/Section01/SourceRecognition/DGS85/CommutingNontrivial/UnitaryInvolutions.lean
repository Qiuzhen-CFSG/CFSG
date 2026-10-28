module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryElementBounds
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# Unitary involution displacement on the original moving center

The full quotient Sylow omega-center acts quadratically by 8.1(h), and
has order q ≥ 4. After a Hermitian basis change and Sylow conjugation,
5.10(b) therefore bounds every involution's displacement by at least q².
The special-unitary action need not be faithful: quasisimplicity and the
prime scalar kernel show that it is either faithful or descends to a
faithful projective action on the same vectors. Both cases retain the
literal scalar projection and its restriction to the prescribed Sylow.

The source application constructs the actual center representation, its
nontriviality, full-omega quadraticity and original edge Sylow. Identity
coordinates return the bound to the original centralizer index for every
elementary subgroup of that edge Sylow escaping the local core, including
an image of order two. `ReciprocalVanishing` applies this to the remaining
moving-intersection case of 8.2. The proof does not assume faithfulness of
the full special-unitary center action or a bound on the critical distance.

Source: DGS, *Groups and Graphs* (1985), 5.10(b), pp.111--112;
8.1(h) and 8.2(**), pp.133--135.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open Representation.SU3.CubicDegree.InnerActors
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open HermitianForm.BorelTorus.EvenCenterAction
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

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

private theorem special_root_element_index_nontrivial
    {K W : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1)
    (hq : IsQuadratic ρ (central J hJ))
    (t : J.specialSubgroup) (ht : t ∈ central J hJ) (ht1 : t ≠ 1) :
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
  have hc : 4 ≤ Nat.card (centralImage J hJ) := by
    rw [centralImage_card J hJ hfixed]
    exact (show 4=2^2 by decide) ▸ Nat.pow_le_pow_right (by decide) hn
  have hc' : 4 ≤ Nat.card (central J hJ) := by
    rw [←hcentral] at hc
    exact hc.trans (Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _))
  rcases special_action_kernel_dichotomy J hn hK hconj ρ hnt with hf | hk
  · simpa only [←pow_mul,Nat.mul_comm n 2] using
      su3_root_element_field_index J hJ hn hK hconj ρ hf _ le_rfl hc' hq t ht ht1
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
    have hquad : IsQuadratic σ (centralImage J hJ) := by
      rw [←hcentral]
      exact quadratic_map_equivariant ρ σ J.specialToProjective (LinearEquiv.refl _ _) heq hq
    have ht2 : t^2=1 := by
      obtain ⟨R,hR⟩ := exists_sylowCenter_containing_central J hJ hn hK hfixed
      have hw := HermitianForm.SylowOmega.special_sylow_omega J hn hK hfixed hJ R
      let : IsElementaryAbelian 2 (sylowCenter R) := by
        change IsElementaryAbelian 2 ((center R).map (R : Subgroup J.specialSubgroup).subtype)
        rw [←hw.1]
        exact hw.2.1
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) t (hR ht)
    have htq : J.specialToProjective t ≠ 1 := by
      intro hh
      have ht3 : t^3=1 := congrArg Subtype.val (J.specialToProjective_ker_cube ⟨t,hh⟩)
      have : t=1 := by simpa only [pow_succ,ht2,one_mul] using ht3
      exact ht1 this
    have hi := psu3_root_element_field_index J hJ hn hK hconj σ hf _ le_rfl hc hquad
      (J.specialToProjective t) (hcentral ▸ mem_map_of_mem J.specialToProjective ht) htq
    have hecomp : σ.comp J.specialToProjective = ρ := by ext g v; exact LinearMap.congr_fun (he g) v
    rw [←MonoidHom.map_zpowers,←fixedSpace_comp_map,hecomp] at hi
    simpa only [←pow_mul,Nat.mul_comm n 2] using hi

private theorem special_sylow_involution_index
    {K W : Type*} [Field K] [Finite K]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1)
    (S : Sylow 2 J.specialSubgroup) (hq : IsQuadratic ρ (omegaCenterIn (S : Subgroup J.specialSubgroup)))
    (t : J.specialSubgroup) (htS : t ∈ S) (ht : IsInvolution t) :
    (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)) := by
  let : CharP K 2 := charTwo_of_card hK
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  let J₀ := standardForm J
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hK hfixed
  let e := specialEquiv J C hC
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨R,hR⟩ := exists_sylowCenter_containing_central J₀ rfl hn hK hfixed
  have hcentralcard : Nat.card (central J₀ rfl) = 2^n := by
    let f := (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl).comp (centralCoord J₀)
    have hu : Function.Injective (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl) := by
      intro z w he
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 1) he)
        (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 2) he)
    have hf : Function.Injective f := hu.comp (centralCoord_injective J₀)
    change Nat.card f.range = 2^n
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_congr Multiplicative.toAdd]
    exact hfixed
  have hw := HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R
  have hRcard : Nat.card (sylowCenter R) = 2^n := by
    rw [sylowCenter,←hw.1]
    exact hw.2.2
  have hReq : sylowCenter R = central J₀ rfl :=
    (eq_of_le_of_card_ge hR (hRcard.trans hcentralcard.symm).le).symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J₀.specialSubgroup T R
  let f := e.trans (MulAut.conj g)
  have hmap : (S : Subgroup J.specialSubgroup).map f.toMonoidHom = (R : Subgroup J₀.specialSubgroup) := by
    rw [show f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,←map_map]
    exact congrArg Sylow.toSubgroup hg
  have hΩ : (omegaCenterIn (S : Subgroup J.specialSubgroup)).map f.toMonoidHom = central J₀ rfl := by
    rw [NilesRankOneKernel.omegaCenterIn_map_injective _ f.injective,hmap,
      omegaCenterIn_eq_omegaOneAmbient,←hw.1]
    let : IsElementaryAbelian 2 (omegaOneAmbient (R : Subgroup J₀.specialSubgroup)) := hw.2.1
    rw [omegaOneAmbient_eq_self,hw.1]
    exact hReq
  let σ := ρ.comp f.symm.toMonoidHom
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨x,hx⟩ := hnt
    refine ⟨f x,?_⟩
    change ρ (f.symm (f x)) ≠ 1
    simpa only [f.symm_apply_apply] using hx
  have hqσ : IsQuadratic σ (central J₀ rfl) := by
    rw [←hΩ]
    apply quadratic_map_equivariant ρ σ f.toMonoidHom (LinearEquiv.refl _ _) _ hq
    intro x v
    change ρ x v = ρ (f.symm (f x)) v
    rw [f.symm_apply_apply]
  have htΩ : f t ∈ central J₀ rfl := by
    rw [←hReq,sylowCenter,←hw.1]
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl _
      (hmap ▸ mem_map_of_mem f.toMonoidHom htS)
    exact (map_pow f t 2).symm.trans (by rw [ht.2,map_one])
  have hi := special_root_element_index_nontrivial J₀ rfl hn hK hconj σ hσ hqσ
    (f t) htΩ (fun he => ht.1 (f.injective (he.trans f.map_one.symm)))
  change (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace (ρ.comp f.symm.toMonoidHom) (zpowers (f t))) at hi
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hi
  simpa only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,f.symm_apply_apply] using hi

private theorem projective_sylow_involution_index
    {K W : Type*} [Field K] [Finite K]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W) (hnt : ∃ g, ρ g ≠ 1)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hq : IsQuadratic ρ (omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (htS : t ∈ S) (ht : IsInvolution t) :
    (2^n)^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 S
  let f := HermitianForm.SylowOmega.specialSylowEquivProjective J R
  have hRt : t ∈ (R.mapSurjective J.specialToProjective_surjective : Subgroup _) := hR.symm ▸ htS
  let x : R := f.symm ⟨t,hRt⟩
  have hx : J.specialToProjective x = t := by
    rw [←HermitianForm.SylowOmega.specialSylowEquivProjective_apply J R x]
    exact congrArg Subtype.val (f.apply_symm_apply ⟨t,hRt⟩)
  have hx2 : x^2=1 := by
    apply f.injective
    rw [map_pow,f.apply_symm_apply,map_one]
    apply Subtype.ext
    exact ht.2
  have hx1 : (x : J.specialSubgroup) ≠ 1 := by
    intro he
    exact ht.1 (hx.symm.trans (he ▸ J.specialToProjective.map_one))
  have homega : (omegaCenterIn (R : Subgroup J.specialSubgroup)).map J.specialToProjective =
      omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
    obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hK hfixed
    have hr := HermitianForm.SylowOmega.omega_of_special_equiv (standardForm J)
      hn hK hfixed rfl (specialEquiv J C hC) R
    have hs := HermitianForm.SylowOmega.omega_of_projective_equiv (standardForm J)
      hn hK hfixed rfl (projectiveEquiv J C hC) S
    let : IsElementaryAbelian 2 (omegaOneAmbient (R : Subgroup J.specialSubgroup)) := hr.2.1
    let : IsElementaryAbelian 2 (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) := hs.2.1
    rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
      ←hr.1,←hs.1,omegaOneAmbient_eq_self (omegaOneAmbient (R : Subgroup J.specialSubgroup)),
      omegaOneAmbient_eq_self (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))),←hR]
    exact HermitianForm.SylowOmega.special_sylow_omega_map J R
  let σ := ρ.comp J.specialToProjective
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨t,ht⟩ := hnt
    obtain ⟨x,rfl⟩ := J.specialToProjective_surjective t
    exact ⟨x,ht⟩
  have hqσ : IsQuadratic σ (omegaCenterIn (R : Subgroup J.specialSubgroup)) := by
    intro a ha b hb v
    exact hq (J.specialToProjective a) (homega ▸ mem_map_of_mem _ ha)
      (J.specialToProjective b) (homega ▸ mem_map_of_mem _ hb) v
  have hi := special_sylow_involution_index J hn hK hconj σ hσ R hqσ x x.property
    ⟨hx1,congrArg Subtype.val hx2⟩
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers,hx] at hi
  exact hi

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem source_moving_omega_elementary_field_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D)
    (c : ℕ)
    (hbound : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W],
      ∀ (ρ : Representation (ZMod 2) D W), (∃ g, ρ g ≠ 1) →
        ∀ S : Sylow 2 D, IsQuadratic ρ (omegaCenterIn (S : Subgroup D)) →
          ∀ t : D, t ∈ S → IsInvolution t → c^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAE : A ≤ (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hAQ : ¬ A ≤ Q (family P) w.val) :
    c^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let F := family P
  let L := d.localGroup w.val
  let Z₀ := Z F w.val
  let q₀ := QuotientGroup.mk' (pCore 2 L)
  let q := e.toMonoidHom.comp q₀
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d
    (show (graph F).Adj a' w.val from w.property).symm
  let Y := quotientSylowOmegaPreimage L R
  let S := R.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hz,_,_,_,T,_⟩ := source_moving_actor h d hc hab hd hb hcomm w hm
  obtain ⟨ρ,hact⟩ := source_exists_center_quotient_action h d w.val e
  obtain ⟨_,_,_,hres⟩ := source_center_module_prepared_of_center_eq_bot h d w.val hz T e ρ hact
  have hZL : Z₀ ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  let δ := centerSection L Z₀ hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) q ρ hact
  have hYS : (Y.subgroupOf L).map q = omegaCenterIn (S : Subgroup D) := by
    rw [←map_map,show (Y.subgroupOf L).map q₀ = omegaCenterIn ((R : Subgroup L).map q₀) from
      quotientSylowOmegaPreimage_image L R,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,map_map]
    rfl
  have hquad : IsQuadratic ρ (omegaCenterIn (S : Subgroup D)) := by
    rw [←hYS]
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le L Z₀ ⊥ Y ρ q δ
    have he := (source_critical_quotient_omega_action h hB d hc hab hd hb hcomm models w hm R hR).2
    rw [commutator_comm Y,commutator_comm Y]
    exact he.le
  have hAR : A ≤ (R : Subgroup L).map L.subtype := hR.symm ▸ hAE
  have hAL : A ≤ L := hAR.trans (map_subtype_le _)
  have hAS : (A.subgroupOf L).map q ≤ S := by
    apply map_mono
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y=x) ▸ hy
  let Aq := (A.subgroupOf L).map q
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 Aq := IsElementaryAbelian.map q
  have hne : Aq ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [local_quotient_kernel F d w.val e] at hk
    exact hAQ (fun a ha => hk (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! ht
    have he : fixedSpace ρ (pResidual 2 D) = ⊤ := by
      apply top_unique
      intro z _ g
      change ρ g z = z
      rw [ht]
      rfl
    exact top_ne_bot (he.symm.trans hres)
  obtain ⟨t,ht,ht1⟩ := Aq.bot_or_exists_ne_one.resolve_left hne
  have hi := hbound (Additive Z₀) ρ hnt S hquad t (hAS ht)
    ⟨ht1,elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht⟩
  have hle : Nat.card (Additive Z₀ ⧸ fixedSpace ρ (zpowers t)) ≤
      Nat.card (Additive Z₀ ⧸ fixedSpace ρ Aq) := by
    let : Finite (Additive Z₀ ⧸ fixedSpace ρ Aq) := Finite.of_surjective _ (fixedSpace ρ Aq).mkQ_surjective
    exact Nat.card_le_card_of_surjective _
      (Submodule.factor_surjective (fixedSpace_antitone ρ (zpowers_le.mpr ht)))
  have hidx := center_action_fixed_index L Z₀ A hZL δ.normalized hAL q ρ hact
  exact hidx ▸ hi.trans hle

/-- The full quotient omega-center from 8.1(h) supplies the large quadratic
actor required by 5.10(b). Every nonzero elementary actor in the original
edge Sylow therefore has displacement index at least q², including actors
of order two and special-unitary actions with a scalar kernel. -/
theorem source_moving_special_unitary_involution_field_square_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* J.specialSubgroup)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAE : A ≤ (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hAQ : ¬ A ≤ Q (family P) w.val) :
    (2^n)^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  apply source_moving_omega_elementary_field_bound h hB d hc hab hd hb hcomm models w hm e (2^n) ?_ A hAE hAQ
  intro W _ _ _ ρ hnt S hq t htS ht
  exact special_sylow_involution_index J hn hK hconj ρ hnt S hq t htS ht

/-- The corresponding bound for the actual PSU₃ quotient. Its prescribed
Sylow and involution are lifted through the odd scalar kernel, retaining
the original fixed space on the original source center. -/
theorem source_moving_projective_unitary_involution_field_square_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAE : A ≤ (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hAQ : ¬ A ≤ Q (family P) w.val) :
    (2^n)^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply source_moving_omega_elementary_field_bound h hB d hc hab hd hb hcomm models w hm e (2^n) ?_ A hAE hAQ
  intro W _ _ _ ρ hnt S hq t htS ht
  exact projective_sylow_involution_index J hn hK hconj ρ hnt S hq t htS ht

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
