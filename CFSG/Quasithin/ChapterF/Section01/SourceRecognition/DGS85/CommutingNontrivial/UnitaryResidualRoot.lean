module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaModule
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.SpecificGroups.SU3.BinaryRootFrattini.Images
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryGeneration

/-!
# Unitary residual intersections in the Chapter 8 counterexample

Odd-coset averaging and the perfect quadratic-pair decomposition split a
fixed-field SL₂ Sylow fixed vector into a cyclic displacement and a block-fixed
vector. If the full unitary Sylow fixes the central-root displacement, root–block
generation kills the latter vector. Every nonzero central-root subactor then
has the full displacement. The calculation uses the actual SU₃ → PSU₃ map.

The full-torus root calculation also shows that a subgroup of a large unitary
Sylow preserved by its normalizer lies in the omega-center or equals the Sylow.
Both results are applied to the literal residual intersection in `ResidualRoot`.
Source: DGS, Groups and Graphs (1985), proof of 8.3, printed pp.135–136;
the quadratic-pair step uses 5.8(d), with perfectness and averaging proved here.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private theorem fixed_le_cyclic_sup_global {D W : Type*} [Group D] [Finite D]
    [Group.IsPerfect D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (S : Sylow 2 D) (B : Subgroup D)
    (t : D) (ht : t ∈ S) (hS : IsQuadratic ρ S) (hB : IsQuadratic ρ B)
    (hgen : zpowers t ⊔ B = ⊤) :
    fixedSpace ρ S ≤ Coinvariants.ker (ρ.comp (zpowers t).subtype) ⊔ fixedSpace ρ ⊤ := by
  let σ := globalFixedQuotient ρ
  let q := (fixedSpace ρ ⊤).mkQ
  have hqt : IsQuadratic ρ (zpowers t) :=
    fun a ha b hb v => hS a ((zpowers_le.mpr ht) ha) b ((zpowers_le.mpr ht) hb) v
  have hmt : Coinvariants.ker (ρ.comp (zpowers t).subtype) ≤ fixedSpace ρ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩ s
    exact hS s s.property a ((zpowers_le.mpr ht) a.property) v
  have hmB : Coinvariants.ker (ρ.comp B.subtype) ≤
      (Coinvariants.ker (σ.comp B.subtype)).comap q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    change q (ρ a v-v) ∈ Coinvariants.ker (σ.comp B.subtype)
    rw [map_sub,←globalFixedQuotient_mk]
    exact Coinvariants.sub_mem_ker (ρ := σ.comp B.subtype) a (q v)
  have hdis := (quadratic_pair_quotient_decomposition ρ (zpowers t) B hgen hqt hB).2.2
  intro v hv
  obtain ⟨w,hw,hm⟩ := BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient ρ S
    (Coinvariants.ker ρ) (Coinvariants.sub_mem_ker (ρ := ρ)) v hv
  have hwf : w ∈ fixedSpace ρ ⊤ := fun a => hw a
  rw [moved_eq_sup_of_generates ρ (zpowers t) B hgen] at hm
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hm
  have hyS : y ∈ fixedSpace ρ S := by
    have hh := (fixedSpace ρ S).sub_mem
      ((fixedSpace ρ S).sub_mem hv (fixedSpace_antitone ρ le_top hwf)) (hmt hx)
    rw [←hxy] at hh
    simpa only [add_sub_cancel_left] using hh
  have hyq : q y ∈ fixedSpace σ (zpowers t) := by
    intro a
    change σ a (q y) = q y
    rw [globalFixedQuotient_mk]
    exact congrArg q (hyS ⟨a,(zpowers_le.mpr ht) a.property⟩)
  have hy0 : q y = 0 := hdis.le_bot ⟨hmB hy,hyq⟩
  have hyg : y ∈ fixedSpace ρ ⊤ := (Submodule.Quotient.mk_eq_zero _).mp hy0
  have he : v = x + (y+w) := by rw [←add_assoc,hxy,sub_add_cancel]
  rw [he]
  exact Submodule.mem_sup.mpr ⟨x,hx,y+w,(fixedSpace ρ ⊤).add_mem hyg hwf,rfl⟩

private theorem sl2_fixed_le_cyclic_sup_global
    {K W : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2,K) W)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (S : Sylow 2 SL(2,K)) (hq : IsQuadratic ρ S)
    (t : SL(2,K)) (ht : t ∈ S) (ht1 : t ≠ 1) :
    fixedSpace ρ S ≤ Coinvariants.ker (ρ.comp (zpowers t).subtype) ⊔ fixedSpace ρ ⊤ := by
  have hcard : 4 ≤ Nat.card S := by
    rw [←Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 S).toEquiv,Nat.card_congr Multiplicative.toAdd,hK]
    exact (show 4 = 2^2 by decide) ▸ Nat.pow_le_pow_right (by decide) hn
  have hK4 : 4 ≤ Nat.card K := hK.symm ▸ ((show 4 = 2^2 by decide) ▸ Nat.pow_le_pow_right (by decide) hn)
  let : Group.IsPerfect SL(2,K) := SL2SylowFixedRecognition.perfect hK4
  obtain ⟨g,hg⟩ := sl2_exists_quadratic_pair (by omega) hK S (S : Subgroup _) le_rfl hcard t ht ht1
  exact fixed_le_cyclic_sup_global ρ S _ t ht hq
    (SL2SylowFixedRecognition.quadratic_conjugate ρ hq g) hg

private theorem block_moved_le_cyclic_of_root_fixed
    {K D W : Type*} [Field K] [Finite K] [CharP K 2] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (j : SL(2,K) →* D)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (S : Sylow 2 SL(2,K)) (T : Subgroup D)
    (hgen : T ⊔ j.range = ⊤)
    (hq : IsQuadratic (ρ.comp j) S) (hf : fixedSpace ρ ⊤ = ⊥)
    (hfix : Coinvariants.ker ((ρ.comp j).comp (S : Subgroup SL(2,K)).subtype) ≤ fixedSpace ρ T)
    (t : SL(2,K)) (ht : t ∈ S) (ht1 : t ≠ 1) :
    Coinvariants.ker ((ρ.comp j).comp (S : Subgroup SL(2,K)).subtype) ≤
      Coinvariants.ker (ρ.comp (zpowers (j t)).subtype) := by
  let σ := ρ.comp j
  have hsmall : Coinvariants.ker (σ.comp (zpowers t).subtype) ≤
      Coinvariants.ker (σ.comp (S : Subgroup SL(2,K)).subtype) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := σ.comp (S : Subgroup SL(2,K)).subtype)
      ⟨a,(zpowers_le.mpr ht) a.property⟩ v
  intro v hv
  have hmS : Coinvariants.ker (σ.comp (S : Subgroup SL(2,K)).subtype) ≤ fixedSpace σ S :=
    (commutator_le_invariants_iff _).mpr (fun a b v => hq a a.property b b.property v)
  have hvS : v ∈ fixedSpace σ S := hmS hv
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp
    (sl2_fixed_le_cyclic_sup_global σ hn hK S hq t ht ht1 hvS)
  have hyT : y ∈ fixedSpace ρ T := by
    have hh := (fixedSpace ρ T).sub_mem (hfix hv) (hfix (hsmall hx))
    simpa only [add_sub_cancel_left] using hh
  have hyall : y ∈ fixedSpace ρ ⊤ := by
    rw [←hgen,show fixedSpace ρ (T ⊔ j.range) = fixedSpace ρ T ⊓ fixedSpace ρ j.range from ρ.invariants_comp_sup _ _]
    refine ⟨hyT,?_⟩
    rw [show j.range = (⊤ : Subgroup SL(2,K)).map j from MonoidHom.range_eq_map j,←fixedSpace_comp_map]
    exact hy
  have hy0 : y = 0 := by simpa only [hf,Submodule.mem_bot] using hyall
  rw [hy0,add_zero]
  apply (show Coinvariants.ker (σ.comp (zpowers t).subtype) ≤
    Coinvariants.ker (ρ.comp (zpowers (j t)).subtype) from ?_) hx
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,v⟩,rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp (zpowers (j t)).subtype)
    ⟨j a,by rw [←MonoidHom.map_zpowers]; exact mem_map_of_mem j a.property⟩ v



private theorem moved_comp_map {D E W : Type*} [Group D] [Group E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (f : D →* E) (A : Subgroup D) :
    Coinvariants.ker ((ρ.comp f).comp A.subtype) = Coinvariants.ker (ρ.comp (A.map f).subtype) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨a,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp (A.map f).subtype) ⟨f a,mem_map_of_mem f a.property⟩ v
  · rintro _ ⟨⟨⟨a,ha⟩,v⟩,rfl⟩
    obtain ⟨b,hb,rfl⟩ := ha
    exact Coinvariants.sub_mem_ker (ρ := (ρ.comp f).comp A.subtype) ⟨b,hb⟩ v

open BenderSuzuki.External HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots

private theorem block_root_image {K : Type*} [Field K] [CharP K 2]
    (J : HermitianForm 3 K) (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    (Matrix.SpecialLinearGroup.upperUnipotent (fixedField J)).map (block J hJ) = central J hJ := by
  have he (c : fixedField J) :
      block J hJ (Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one c) =
        hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd c)) := by
    apply Subtype.ext
    apply Units.ext
    rw [block_val]
    change _ = (!![1,0,(c : K);0,1,-J.conj 0;0,0,1] : Matrix (Fin 3) (Fin 3) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    obtain ⟨c,rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mp ha
    exact he c ▸ ⟨Multiplicative.ofAdd c,rfl⟩
  · rintro _ ⟨c,rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one c.toAdd,
      (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨c.toAdd,rfl⟩,he c.toAdd⟩

private theorem special_root_moved_le_cyclic
    {K W : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (J : HermitianForm 3 K) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W)
    (hq : IsQuadratic ρ (central J hJ)) (hf : fixedSpace ρ ⊤ = ⊥)
    (hfix : Coinvariants.ker (ρ.comp (central J hJ).subtype) ≤ fixedSpace ρ (specialRoot J hJ))
    (t : J.specialSubgroup) (ht : t ∈ central J hJ) (ht1 : t ≠ 1) :
    Coinvariants.ker (ρ.comp (central J hJ).subtype) ≤ Coinvariants.ker (ρ.comp (zpowers t).subtype) := by
  let S := Matrix.SpecialLinearGroup.upperUnipotentSylow (fixedField J) 2
  have hmap : (S : Subgroup SL(2,fixedField J)).map (block J hJ) = central J hJ := block_root_image J hJ
  obtain ⟨t₀,ht₀,he⟩ := hmap.symm ▸ ht
  have h₀ : t₀ ≠ 1 := fun hh => ht1 (by rw [←he,hh,map_one])
  have hq₀ : IsQuadratic (ρ.comp (block J hJ)) S := by
    intro a ha b hb v
    exact hq _ (hmap ▸ mem_map_of_mem _ ha) _ (hmap ▸ mem_map_of_mem _ hb) v
  have hc : Nat.card (fixedField J) = 2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  have hi := block_moved_le_cyclic_of_root_fixed ρ (block J hJ) hn hc S (specialRoot J hJ)
    (su3_root_block_generate J hJ hn hK hconj) hq₀ hf
    (by rw [moved_comp_map,hmap]; exact hfix) t₀ ht₀ h₀
  rwa [moved_comp_map,hmap,he] at hi

private theorem special_root_sylow {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2^n) :
    ∃ S : Sylow 2 J.specialSubgroup, (S : Subgroup J.specialSubgroup) = specialRoot J hJ := by
  have hu : Function.Injective (hermitianUnipotentSU J hJ) := by
    intro z w he
    apply Subtype.ext
    exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) he)
      (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) he)
  let R := HermitianForm.EvenTwoRank.rootSylow J hJ (by omega : 0<n) hK hfixed
  let ec := HermitianForm.SylowOmega.projectiveSylowEquivCoords J hn hK hfixed hJ R
  let es : hermitianUnipotentCoord J ≃* specialRoot J hJ := MonoidHom.ofInjective hu
  have hp : IsPGroup 2 (specialRoot J hJ) := (R.isPGroup'.of_equiv ec).of_equiv es
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hc : Nat.card S = Nat.card (specialRoot J hJ) := Nat.card_congr
    (((HermitianForm.SylowOmega.specialSylowEquivProjective J S).trans
      (HermitianForm.SylowOmega.projectiveSylowEquivCoords J hn hK hfixed hJ _)).trans es).toEquiv
  exact ⟨S,(eq_of_le_of_card_ge hS hc.le).symm⟩



private theorem moved_transport {D E W : Type*} [Group D] [Group E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (f : D ≃* E) (A : Subgroup D) :
    Coinvariants.ker ((ρ.comp f.symm.toMonoidHom).comp (A.map f.toMonoidHom).subtype) =
      Coinvariants.ker (ρ.comp A.subtype) := by
  rw [moved_comp_map,map_map]
  rw [show f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id D from
    MonoidHom.ext (fun x => f.symm_apply_apply x),Subgroup.map_id]

private theorem special_sylow_moved_le_actor
    {K W : Type*} [Field K] [Finite K]
    [AddCommGroup W] [Module (ZMod 2) W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (S : Sylow 2 J.specialSubgroup)
    (hq : IsQuadratic ρ (omegaCenterIn (S : Subgroup J.specialSubgroup)))
    (hf : fixedSpace ρ ⊤ = ⊥)
    (hfix : Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup J.specialSubgroup)).subtype) ≤ fixedSpace ρ S)
    (A : Subgroup J.specialSubgroup) (hA : A ≤ omegaCenterIn (S : Subgroup J.specialSubgroup)) (hne : A ≠ ⊥) :
    Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup J.specialSubgroup)).subtype) ≤
      Coinvariants.ker (ρ.comp A.subtype) := by
  let : CharP K 2 := charTwo_of_card hK
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨C,hC⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis J (2^n) hK hfixed
  let e := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨R,hR⟩ := special_root_sylow J₀ rfl hn hK hfixed
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J₀.specialSubgroup T R
  let f := e.trans (MulAut.conj g)
  have hmap : (S : Subgroup J.specialSubgroup).map f.toMonoidHom = specialRoot J₀ rfl := by
    rw [show f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,←map_map]
    exact (congrArg Sylow.toSubgroup hg).trans hR
  have hw := HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R
  have hΩ : (omegaCenterIn (S : Subgroup J.specialSubgroup)).map f.toMonoidHom = central J₀ rfl := by
    rw [NilesRankOneKernel.omegaCenterIn_map_injective _ f.injective,hmap,←hR,
      omegaCenterIn_eq_omegaOneAmbient,←hw.1]
    let : IsElementaryAbelian 2 (omegaOneAmbient (R : Subgroup J₀.specialSubgroup)) := hw.2.1
    rw [omegaOneAmbient_eq_self,hw.1]
    rw [hR,←central_eq_embedded_center J₀ rfl hn hK hfixed]
  let σ := ρ.comp f.symm.toMonoidHom
  have hqσ : IsQuadratic σ (central J₀ rfl) := by
    rw [←hΩ]
    apply quadratic_map_equivariant ρ σ f.toMonoidHom (LinearEquiv.refl _ _) _ hq
    intro x v
    change ρ x v = ρ (f.symm (f x)) v
    rw [f.symm_apply_apply]
  have hfσ : fixedSpace σ ⊤ = ⊥ := by
    rw [fixedSpace_comp_map,map_top_of_surjective _ f.symm.surjective]
    exact hf
  have hfixσ : Coinvariants.ker (σ.comp (central J₀ rfl).subtype) ≤ fixedSpace σ (specialRoot J₀ rfl) := by
    rw [←hΩ,moved_transport,←hmap,fixedSpace_comp_map,map_map]
    simpa only [show f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id J.specialSubgroup from MonoidHom.ext (fun x => f.symm_apply_apply x),Subgroup.map_id] using hfix
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hi := special_root_moved_le_cyclic J₀ rfl hn hK hconj σ hqσ hfσ hfixσ (f t)
    (hΩ ▸ mem_map_of_mem _ (hA ht)) (fun he => ht1 (f.injective (he.trans f.map_one.symm)))
  have hzmap : (zpowers t).map f.toMonoidHom = zpowers (f t) := MonoidHom.map_zpowers _ _
  rw [←hΩ,moved_transport,←hzmap,moved_transport] at hi
  apply hi.trans
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,v⟩,rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨a,(zpowers_le.mpr ht) a.property⟩ v

private theorem projective_sylow_moved_le_actor
    {K W : Type*} [Field K] [Finite K]
    [AddCommGroup W] [Module (ZMod 2) W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hq : IsQuadratic ρ (omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))))
    (hf : fixedSpace ρ ⊤ = ⊥)
    (hfix : Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).subtype) ≤ fixedSpace ρ S)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A ≤ omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) (hne : A ≠ ⊥) :
    Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).subtype) ≤
      Coinvariants.ker (ρ.comp A.subtype) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 S
  have homega : (omegaCenterIn (R : Subgroup J.specialSubgroup)).map J.specialToProjective =
      omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
    obtain ⟨C,hC⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis J (2^n) hK hfixed
    have hr := HermitianForm.SylowOmega.omega_of_special_equiv
      (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
      hn hK hfixed rfl (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC) R
    have hs := HermitianForm.SylowOmega.omega_of_projective_equiv
      (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
      hn hK hfixed rfl (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.projectiveEquiv J C hC) S
    let : IsElementaryAbelian 2 (omegaOneAmbient (R : Subgroup J.specialSubgroup)) := hr.2.1
    let : IsElementaryAbelian 2 (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) := hs.2.1
    rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
      ←hr.1,←hs.1,omegaOneAmbient_eq_self (omegaOneAmbient (R : Subgroup J.specialSubgroup)),
      omegaOneAmbient_eq_self (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))),←hR]
    exact HermitianForm.SylowOmega.special_sylow_omega_map J R
  let σ := ρ.comp J.specialToProjective
  let E := omegaCenterIn (R : Subgroup J.specialSubgroup) ⊓ A.comap J.specialToProjective
  have hEA : E.map J.specialToProjective = A := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro x hx
      obtain ⟨y,hy,he⟩ := homega.symm ▸ hA hx
      exact ⟨y,⟨hy,show J.specialToProjective y ∈ A from he.symm ▸ hx⟩,he⟩
  have hE : E ≠ ⊥ := by intro he; apply hne; rw [←hEA,he,Subgroup.map_bot]
  have hqσ : IsQuadratic σ (omegaCenterIn (R : Subgroup J.specialSubgroup)) := by
    intro a ha b hb v
    exact hq _ (homega ▸ mem_map_of_mem _ ha) _ (homega ▸ mem_map_of_mem _ hb) v
  have hfσ : fixedSpace σ ⊤ = ⊥ := by
    rw [fixedSpace_comp_map,map_top_of_surjective _ J.specialToProjective_surjective]
    exact hf
  have hfixσ : Coinvariants.ker (σ.comp (omegaCenterIn (R : Subgroup J.specialSubgroup)).subtype) ≤ fixedSpace σ R := by
    rw [moved_comp_map,homega,fixedSpace_comp_map]
    change _ ≤ fixedSpace ρ (R.mapSurjective J.specialToProjective_surjective : Subgroup _)
    rw [hR]
    exact hfix
  have hi := special_sylow_moved_le_actor J hn hK hconj σ R hqσ hfσ hfixσ E inf_le_left hE
  rwa [moved_comp_map,moved_comp_map,homega,hEA] at hi



/-- In a large unitary center action, if the full Sylow fixes the omega
 displacement, every nonzero elementary subactor has the whole displacement.
 The statement retains arbitrary Hermitian coordinates and both scalar covers. -/
theorem unitary_sylow_moved_le_actor
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU D 3 (2^n) ∨ IsSU D 3 (2^n))
    (ρ : Representation (ZMod 2) D W) (S : Sylow 2 D)
    (hq : IsQuadratic ρ (omegaCenterIn (S : Subgroup D)))
    (hf : fixedSpace ρ ⊤ = ⊥)
    (hfix : Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup D)).subtype) ≤ fixedSpace ρ S)
    (A : Subgroup D) (hA : A ≤ omegaCenterIn (S : Subgroup D)) (hne : A ≠ ⊥) :
    Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup D)).subtype) ≤
      Coinvariants.ker (ρ.comp A.subtype) := by
  have transport {E : Type} [Group E] (e : D ≃* E)
      (hmodel : ∀ (σ : Representation (ZMod 2) E W) (T : Sylow 2 E),
        IsQuadratic σ (omegaCenterIn (T : Subgroup E)) → fixedSpace σ ⊤ = ⊥ →
        Coinvariants.ker (σ.comp (omegaCenterIn (T : Subgroup E)).subtype) ≤ fixedSpace σ T →
        ∀ C : Subgroup E, C ≤ omegaCenterIn (T : Subgroup E) → C ≠ ⊥ →
        Coinvariants.ker (σ.comp (omegaCenterIn (T : Subgroup E)).subtype) ≤
          Coinvariants.ker (σ.comp C.subtype)) :
      Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup D)).subtype) ≤
        Coinvariants.ker (ρ.comp A.subtype) := by
    let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let σ := ρ.comp e.symm.toMonoidHom
    have ho : omegaCenterIn (T : Subgroup E) = (omegaCenterIn (S : Subgroup D)).map e.toMonoidHom :=
      (NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective (S : Subgroup D)).symm
    have hq' : IsQuadratic σ (omegaCenterIn (T : Subgroup E)) := by
      rw [ho]
      apply quadratic_map_equivariant ρ σ e.toMonoidHom (LinearEquiv.refl _ _) _ hq
      intro a v
      change ρ a v = ρ (e.symm (e a)) v
      rw [e.symm_apply_apply]
    have hf' : fixedSpace σ ⊤ = ⊥ := by
      rw [fixedSpace_comp_map,map_top_of_surjective _ e.symm.surjective]
      exact hf
    have hs' : fixedSpace σ T = fixedSpace ρ S := by
      rw [fixedSpace_comp_map]
      change fixedSpace ρ (((S : Subgroup D).map e.toMonoidHom).map e.symm.toMonoidHom) = _
      rw [map_map]
      simp only [show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id D from MonoidHom.ext (fun x => e.symm_apply_apply x),Subgroup.map_id]
    have hi := hmodel σ T hq' hf' (by rw [ho,moved_transport,hs']; exact hfix)
      (A.map e.toMonoidHom) (ho ▸ map_mono hA) (by
        intro he
        exact hne (Subgroup.map_injective e.injective (he.trans (Subgroup.map_bot _).symm)))
    rwa [ho,moved_transport,moved_transport] at hi
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact transport e (fun σ T => projective_sylow_moved_le_actor J hn hK hconj σ T)
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact transport e (fun σ T => special_sylow_moved_le_actor J hn hK hconj σ T)


private theorem projective_sylow_invariant_dichotomy
    {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hA : A ≤ S)
    (hN : normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ normalizer (A : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    A ≤ omegaCenterIn (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ∨ A = S := by
  let : CharP K 2 := charTwo_of_card hK
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨C,hC⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis J (2^n) hK hfixed
  let e := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.projectiveEquiv J C hC
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let R := HermitianForm.EvenTwoRank.rootSylow J₀ rfl (by omega : 0<n) hK hfixed
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective J₀.specialToProjective J₀.specialToProjective_surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J₀) T R
  let f := e.trans (MulAut.conj g)
  have hmap : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map f.toMonoidHom =
      projectiveRoot J₀ rfl := by
    rw [show f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,←map_map]
    exact congrArg Sylow.toSubgroup hg
  have htorus : projectiveTorus J₀ rfl ≤ normalizer (projectiveRoot J₀ rfl : Set (ProjectiveSpecialUnitaryMatrixGroup J₀)) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨k,rfl⟩ _ ⟨z,rfl⟩
    exact ⟨hermitianTorusAction J₀ k z,HermitianForm.EvenInner.projective_torus_action J₀ rfl k z |>.symm⟩
  have hN' : normalizer (projectiveRoot J₀ rfl : Set (ProjectiveSpecialUnitaryMatrixGroup J₀)) ≤
      normalizer (A.map f.toMonoidHom : Set (ProjectiveSpecialUnitaryMatrixGroup J₀)) := by
    rw [←hmap,←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
    exact map_mono hN
  have hq : 2 < 2^n := (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
  rcases HermitianForm.BinaryRootFrattini.projective_invariant_subgroup J₀ rfl hK hfixed hq
      (A.map f.toMonoidHom) (hmap ▸ map_mono hA) (htorus.trans hN') with hlo | he
  · left
    have hc := HermitianForm.BinaryRootFrattini.equiv_structure J₀ hK hfixed
      (HermitianForm.SylowOmega.projectiveSylowEquivCoords J₀ hn hK hfixed rfl R)
    have hfr : (frattini (projectiveRoot J₀ rfl)).map (projectiveRoot J₀ rfl).subtype ≤
        omegaCenterIn (projectiveRoot J₀ rfl) := by
      rintro _ ⟨x,hx,rfl⟩
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨x.property,?_,?_⟩
      · intro y hy
        exact congrArg Subtype.val (mem_center_iff.mp (hc.2 hx) ⟨y,hy⟩)
      · exact congrArg Subtype.val ((hc.1 x).mp hx)
    have hh := hlo.trans hfr
    rw [←hmap,←NilesRankOneKernel.omegaCenterIn_map_injective f.toMonoidHom f.injective] at hh
    exact (map_le_map_iff_of_injective f.injective).mp hh
  · right
    exact Subgroup.map_injective f.injective (he.trans hmap.symm)

private theorem special_sylow_invariant_dichotomy
    {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (S : Sylow 2 J.specialSubgroup) (A : Subgroup J.specialSubgroup) (hA : A ≤ S)
    (hN : normalizer (S : Set J.specialSubgroup) ≤ normalizer (A : Set J.specialSubgroup)) :
    A ≤ omegaCenterIn (S : Subgroup J.specialSubgroup) ∨ A = S := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let q := J.specialToProjective
  let T := S.mapSurjective (f := q) J.specialToProjective_surjective
  have hN' : normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ normalizer (A.map q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    change normalizer ((S : Subgroup J.specialSubgroup).map q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ _
    rw [←S.normalizer_map_surjective q J.specialToProjective_surjective]
    exact (map_mono hN).trans (A.le_normalizer_map q)
  rcases projective_sylow_invariant_dichotomy J hn hK hconj T (A.map q) (map_mono hA) hN' with hlo | he
  · left
    intro a ha
    have hmem := (mem_omegaCenterIn_iff _ _).mp (hlo (mem_map_of_mem q ha))
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hA ha,?_,?_⟩
    · intro s hs
      exact congrArg Subtype.val (HermitianForm.SylowOmega.specialProjection_injective_on_sylow J S
        (a₁ := ⟨s*a,(S : Subgroup J.specialSubgroup).mul_mem hs (hA ha)⟩)
        (a₂ := ⟨a*s,(S : Subgroup J.specialSubgroup).mul_mem (hA ha) hs⟩)
        (by change q (s*a) = q (a*s); rw [map_mul,map_mul]; exact hmem.2.1 _ (mem_map_of_mem q hs)))
    · exact congrArg Subtype.val (HermitianForm.SylowOmega.specialProjection_injective_on_sylow J S
        (a₁ := ⟨a^2,(S : Subgroup J.specialSubgroup).pow_mem (hA ha) 2⟩) (a₂ := 1)
        (by change q (a^2) = q 1; rw [map_pow,map_one]; exact hmem.2.2))
  · right
    apply le_antisymm hA
    intro s hs
    have hsA : q s ∈ A.map q := by rw [he]; exact mem_map_of_mem q hs
    obtain ⟨a,ha,heq⟩ := hsA
    have hae : a = s := congrArg Subtype.val
      (HermitianForm.SylowOmega.specialProjection_injective_on_sylow J S
        (a₁ := ⟨a,hA ha⟩) (a₂ := ⟨s,hs⟩) heq)
    exact hae ▸ ha

/-- A subgroup of a large unitary Sylow normalized by its full normalizer
lies in its omega-center or equals the Sylow. -/
theorem unitary_sylow_invariant_dichotomy {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : 2 ≤ n) (hu : ClassicalGroup.IsPSU D 3 (2^n) ∨ IsSU D 3 (2^n))
    (S : Sylow 2 D) (A : Subgroup D) (hA : A ≤ S)
    (hN : normalizer (S : Set D) ≤ normalizer (A : Set D)) :
    A ≤ omegaCenterIn (S : Subgroup D) ∨ A = S := by
  have transport {E : Type} [Group E] (e : D ≃* E)
      (hm : ∀ (T : Sylow 2 E) (C : Subgroup E), C ≤ T →
        normalizer (T : Set E) ≤ normalizer (C : Set E) →
        C ≤ omegaCenterIn (T : Subgroup E) ∨ C = T) :
      A ≤ omegaCenterIn (S : Subgroup D) ∨ A = S := by
    let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hn' : normalizer (T : Set E) ≤ normalizer (A.map e.toMonoidHom : Set E) := by
      change normalizer ((S : Subgroup D).map e.toMonoidHom : Set E) ≤ _
      rw [←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
      exact map_mono hN
    rcases hm T (A.map e.toMonoidHom) (map_mono hA) hn' with hlo | he
    · left
      change A.map e.toMonoidHom ≤ omegaCenterIn ((S : Subgroup D).map e.toMonoidHom) at hlo
      rw [←NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective] at hlo
      exact (map_le_map_iff_of_injective e.injective).mp hlo
    · right
      exact Subgroup.map_injective e.injective he
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact transport e (projective_sylow_invariant_dichotomy J hn hK hconj)
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact transport e (special_sylow_invariant_dichotomy J hn hK hconj)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
