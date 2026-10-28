module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalModelBounds
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Excluding the two smallest terminal unitary models

For PSU₃(2), the exact root/torus decomposition makes a Sylow two-subgroup
self-normalizing. Fixed-space generation and faithful Sylow action force the
whole action to be faithful. For SU₃(2), the same argument after projection
puts the kernel in the scalar subgroup of order dividing three. The action
is therefore faithful or descends to a faithful action of PSU₃(2).

In both cases the quadratic square bound applies to the original actor and
fixed-space index. Transport through the actual model isomorphism contradicts
the upper index bound of the terminal V_t/Z_t section. `TerminalBound` uses
this to close the long epsilon-two branch, without any extra terminal
faithfulness or residual-fixed-space premise.

Source: DGS, *Groups and Graphs* (1985), (7.5), pp.130--131, using the
Chapter 5 quadratic bounds and the corrected fixed-space generation condition.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open BenderSuzuki.External
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

private theorem kernel_le_normalizer_of_fixed_generated
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (hf : RankOneSylowFacts T)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup D))
    (hne : (T : Subgroup D) ≠ ⊥) : σ.ker ≤ normalizer (T : Set D) := by
  apply le_sup_left.trans (hf.unique_maximal _ le_sup_right (lt_top_iff_ne_top.mpr ?_))
  intro hsup
  have hR : fixedSpace σ σ.ker = ⊤ := by
    apply top_unique
    intro w _ a
    change σ a w = w
    rw [show σ a = 1 from a.property]
    rfl
  have hfix : fixedSpace σ ⊤ = fixedSpace σ T := by
    have he := σ.invariants_comp_sup σ.ker (T : Subgroup D)
    change fixedSpace σ (σ.ker ⊔ (T : Subgroup D)) =
      fixedSpace σ σ.ker ⊓ fixedSpace σ T at he
    rwa [hsup,hR,top_inf_eq] at he
  have hspan : (⨆ g : D, (fixedSpace σ T).map (σ g)) ≤ fixedSpace σ ⊤ := by
    apply iSup_le
    rintro g _ ⟨v,hv,rfl⟩
    have hv' : v ∈ fixedSpace σ ⊤ := hfix.symm ▸ hv
    rw [show σ g v = v from hv' ⟨g,mem_top _⟩]
    exact hv'
  have htop : fixedSpace σ ⊤ = ⊤ := top_unique (hg ▸ hspan)
  apply hne
  apply bot_unique
  intro t ht
  have htk : t ∈ σ.ker := by
    apply LinearMap.ext
    intro w
    exact (show w ∈ fixedSpace σ ⊤ from htop.symm ▸ Submodule.mem_top) ⟨t,mem_top _⟩
  exact hd.le_bot ⟨htk,ht⟩

private theorem standard_psu_two_self_normalizing
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = T := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ J.specialToProjective_surjective
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hc) (by simpa using hconj)
  obtain ⟨_,ρ,p,_,_,_,hroot,_,hcard,_⟩ := huppert_II_10_12 J 2 hc hfixed hJ
  obtain ⟨R,H,hRU,_,hUN,_,hRH,_,hR,_,_,hH,hreg,_⟩ := hroot
  have hHb : H = ⊥ := card_eq_one.mp (by simpa using hH)
  rw [hHb,sup_bot_eq] at hRH
  let Ω := Unitary.unitaryIsotropicPoints J
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) Ω := MulAction.compHom Ω ρ
  have hRne : R ≠ ⊥ := by intro hr; simp [hr] at hR
  have hN := BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl R p hRU hRne hreg hUN
  have hNR : normalizer (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = R :=
    hN.trans hRH.symm
  let S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) := Sylow.ofCard R (by
    rw [hR,hcard]
    norm_num only
    rw [show (72 : ℕ) = 2^3*3^2 from rfl,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow,Nat.factorization_pow]
    norm_num [Nat.Prime.factorization])
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S T
  have hm : R.map (MulAut.conj g).toMonoidHom = (T : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  have hh := map_equiv_normalizer_eq R (MulAut.conj g)
  rw [hNR,hm] at hh
  exact hh.symm

/-- Every Sylow two-subgroup of the actual field-two projective model is self-normalizing. -/
theorem psu_two_self_normalizing
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = T := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ J.specialToProjective_surjective
  obtain ⟨C,hC⟩ := Unitary.FormTransport.exists_standard_basis J 1 (by decide)
    (by simpa using hc) (by simpa using hconj)
  let e := Unitary.FormTransport.projectiveEquiv J C hC
  have hh := standard_psu_two_self_normalizing (Unitary.FormTransport.standardForm J) rfl
    hc hconj (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  apply map_injective (f := e.toMonoidHom) e.injective
  have he := map_equiv_normalizer_eq (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) e
  change (normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))).map e.toMonoidHom =
    normalizer (((T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom) :
      Set (ProjectiveSpecialUnitaryMatrixGroup (Unitary.FormTransport.standardForm J))) at he
  exact he.trans hh

/-- Fixed generation and Sylow faithfulness detect the whole projective action. -/
theorem psu_two_fixed_generated_faithful
    {F W : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hne : (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≠ ⊥) : Function.Injective σ := by
  have hk := kernel_le_normalizer_of_fixed_generated σ T
    (rankOneSylowFacts_psu3 J 1 (by decide) (by simpa using hc) (by simpa using hconj) T)
    hg hd hne
  rw [psu_two_self_normalizing J hc hconj] at hk
  exact σ.ker_eq_bot_iff.mp (bot_unique (fun x hx => hd.le_bot ⟨hx,hk hx⟩))

private theorem kernel_coprime_two {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D)
    (hd : Disjoint σ.ker (T : Subgroup D)) : Nat.Coprime 2 (Nat.card σ.ker) := by
  obtain ⟨R,hR⟩ := T.exists_sylow_map_eq_inf_of_normal σ.ker
  have hRbot : (R : Subgroup σ.ker) = ⊥ := by
    apply map_injective σ.ker.subtype_injective
    simpa only [Subgroup.map_bot,hd.symm.eq_bot] using hR
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro he
  exact R.ne_bot_of_dvd_card he hRbot

/-- The analogous special-unitary action can have only a scalar kernel. -/
theorem su_two_kernel_le_scalar
    {F W : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) J.specialSubgroup W) (T : Sylow 2 J.specialSubgroup)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup J.specialSubgroup))
    (hne : (T : Subgroup J.specialSubgroup) ≠ ⊥) : σ.ker ≤ J.specialToProjective.ker := by
  let π := J.specialToProjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective _ J.specialToProjective_surjective
  let S := T.mapSurjective J.specialToProjective_surjective
  have hk := kernel_le_normalizer_of_fixed_generated σ T
    (rankOneSylowFacts_su3 J 1 (by decide) (by simpa using hc) (by simpa using hconj) T)
    hg hd hne
  have hm : σ.ker.map π ≤ (S : Subgroup _) := by
    have hh := map_mono (f := π) hk
    rw [T.normalizer_map_surjective π J.specialToProjective_surjective] at hh
    exact hh.trans_eq (psu_two_self_normalizing J hc hconj S)
  have hp := S.isPGroup'.to_le hm
  obtain ⟨n,hn⟩ := (IsPGroup.iff_card).mp hp
  have hdiv : Nat.card (σ.ker.map π) ∣ Nat.card σ.ker :=
    card_dvd_of_surjective (π.subgroupMap σ.ker) (π.subgroupMap_surjective σ.ker)
  have hn0 : n = 0 := by
    by_contra hpos
    have hh : 2 ∣ Nat.card σ.ker := by
      apply dvd_trans _ hdiv
      rw [hn]
      exact dvd_pow_self 2 hpos
    exact (Nat.prime_two.coprime_iff_not_dvd.mp (kernel_coprime_two σ T hd)) hh
  have hb : σ.ker.map π = ⊥ := card_eq_one.mp (by simpa only [hn0,pow_zero] using hn)
  intro g hg
  exact mem_bot.mp (hb ▸ mem_map_of_mem π hg)

/-- Descending a possible scalar kernel preserves the original quadratic square bound. -/
theorem su_two_fixed_generated_square_bound
    {F W : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) J.specialSubgroup W) (T : Sylow 2 J.specialSubgroup)
    (A : Subgroup J.specialSubgroup) (hAT : A ≤ T)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup J.specialSubgroup))
    (hne : (T : Subgroup J.specialSubgroup) ≠ ⊥) (hq : IsQuadratic σ A) :
    Nat.card A ^ 2 ≤ Nat.card (W ⧸ fixedSpace σ A) := by
  by_cases hk0 : σ.ker = ⊥
  · exact su3_two_quadratic_square_bound J hc hconj σ (σ.ker_eq_bot_iff.mp hk0) A hq
  let π := J.specialToProjective
  have hk := su_two_kernel_le_scalar J hc hconj σ T hg hd hne
  have hkc : Nat.card σ.ker = 3 := by
    have hv := (card_dvd_of_le hk).trans J.card_specialToProjective_ker_dvd_three
    exact ((Nat.dvd_prime Nat.prime_three).mp hv).resolve_left (fun he => hk0 (card_eq_one.mp he))
  have heq : σ.ker = π.ker := eq_of_le_of_card_ge hk (by
    rw [hkc]
    exact Nat.le_of_dvd (by decide) J.card_specialToProjective_ker_dvd_three)
  let eπ := QuotientGroup.quotientKerEquivOfSurjective π J.specialToProjective_surjective
  let ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W :=
    (QuotientGroup.lift π.ker σ heq.ge).comp eπ.symm.toMonoidHom
  have hρ (g : J.specialSubgroup) : ρ (π g) = σ g := by
    have he : eπ.symm (π g) = QuotientGroup.mk' π.ker g :=
      eπ.symm_apply_eq.mpr rfl
    change QuotientGroup.lift π.ker σ heq.ge (eπ.symm (π g)) = σ g
    rw [he]
    rfl
  have hf : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    apply bot_unique
    intro g hg
    obtain ⟨x,rfl⟩ := J.specialToProjective_surjective g
    change ρ (π x) = 1 at hg
    exact heq.le (by rwa [hρ] at hg)
  have hqρ : IsQuadratic ρ (A.map π) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
    simpa only [hρ] using hq a ha b hb w
  have hinj : Function.Injective (π.subgroupMap A) := by
    apply (π.subgroupMap A).ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    have hpa : π a = 1 := congrArg Subtype.val ha
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨heq.ge hpa,hAT a.property⟩))
  have hcard : Nat.card (A.map π) = Nat.card A :=
    (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,π.subgroupMap_surjective A⟩)).symm
  have hfixed : fixedSpace ρ (A.map π) = fixedSpace σ A := by
    rw [←fixedSpace_comp_map]
    have he : ρ.comp π = σ := MonoidHom.ext hρ
    rw [he]
  have hb := psu3_two_quadratic_square_bound J hc hconj ρ hf (A.map π) hqρ
  rwa [hcard,hfixed] at hb

private theorem terminal_model_transport {D H W : Type*} [Group D] [Finite D] [Group H]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (e : D ≃* H) (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (A : Subgroup D)
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup D))
    (hb : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) :
    let ρ := σ.comp e.symm.toMonoidHom
    let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
    let C := A.map e.toMonoidHom
    GeneratedByFixedSpace ρ S ∧ Disjoint ρ.ker (S : Subgroup H) ∧
      (S : Subgroup H) ≠ ⊥ ∧ IsQuadratic ρ C ∧ 1 < Nat.card C ∧
      Nat.card (W ⧸ fixedSpace ρ C) ≤ Nat.card C := by
  dsimp only
  have hgen := generatedByFixedSpace_of_equivariant_surjection σ
    (σ.comp e.symm.toMonoidHom) e.toMonoidHom LinearMap.id
    Function.surjective_id (by intro g w; simp) T hg
  have hdis : Disjoint (σ.comp e.symm.toMonoidHom).ker
      ((T : Subgroup D).map e.toMonoidHom) := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro _ ⟨hk,x,hx,rfl⟩
    have hxk : x ∈ σ.ker := by simpa using hk
    have hx1 := mem_bot.mp (hd.le_bot ⟨hxk,hx⟩)
    simp only [hx1,map_one,mem_bot]
  have hAc : Nat.card (A.map e.toMonoidHom) = Nat.card A := card_map_of_injective e.injective
  have hne : ((T : Subgroup D).map e.toMonoidHom) ≠ ⊥ := by
    intro hs
    have ha : A.map e.toMonoidHom = ⊥ := bot_unique ((map_mono hAT).trans hs.le)
    rw [ha,card_bot] at hAc
    omega
  have hquad : IsQuadratic (σ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
    simpa using hq a ha b hb w
  have hfixed : fixedSpace (σ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) = fixedSpace σ A := by
    rw [fixedSpace_comp_map,map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id D := by ext x; simp
    rw [he,map_id]
  exact ⟨hgen,hdis,hne,hquad,hAc.symm ▸ hA,by simpa only [hAc,hfixed] using hb⟩

/-- Neither field-two unitary model admits the literal terminal actor and index bound. -/
theorem small_unitary_fixed_generated_index_obstruction
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hm : IsSU D 3 2 ∨ ClassicalGroup.IsPSU D 3 2)
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (A : Subgroup D)
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup D))
    (hb : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) : False := by
  rcases hm with he | he
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := he
    let := hF
    let := hfin
    obtain ⟨hg',hd',hne,hq',hA',hb'⟩ := terminal_model_transport e σ T A hAT hA hq hg hd hb
    have hh := su_two_fixed_generated_square_bound J hcard hconj
      (σ.comp e.symm.toMonoidHom) (T.mapSurjective (f := e.toMonoidHom) e.surjective)
      (A.map e.toMonoidHom) (map_mono hAT) hg' hd' hne hq'
    nlinarith
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := he
    let := hF
    let := hfin
    obtain ⟨hg',hd',hne,hq',hA',hb'⟩ := terminal_model_transport e σ T A hAT hA hq hg hd hb
    have hf := psu_two_fixed_generated_faithful J hcard hconj
      (σ.comp e.symm.toMonoidHom) (T.mapSurjective (f := e.toMonoidHom) e.surjective)
      hg' hd' hne
    have hh := psu3_two_quadratic_square_bound J hcard hconj
      (σ.comp e.symm.toMonoidHom) hf (A.map e.toMonoidHom) hq'
    nlinarith

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
