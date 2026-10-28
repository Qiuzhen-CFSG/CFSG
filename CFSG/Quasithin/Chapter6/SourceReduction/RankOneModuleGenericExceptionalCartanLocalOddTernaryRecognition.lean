module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOddTernary
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOddTernaryRecognition
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.SourceCases
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeRankOneSelection
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.RankOneSource
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# The original residual section in odd-ternary Cartan containers

The original seed equality makes O²(H) a C-component. Compare it with the
actual E.2.2 source component before choosing a model. The exchanged row
contradicts normality. Every section of the odd-ternary containing quotient
has two-rank at most three, excluding the two diagram models; cyclic Sylow
commutators exclude the binary unitary source model. The linear/Suzuki
comparison has trivial kernel, giving a simple rank-one intrinsic quotient.

Restrict the original full Sylow to the literal containing image in Y/O₂(Y).
The odd-ternary section theorems now apply with their hypotheses discharged:
O²(H)/O₂(O²(H)) is PSL₂(4), its actual image in Y/O₂(Y) is SL₂(5), and the
containing prime is five. The original right Hall subgroup is cubic.
Central projective kernels and the distinct source and two-core quotients
are retained throughout. The final theorem strengthens the same original
sieve, preserving every preceding exclusion and the original module.
Normalization by the entire escaping Cartan intersection remains to be proved.

Source: Aschbacher--Smith A.3.12(9), A.3.14, A.3.21(a), E.2.2 and
5.1.10--13, printed pp.47--50,55,215--216,634--637 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels

private theorem section_rank {E Q Z : Type*} [Group E] [Finite E]
    [Group Q] [Finite Q] [Group Z] [Finite Z]
    (i : E →* Q) (hi : Function.Injective i)
    (f : E →* Z) (hf : Function.Surjective f)
    (hr : ∀ (P : Subgroup Q) (N : Subgroup P) [N.Normal], primeRank 2 (P ⧸ N) ≤ 3) :
    primeRank 2 Z ≤ 3 := by
  let e := MonoidHom.ofInjective hi
  let g := f.comp e.symm.toMonoidHom
  let a := QuotientGroup.quotientKerEquivOfSurjective g (hf.comp e.symm.surjective)
  rw [←primeRank_equiv 2 a]
  exact hr i.range g.ker

private theorem cover_section_restrictions {E Q Z : Type*} [Group E] [Finite E]
    [Group Q] [Finite Q] [Group Z] [Finite Z]
    (q : E →* Q) (hq : Function.Surjective q) (hk : Nat.Coprime 2 (Nat.card q.ker))
    (hr : ∀ (P : Subgroup Q) (N : Subgroup P) [N.Normal], primeRank 2 (P ⧸ N) ≤ 3)
    (hc : ∀ P : Sylow 2 Q, IsCyclic (commutator P))
    (B : Subgroup E) (f : B →* Z) (hf : Function.Surjective f) :
    primeRank 2 Z ≤ 3 ∧ (∀ P : Sylow 2 Z, IsCyclic (commutator P)) := by
  have hcE : ∀ P : Sylow 2 E, IsCyclic (commutator P) := by
    intro P
    let R : Sylow 2 Q := Sylow.nonempty.some
    let e := Sylow.equivOfSurjectiveCoprime q hq hk P R
    exact derived_cyclic_of_injective e.toMonoidHom e.injective (hc R)
  refine ⟨?_,sylow_derived_cyclic_of_surjective f hf
    (sylow_derived_cyclic_of_injective B.subtype B.subtype_injective hcE)⟩
  let T : Sylow 2 B := Sylow.nonempty.some
  obtain ⟨S,hS⟩ := (T.isPGroup'.map B.subtype).exists_le_sylow
  let j : T →* S := (B.subtype.comp (T : Subgroup B).subtype).codRestrict S
    (fun t => hS (mem_map_of_mem B.subtype t.property))
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : E)) hh))
  let R : Sylow 2 Q := Sylow.nonempty.some
  let e := Sylow.equivOfSurjectiveCoprime q hq hk S R
  let i := (R : Subgroup Q).subtype.comp (e.toMonoidHom.comp j)
  have hi : Function.Injective i := (R : Subgroup Q).subtype_injective.comp (e.injective.comp hj)
  rw [(T.mapSurjective hf).primeRank_eq]
  exact section_rank i hi (f.subgroupMap (T : Subgroup B)) (f.subgroupMap_surjective _) hr

private theorem projective_odd_sections {Q Z : Type*} [Group Q] [Finite Q]
    [Group Z] [Finite Z] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Q 3 p ∨ ClassicalGroup.IsPSU Q 3 p)
    (B : Subgroup Q) (f : B →* Z) (hf : Function.Surjective f) :
    primeRank 2 Z ≤ 3 ∧ (∀ P : Sylow 2 Z, IsCyclic (commutator P)) := by
  have hc : ∀ P : Sylow 2 Q, IsCyclic (commutator P) := by
    apply ChapterA.Section03.SourceEmbeddings.AlternatingEight.odd_model_sylow_derived_cyclic
    rcases hm with hm | hm
    · exact .linear_three p hp ho hm
    · exact .unitary_three p hp ho hm
  refine ⟨?_,sylow_derived_cyclic_of_surjective f hf
    (sylow_derived_cyclic_of_injective B.subtype B.subtype_injective hc)⟩
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,_,⟨e⟩⟩
  · exact section_rank (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective)
      f hf (Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
        (hF.symm ▸ ho))
  · exact section_rank (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective)
      f hf (Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three
        J (hF.symm ▸ ho.pow))

private theorem odd_ternary_sections {Q Z : Type*} [Group Q] [Finite Q]
    [Group Z] [Finite Z] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Q 3 p ∨ ClassicalGroup.IsPSU Q 3 p ∨
      IsSL Q 3 p ∨ IsSU Q 3 p)
    (B : Subgroup Q) (f : B →* Z) (hf : Function.Surjective f) :
    primeRank 2 Z ≤ 3 ∧ (∀ P : Sylow 2 Z, IsCyclic (commutator P)) := by
  rcases hm with hm | hm | hm | hm
  · exact projective_odd_sections hp ho (.inl hm) B f hf
  · exact projective_odd_sections hp ho (.inr hm) B f hf
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let q := (Matrix.PSL3.projection F).comp e.toMonoidHom
    have hq : Function.Surjective q := (Matrix.PSL3.projection_surjective F).comp e.surjective
    have h3 : IsPGroup 3 q.ker := by
      have hz : IsPGroup 3 (center SL(3,F)) := by
        intro x
        refine ⟨1,?_⟩
        exact orderOf_dvd_iff_pow_eq_one.mp
          ((orderOf_dvd_natCard x).trans (Matrix.SL3.card_center_dvd_three F))
      rw [show q.ker = (Matrix.PSL3.projection F).ker.comap e.toMonoidHom from rfl,
        Matrix.PSL3.projection_ker]
      exact hz.comap_of_injective e.toMonoidHom e.injective
    have hk : Nat.Coprime 2 (Nat.card q.ker) := by
      obtain ⟨k,hk⟩ := h3.exists_card_eq
      rw [hk]
      exact (show Odd (3^k) from (by decide : Odd 3).pow).coprime_two_left
    exact cover_section_restrictions q hq hk
      (Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
        (hF.symm ▸ ho))
      (ChapterA.Section03.SourceEmbeddings.AlternatingEight.odd_model_sylow_derived_cyclic
        (.linear_three p hp ho ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)) B f hf
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let q := J.specialToProjective.comp e.toMonoidHom
    have hq : Function.Surjective q := J.specialToProjective_surjective.comp e.surjective
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective q hq
    have h3 : IsPGroup 3 q.ker := by
      have hz : IsPGroup 3 J.specialToProjective.ker :=
        fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩
      exact hz.comap_of_injective e.toMonoidHom e.injective
    have hk : Nat.Coprime 2 (Nat.card q.ker) := by
      obtain ⟨k,hk⟩ := h3.exists_card_eq
      rw [hk]
      exact (show Odd (3^k) from (by decide : Odd 3).pow).coprime_two_left
    exact cover_section_restrictions q hq hk
      (Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three
        J (hF.symm ▸ ho.pow))
      (ChapterA.Section03.SourceEmbeddings.AlternatingEight.odd_model_sylow_derived_cyclic
        (.unitary_three p hp ho ⟨F,inferInstance,inferInstance,J,hF,hc,⟨MulEquiv.refl _⟩⟩)) B f hf

variable {G : Type*} [Group G] [Finite G]

private theorem odd_container_section_restrictions
    {K Y : Subgroup G} (C : Subgroup Y) (hC : C.IsCComponent)
    (hKC : K ≤ C.map Y.subtype) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)
    {Z : Type*} [Group Z] [Finite Z]
    (f : (K ⧸ pCore 2 K) →* Z) (hf : Function.Surjective f) :
    primeRank 2 Z ≤ 3 ∧ (∀ P : Sylow 2 Z, IsCyclic (commutator P)) := by
  have hKY := hKC.trans (map_subtype_le C)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Kbar := (K.subgroupOf Y).map q
  let Cbar := C.map q
  have hKC' : K.subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Kbar ≤ Cbar := map_mono hKC'
  let U := Kbar.subgroupOf Cbar
  let eC := (cComponentTwoCoreQuotientEquiv hC).symm
  let r := q.subgroupMap (K.subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := (subgroupOfEquivOfLe hKY).symm
  let e₁ := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let b := (subgroupOfEquivOfLe hle).symm
  let e₃ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let eK : (K ⧸ pCore 2 K) ≃* (U ⧸ pCore 2 U) := e₁.trans (e₂.trans e₃)
  have hmC : ClassicalGroup.IsPSL Cbar 3 p ∨ ClassicalGroup.IsPSU Cbar 3 p ∨
      IsSL Cbar 3 p ∨ IsSU Cbar 3 p := by
    rcases hm with hm | hm | hm | hm
    · exact .inl (hm.of_mulEquiv eC)
    · exact .inr (.inl (hm.of_mulEquiv eC))
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact .inr (.inr (.inl ⟨F,inferInstance,inferInstance,hF,⟨eC.trans e⟩⟩))
    · obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
      exact .inr (.inr (.inr ⟨F,inferInstance,inferInstance,J,hF,hj,⟨eC.trans e⟩⟩))
  exact odd_ternary_sections hp ho hmC U
    ((f.comp eK.symm.toMonoidHom).comp (QuotientGroup.mk' (pCore 2 U)))
    (hf.comp (eK.symm.surjective.comp (QuotientGroup.mk'_surjective _)))

open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem intrinsic_source_surjection
    {X : Type*} [Group X] [Finite X]
    {M C : Subgroup X} (hC : C.IsCComponent) (hO : pCore 2 X ≤ sourceKernel M) :
    ∃ v : (C ⧸ pCore 2 C) →* sourceImage M C, Function.Surjective v := by
  let eC := cComponentTwoCoreQuotientEquiv hC
  let q := QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) hO
  let r : actorImage C →* sourceImage M C :=
    (q.comp (actorImage C).subtype).codRestrict _ (by
      rintro ⟨x,k,hk,rfl⟩
      exact ⟨k,hk,rfl⟩)
  have hr : Function.Surjective r := by
    rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨QuotientGroup.mk' (pCore 2 X) k,k,hk,rfl⟩,rfl⟩
  exact ⟨r.comp eC.toMonoidHom,hr.comp eC.surjective⟩

open Matrix BenderSuzuki.MatrixGroups
private theorem no_unitary_cyclic_derived
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hcyc : ∀ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCyclic (commutator S)) : False := by
  let S := HermitianForm.EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed
  let e := HermitianForm.SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ S
  let : IsCyclic (commutator (BenderSuzuki.External.hermitianUnipotentCoord J)) :=
    derived_cyclic_of_surjective e.toMonoidHom e.surjective (hcyc S)
  let : IsCyclic (center (BenderSuzuki.External.hermitianUnipotentCoord J)) :=
    isCyclic_of_le (_root_.SU3.EvenInvolutionResidual.root_structure J (2^n) hcard hfixed hJ).2.2
  let : IsCyclic (center S) := isCyclic_of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  obtain ⟨he,hE,hc⟩ := HermitianForm.SylowOmega.projective_sylow_omega J hn hcard hfixed hJ S
  let := hE
  have hcy : IsCyclic (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) := by
    rw [he]
    exact isCyclic_of_surjective ((S : Subgroup _).subtype.subgroupMap (center S))
      ((S : Subgroup _).subtype.subgroupMap_surjective _)
  have hd := IsElementaryAbelian.exponent_dvd_p 2
    (omegaOneAmbient (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
  rw [hcy.exponent_eq_card,hc] at hd
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  have hge := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  norm_num at hge
  omega

/-- In the original unmoved odd-ternary row the source is a single linear or
Suzuki component, and its intrinsic two-core quotient is simple and rank one. -/
theorem residual_rankOne_simple_of_odd_ternary
    {T : Sylow 2 G} {L W H Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hR : (pResidual 2 H).IsCComponent)
    (C : Subgroup Y) (hC : C.IsCComponent) (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) :
    ChapterF.Source.IsRankOneModel ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∧
      IsSimpleGroup ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
  let S := T.subtype hH.1.1.2
  have hP := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen
  let M := ChapterB.minimalParabolicMax S hP
  obtain ⟨K,f,hK,hqs,_,hf,hcases⟩ :=
    ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.source_binary_cases_generating_knownSimple
      (Chapter3.sqtk_of_mem_H h.qtke hH.1.1.1) S hP hgen
  have hKR : K = pResidual 2 H := by
    apply hK.eq_of_le hR
    let := hK.perfect
    apply le_sInf
    rintro N ⟨hn,hN⟩
    let := hn
    let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
    exact (le_solvableResidual_of_isPerfect K).trans (solvableResidual_le_of_solvable_quotient N)
  subst K
  let eR := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eQ := QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)
  obtain ⟨v,hv⟩ := intrinsic_source_surjection hK (twoCore_le_sourceKernel S hP)
  have hb := odd_container_section_restrictions C hC hRC hp ho hm
    (v.comp eQ.symm.toMonoidHom) (hv.comp eQ.symm.surjective)
  cases hcases with
  | exchanged hc hm =>
    obtain ⟨t,_,hne,_⟩ := hc.exchanged_product
    exact (hne (mem_normalizer_iff_map_conj_eq.mp
      (show t⁻¹ ∈ normalizer (pResidual 2 H : Set H) by
        rw [normalizer_eq_top]; exact mem_top _)).symm).elim
  | diagram hc hd =>
    rcases hd with ⟨F,_,_,_,_,hF,e,_,_⟩ | ⟨F,_,_,_,_,hF,e,_,_⟩
    · have hr := hb.1
      rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by omega) hF] at hr
      omega
    · have hr := hb.1
      rw [primeRank_equiv 2 e,
        Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_rank hF (by omega)] at hr
      omega
  | bender hc hd =>
    rcases hd with hd | ⟨F,_,_,_,J,hJ,hf,hF,_,hfix,e,_⟩
    · have hr := Prime.single_linear_suzuki_component_quotient hK hqs
        (twoCore_le_sourceKernel S hP) hc hd
      let g := DiagramHall.linearSourceComparison S hP (pResidual 2 H)
      have hg := ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.rank_one_comparison_kernel_isTwoGroup
        S hP (pResidual 2 H) hK hqs hc hd
      let eK := cComponentTwoCoreQuotientEquiv hK
      have hzero : pCore 2 (actorImage (pResidual 2 H)) = ⊥ := by
        change pCore 2 ((pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H))) = ⊥
        rw [←pCore_map_iso 2 eK,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
      have hker : g.ker = ⊥ := le_bot_iff.mp
        ((show g.ker ≤ pCore 2 (actorImage (pResidual 2 H)) from le_sSup ⟨inferInstance,hg⟩).trans_eq hzero)
      let e := eK.trans (MulEquiv.ofBijective g
        ⟨(MonoidHom.ker_eq_bot_iff g).mp hker,DiagramHall.linearSourceComparison_surjective S hP _⟩)
      have hs : IsSimpleGroup (sourceImage M (pResidual 2 H)) := by
        rcases hd with ⟨F,_,_,_,hf,hF,a,_⟩ | ⟨m,hm,_,a,_⟩
        · have hl : 3 < Nat.card F := by
            have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hf
            norm_num at hh
            omega
          exact a.isSimpleGroup_congr.mpr (ProjectiveSpecialLinearGroup.rank_two_simple hl)
        · exact a.isSimpleGroup_congr.mpr (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
      let := hs
      exact ⟨hr,e.isSimpleGroup⟩
    · exact (no_unitary_cyclic_derived J hf hJ hF hfix
        (sylow_derived_cyclic_of_surjective e.toMonoidHom e.surjective hb.2)).elim

private theorem five_section_through_cubic_kernel
    {Y Z : Type*} [Group Y] [Finite Y] [Group Z] [Finite Z]
    (S : Sylow 2 Y) (U : Subgroup Y)
    (hl : U ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Y) ≤ normalizer (U : Set Y))
    (e5 : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 5))
    (f : Y →* Z) (hf : Function.Surjective f) (hk : IsPGroup 3 f.ker)
    {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL Z 3 q ∨ ClassicalGroup.IsPSU Z 3 q) :
    q = 5 ∧ Chapter1.Section02.LocalModels.IsSL U 2 5 := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let r := f.subgroupMap U
  have h3 : IsPGroup 3 r.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let : Group.IsNilpotent r.ker := h3.isNilpotent
  let : Group.IsPerfect U := by
    let := hl.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show U ≤ U ⊔ (S : Subgroup Y) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (U ⧸ pCore 2 U) := e5.isSimpleGroup
  have h2 := PerfectCoreTwoExtension.ker_isTwoGroup r
  have hi : Function.Injective r := (MonoidHom.ker_eq_bot_iff r).mp
    (disjoint_self.mp (h2.disjoint_of_coprime h3 (by decide)))
  let e : U ≃* U.map f := MulEquiv.ofBijective r ⟨hi,f.subgroupMap_surjective U⟩
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let e5' := eq.symm.trans e5
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f
  have hn' := (map_mono (f := f) hn).trans (le_normalizer_map f)
  have hq5 := ChapterA.Section03.SourceEmbeddings.odd_three_five_section_parameter
    (S.mapSurjective hf) (U.map f) hl' hn' ⟨e5'⟩ hq ho hm
  obtain ⟨F,_,_,hF,⟨a⟩⟩ :=
    (ChapterA.Section03.SourceEmbeddings.odd_three_five_section_models
      (S.mapSurjective hf) (U.map f) hl' hn' e5' hq ho hm).2
  exact ⟨hq5,F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩

private theorem odd_ternary_five_section
    {Y : Type*} [Group Y] [Finite Y]
    (S : Sylow 2 Y) (U : Subgroup Y)
    (hl : U ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Y) ≤ normalizer (U : Set Y))
    (e5 : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 5))
    {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL Y 3 q ∨ ClassicalGroup.IsPSU Y 3 q ∨
      Chapter1.Section02.LocalModels.IsSL Y 3 q ∨
      Chapter1.Section02.LocalModels.IsSU Y 3 q) :
    q = 5 ∧ Chapter1.Section02.LocalModels.IsSL U 2 5 := by
  rcases hm with hm | hm | hm | hm
  · exact ⟨ChapterA.Section03.SourceEmbeddings.odd_three_five_section_parameter
        S U hl hn ⟨e5⟩ hq ho (.inl hm),
      (ChapterA.Section03.SourceEmbeddings.odd_three_five_section_models
        S U hl hn e5 hq ho (.inl hm)).2⟩
  · exact ⟨ChapterA.Section03.SourceEmbeddings.odd_three_five_section_parameter
        S U hl hn ⟨e5⟩ hq ho (.inr hm),
      (ChapterA.Section03.SourceEmbeddings.odd_three_five_section_models
        S U hl hn e5 hq ho (.inr hm)).2⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let f := (Matrix.PSL3.projection F).comp e.toMonoidHom
    have hf : Function.Surjective f := (Matrix.PSL3.projection_surjective F).comp e.surjective
    have hk : IsPGroup 3 f.ker := by
      have hz : IsPGroup 3 (center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
        intro x
        refine ⟨1,?_⟩
        exact orderOf_dvd_iff_pow_eq_one.mp
          ((orderOf_dvd_natCard x).trans (Matrix.SL3.card_center_dvd_three F))
      rw [show f.ker = (Matrix.PSL3.projection F).ker.comap e.toMonoidHom from rfl,
        Matrix.PSL3.projection_ker]
      exact hz.comap_of_injective e.toMonoidHom e.injective
    exact five_section_through_cubic_kernel S U hl hn e5 f hf hk hq ho
      (.inl ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let f := J.specialToProjective.comp e.toMonoidHom
    have hf : Function.Surjective f := J.specialToProjective_surjective.comp e.surjective
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective f hf
    have hk : IsPGroup 3 f.ker := by
      have hz : IsPGroup 3 J.specialToProjective.ker :=
        fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩
      exact hz.comap_of_injective e.toMonoidHom e.injective
    exact five_section_through_cubic_kernel S U hl hn e5 f hf hk hq ho
      (.inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨MulEquiv.refl _⟩⟩)

/-- The original residual has PSL₂(4) two-core quotient; its literal image in
Y/O₂(Y) is SL₂(5), and the odd-ternary field is forced to have order five. -/
theorem residual_section_of_odd_ternary
    {T : Sylow 2 G} {L W H Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (hHY : H ≤ Y)
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) :
    p = 5 ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      IsSL (((residual H).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 2 5 := by
  have hR' : (pResidual 2 H).IsCComponent := by
    have hh := hR.1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  obtain ⟨hmodel,hsimple⟩ := residual_rankOne_simple_of_odd_ternary h hH hgen hR' C hC hRC hp ho hm
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hHY
  have hTY := hH.1.1.2.trans hHY
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlq hle (hC.map_quotient (pCore 2 Y)).subnormal
  let U := Rbar.subgroupOf Cbar
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hnU : (Q : Subgroup Cbar) ≤ normalizer (U : Set Cbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hle]
    exact comap_mono hn
  let r := q.subgroupMap ((residual H).subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e₁ := e₀.trans (subgroupOfEquivOfLe hRY).symm
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ := (subgroupOfEquivOfLe hle).symm
  let eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* (U ⧸ pCore 2 U) :=
    (QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)).trans
      (e₂.trans (QuotientGroup.congr _ _ e₃ (pCore_map_iso 2 e₃)))
  let : IsSimpleGroup ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := hsimple
  let : IsSimpleGroup (U ⧸ pCore 2 U) := eR.symm.isSimpleGroup
  let : Group.IsPerfect U := by
    let := hU.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show U ≤ U ⊔ (Q : Subgroup Cbar) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let eC := (cComponentTwoCoreQuotientEquiv hC).symm
  have hmC : ClassicalGroup.IsPSL Cbar 3 p ∨ ClassicalGroup.IsPSU Cbar 3 p ∨
      IsSL Cbar 3 p ∨ IsSU Cbar 3 p := by
    rcases hm with hm | hm | hm | hm
    · exact .inl (hm.of_mulEquiv eC)
    · exact .inr (.inl (hm.of_mulEquiv eC))
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact .inr (.inr (.inl ⟨F,inferInstance,inferInstance,hF,⟨eC.trans e⟩⟩))
    · obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
      exact .inr (.inr (.inr ⟨F,inferInstance,inferInstance,J,hF,hj,⟨eC.trans e⟩⟩))
  have hfour := Prime.OddTernary.right_quotient_four Q U hnU (hmodel.of_equiv eR.symm) hp ho hmC
  have hfourOrig := hfour.of_mulEquiv eR
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hfour
  let e5 := a.trans (ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  obtain ⟨hp5,E,_,_,hE,⟨b⟩⟩ := odd_ternary_five_section Q U hU hnU e5 hp ho hmC
  exact ⟨hp5,hfourOrig,E,inferInstance,inferInstance,hE,
    ⟨(subgroupOfEquivOfLe hle).symm.trans b⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The original sieve identifies the residual quotient, the actual SL₂(5) image,
the containing prime, and the prescribed right Hall order in every odd-ternary row. -/
theorem localCartan_escape_seed_oddTernary_section_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) →
          K = residual H ∧ p = 5 ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
            IsSL (((residual H).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 2 5 ∧
            Nat.card B = 3) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd⟩ :=
    localCartan_escape_seed_oddTernary_residual_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,?_⟩
  intro p hp ho hm
  have he := hOdd p hp ho hm
  obtain ⟨hp5,hfour,hsl⟩ := LocalSieve.residual_section_of_odd_ternary h hH hgen hY.2
    (he ▸ hKL) C hC (he ▸ hKC) hp ho hm
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hfour
    exact ⟨eq.symm.trans (a.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  exact ⟨he,hp5,hfour,hsl,LocalSieve.right_hall_card_three_of_residual_A5 h hH hgen c hA5⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
