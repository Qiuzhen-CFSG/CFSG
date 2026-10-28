module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.ModuleKernel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.CubicModule
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.OddRankOne
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# Faithful non-FF sections of the actual swapped components

Each original component survives faithfully in the literal core-quotient
module. Perfectness constructs a noncentral Irr⁺ section; the central-kernel
theorem and simplicity make its central quotient faithful. The original
odd-prime congruences exclude every FF parameter in the proved B.4 sieve.
The same construction works after removing the full fixed subspace.

The consumer constructs these sections from the original marked pure point,
contrary ambient Sylow assumption and fixed-subgroup premise. It retains
the exact conjugation formula, both original component markings, the normal
join and the cubic bound. SQTK is inherited from the original containing
group, rather than added as a classification premise.

These component sections are not yet a pair of sections invariant under
the same cubic actor. Constructing that common actor geometry and excluding
the remaining swapped case, followed by ambient Sylow, core, fusion and
abelian closure, remain with qt-d-double-natural-pure-fusion. The original
fixed-subgroup premise remains with qt-rank-two-ms93 and final
qt-d-double-natural-centralizers.
Source: Aschbacher--Smith B.1.11, B.4.2 and 12.1.4,
printed pp.73,86,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem faithful_component_section
    {Q U : Type*} [Group Q] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (A : Subgroup Q) (hA : IsComponent Q A) [IsSimpleGroup A] :
    ∃ I, ∃ hI : IsIrrPlus ρ A I,
      Function.Injective (centralQuotientRepresentation ρ A I hI.choose) := by
  let := hA.2
  have hne : A ≠ ⊥ := by
    intro he
    have hh : Subsingleton A := he ▸ inferInstance
    exact not_subsingleton A hh
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf A hne
  have hz : center A = ⊥ :=
    (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  refine ⟨I,hI,(MonoidHom.ker_eq_bot_iff _).mp (bot_unique ?_)⟩
  intro a ha
  have hc := (centralSection_kernel_le_centralizer ρ A A le_rfl I hI hI.choose
    A.le_normalizer (mem_map_of_mem A.subtype ha)).2
  have hm : a ∈ center A := mem_center_iff.mpr (fun b =>
    Subtype.ext ((mem_centralizer_iff.mp hc) b b.property))
  exact hz ▸ hm

/-- Every original component image has a faithful irreducible central section
in the actual module, and also in its quotient by all fixed vectors. -/
theorem local_quotient_component_sections
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (XiQuotient (localJoin T L)) U)
    (hf : Function.Injective ρ)
    (A : Subgroup (XiQuotient (localJoin T L)))
    (hA : IsComponent (XiQuotient (localJoin T L)) A)
    (he : Nonempty (A ≃* XiQuotient L)) :
    (∃ I, ∃ hI : IsIrrPlus ρ A I,
      Function.Injective (centralQuotientRepresentation ρ A I hI.choose)) ∧
    (∃ I, ∃ hI : IsIrrPlus (fixedQuotient ρ ⊤) A I,
      Function.Injective (centralQuotientRepresentation (fixedQuotient ρ ⊤) A I hI.choose)) := by
  let : IsSimpleGroup A := he.some.isSimpleGroup
  exact ⟨faithful_component_section ρ hf A hA,
    faithful_component_section (fixedQuotient ρ ⊤)
      (faithful_fixedQuotient_of_core ρ hf (pCore_quotient_pCore_eq_bot 2)) A hA⟩

private theorem odd_prime_irreducible_not_ff
    {Q U : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [IsQuasisimple Q]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Q 2 p) (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    ¬ IsFFModule ρ := by
  intro hff
  let L : Subgroup Q := ⊤
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (topEquiv : L ≃* Q).symm
  let : IsSimpleGroup L := (topEquiv : L ≃* Q).isSimpleGroup
  have hz : center L = ⊥ :=
    (inferInstance : (center L).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp he))
  let e : (L ⧸ center L) ≃* Q :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans topEquiv
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hm' : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ 1) :=
    ⟨F,inferInstance,inferInstance,by simpa only [pow_one] using hF,⟨e.trans eF⟩⟩
  have hi' : IsIrreducible (ρ.comp L.subtype) :=
    (irreducible_comp_surjective_iff L.subtype topEquiv.surjective ρ).mpr hi
  have hc : cubicRatio ρ ≤ 2 :=
    ((isFFModule_iff_cubicRatio_le_one ρ).mp hff).trans (by norm_num)
  have hh : ChapterK.RankOne.SourceHypotheses ρ L :=
    ⟨hsq,generalizedFitting_eq_top_of_quasisimple,inferInstance,hf,hi',hc⟩
  have hlo : 4 ≤ p ^ 1 := by simpa only [pow_one] using (show 4 ≤ p by omega)
  rcases ChapterB.SourceClassification.odd_pslTwo_parameters hh hff hp ho
    (Or.inl rfl) hlo hm' with ⟨he,_⟩ | ⟨he,_⟩ | ⟨he,_⟩ <;> omega

/-- The odd-prime source models left by the original congruence sieve admit
no faithful irreducible FF section. Both group identifications are literal. -/
theorem local_quotient_component_nonFF_sections
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (XiQuotient (localJoin T L)) U)
    (hf : Function.Injective ρ)
    (A : Subgroup (XiQuotient (localJoin T L)))
    (hA : IsComponent (XiQuotient (localJoin T L)) A)
    (he : Nonempty (A ≃* XiQuotient L))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient L))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    (∃ I, ∃ hI : IsIrrPlus ρ A I,
      Function.Injective (centralQuotientRepresentation ρ A I hI.choose) ∧
      ¬ IsFFModule (centralQuotientRepresentation ρ A I hI.choose)) ∧
    (∃ I, ∃ hI : IsIrrPlus (fixedQuotient ρ ⊤) A I,
      Function.Injective (centralQuotientRepresentation (fixedQuotient ρ ⊤) A I hI.choose) ∧
      ¬ IsFFModule (centralQuotientRepresentation (fixedQuotient ρ ⊤) A I hI.choose)) := by
  let := hA.2
  let : IsSimpleGroup A := he.some.isSimpleGroup
  have hsqA : IsSQTK KnownSimple.IsKnownSimple A := (IsSQTK.equiv he.some).mpr hsq
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hmA : ClassicalGroup.IsPSL A 2 p :=
    ⟨F,inferInstance,inferInstance,hF,⟨he.some.trans eF⟩⟩
  obtain ⟨⟨I,hI,hfI⟩,⟨J,hJ,hfJ⟩⟩ := local_quotient_component_sections ρ hf A hA he
  exact ⟨⟨I,hI,hfI,odd_prime_irreducible_not_ff _ hsqA hfI hI.choose_spec.2 hp ho hmA hmod⟩,
    ⟨J,hJ,hfJ,odd_prime_irreducible_not_ff _ hsqA hfJ hJ.choose_spec.2 hp ho hmA hmod⟩⟩

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The remaining swapped configuration has its literal faithful core-quotient
module, two distinct original components, and faithful non-FF Irr⁺ sections. -/
theorem doubleNatural_four_pure_faithful_sections_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ (P : Sylow 2 G) (A : Sylow 3 X) (K : Subgroup G)
        (F : FundamentalSetup KnownSimple.IsKnownSimple T K),
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
          ((A : Subgroup X).map X.subtype) H K ∧
        conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
        X < componentOrbit K (T : Subgroup G) ∧
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
          (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∧
        elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (F.moduleSubgroup : Set G) ∧
        F.moduleSubgroup ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        letI := F.module_elementary
        let Q := XiQuotient (localJoin T K)
        let q := QuotientGroup.mk' (pCore 2 (localJoin T K))
        let K₁ := (K.subgroupOf (localJoin T K)).map q
        ∃ ρ : Representation (ZMod 2) Q (Additive F.moduleSubgroup),
          Function.Injective ρ ∧ Function.Injective (fixedQuotient ρ ⊤) ∧
          (∀ (x : localJoin T K) (v : F.moduleSubgroup),
            (ρ (q x) (Additive.ofMul v)).toMul =
              ⟨(x : G) * v * (x : G)⁻¹,
                (F.join_normalizes_module x.property v).mp v.property⟩) ∧
          cubicRatio ρ ≤ 2 ∧ cubicRatio (fixedQuotient ρ ⊤) ≤ 2 ∧
          ∃ t : localJoin T K, (t : G) ∈ T ∧ (t : G) ∉ normalizer (K : Set G) ∧
            let K₂ := K₁.map (MulAut.conj (q t)).toMonoidHom
            K₁ ≠ K₂ ∧ (K₁ ⊔ K₂).Normal ∧
            K₁ ⊔ K₂ = ((localOrbit T K).subgroupOf (localJoin T K)).map q ∧
            ∀ C ∈ ({K₁,K₂} : Set (Subgroup Q)),
              IsComponent Q C ∧ Nonempty (C ≃* XiQuotient K) ∧
              (∃ I, ∃ hI : IsIrrPlus ρ C I,
                Function.Injective (centralQuotientRepresentation ρ C I hI.choose) ∧
                ¬ IsFFModule (centralQuotientRepresentation ρ C I hI.choose)) ∧
              (∃ I, ∃ hI : IsIrrPlus (fixedQuotient ρ ⊤) C I,
                Function.Injective
                  (centralQuotientRepresentation (fixedQuotient ρ ⊤) C I hI.choose) ∧
                ¬ IsFFModule
                  (centralQuotientRepresentation (fixedQuotient ρ ⊤) C I hI.choose)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,A,K,F,hs,he,hstrict,hodd,hJF,hFQ,hc,_⟩ :=
    D.doubleNatural_four_pure_cubic_module_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  obtain ⟨_,hmodel⟩ := SwappedSylow.nonnormal_model_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hs.toSwappedInput
  let : IsSimpleGroup (XiQuotient K) :=
    SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodel
  have hsqK : IsSQTK KnownSimple.IsKnownSimple (XiQuotient K) :=
    (IsSQTK.equiv (SwappedFactorsProof.componentImageEquiv hs.toSwappedInput hs.component
      (le_componentOrbit K (T : Subgroup G)))).mpr
        ((SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).subgroup _)
  obtain ⟨p,hp',ho,hm,h8,h24⟩ := hodd
  let := F.module_elementary
  obtain ⟨ρ,hρ,hρq,hact,hbound⟩ := PureFourXi.local_module_faithful_action F hs.not_invariant
  have hρc : cubicRatio ρ ≤ 2 := hbound hc
  obtain ⟨t,ht,htn,hK₁,hK₂,hneK,eK₁,eK₂,hnK,hpair⟩ :=
    PureFourXi.local_quotient_component_pair F hs.not_invariant
  refine ⟨P,A,K,F,hs,he,hstrict,⟨p,hp',ho,hm,h8,h24⟩,hJF,hFQ,ρ,hρ,hρq,hact,hρc,
    cubicRatio_quotient_le_nat ρ (fixedSubrepresentation ρ ⊤) 2 hρc,
    t,ht,htn,hneK,hnK,hpair,?_⟩
  intro C hC
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact ⟨hK₁,eK₁,PureFourXi.local_quotient_component_nonFF_sections
      ρ hρ _ hK₁ eK₁ hsqK hp' ho hm h24⟩
  · have heq := Set.mem_singleton_iff.mp hC
    subst C
    exact ⟨hK₂,eK₂,PureFourXi.local_quotient_component_nonFF_sections
      ρ hρ _ hK₂ eK₂ hsqK hp' ho hm h24⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
