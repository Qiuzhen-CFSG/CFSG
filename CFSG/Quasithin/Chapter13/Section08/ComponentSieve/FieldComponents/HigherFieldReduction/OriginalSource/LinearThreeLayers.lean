module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.LinearTwoComplete

/-!
# Native odd PSL₃ layers on the original source action

The original residual and cubic structure supply the common-centralizer bound
and faithful action; the native cubic-pair argument excludes strong FF modules.
A realized FF constituent whose actual orbit is its two cubic conjugates then
has one or two natural tensor layers. The original quadratic actor supplies the
ratio bound, Sylow conjugacy aligns the original Borel, and Borel centralization
contradicts both alternatives. The two layers retain independent natural/dual
orientations and the component-central complement is not removed.

The actual original FF multiplicity action also constructs an Irr⁺ constituent
in the original module, with its literal inclusion, natural/dual coordinates,
vanishing central kernel and disjoint cubic translate. It does not yet prove
that this pair is invariant under the whole source actor. That orbit argument,
the exceptional outer fields, binary premises and final 13.8.19–21 assembly
remain with qt-d-138-fields-source; qt-d-1381-source retains the preceding
source context. These are source applications, not the full odd-PSL₃ exclusion.
Source: Aschbacher–Smith, 13.8.20(a), pp.954–955, with B.4.2 and F.9.18.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open Representation.BinaryOffender.Homogeneous
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases (B4Hypotheses)
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
private theorem inverse_intertwines
    {D E M N : Type*} [Group D] [Group E]
    [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) D M) (σ : Representation (ZMod 2) E N)
    (a : D ≃* E) (b : M ≃ₗ[ZMod 2] N)
    (hb : ∀ g v, b (ρ g v) = σ (a g) (b v)) (g : E) (v : N) :
    b.symm (σ g v) = ρ (a.symm g) (b.symm v) := by
  apply b.injective
  calc
    b (b.symm (σ g v)) = σ g v := b.apply_symm_apply _
    _ = σ (a (a.symm g)) (b (b.symm v)) := by
      rw [a.apply_symm_apply,b.apply_symm_apply]
    _ = b (ρ (a.symm g) (b.symm v)) := (hb _ _).symm

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Native recognition rules out strong FF actions on the original external
odd PSL₃ module, with no universal B.4.2 or F.9.18 premise. -/
theorem source_external_linearThree_no_strong
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2^n)
    (e : Source.starImage H K ≃* PSL(3,F)) : ¬ IsStrongFFModule act.representation := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let : Xs.Normal := hx.2.2.1
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  have hF9 := c.f9 H c.component.local_overgroup
  have hf := f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  obtain ⟨s,_,hcomm,hm,hg,_,_⟩ := source_external_cubic_action act X ha hx hseed
  exact RankTwo.Native.no_strong act.representation Ks hsq hf Xs hx.1
    (source_external_common_centralizer c X hx) s
    (fun k g => hcomm ⟨g,rfl⟩ k k.property) hm hg hn ho hF e

/-- A realized FF constituent with its actual two-conjugate orbit is
impossible in the original odd PSL₃ branch. The native first/second-layer
recognition, original quadratic actor, and Borel obstruction are discharged.
Construction of the orbit itself remains with this field-source owner. -/
theorem source_external_linearThree_realization_false
    [(Source.starImage H K).Normal]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H)
    (hcentral : LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G))
    (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    {E N : Type u} [Group E] [Finite E] [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N)
    (hσ : B4Hypotheses KnownSimple.IsKnownSimple σ) (hff : IsFFModule σ)
    (r : LinearTwo.FiveReconstruction.ConstituentRealization act.representation
      (Source.starImage H K) σ (generalizedFitting E))
    (horbit : Representation.BinaryOffender.Homogeneous.orbitSpan act.representation ⊤ r.space =
      r.space ⊔ r.space.map (act.representation (s cubic)))
    {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : ClassicalGroup.IsPSL (Source.starImage H K) 3 (2^n)) : False := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Xs.Normal := hx.2.2.1
  let : (K.subgroupOf H).Normal := c.component.normal
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let B : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := hcard }
  let S := LocalBorel.sourceSylow H K (T : Subgroup G) hT
  let B₀ := LocalBorel.borelStar H K (T : Subgroup G) hT
  have hB : B₀.subgroupOf Ks = normalizer (S : Set Ks) :=
    comap_map_eq_self_of_injective Ks.subtype_injective _
  obtain ⟨e',hBe⟩ := RankTwo.exists_borel_marking (by omega : 0 < n) hcard e S
  have hmarkB : (B₀.subgroupOf Ks).map e'.toMonoidHom = Matrix.PSL3.LinearThree.borel F := by
    rw [hB]; exact hBe
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  obtain ⟨_,_,_,_,hg,_,_⟩ := source_external_cubic_action act X ha hx hseed
  have hgen : subspaceCommutator act.representation ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤ := by
    rw [hmark]; exact hg
  obtain ⟨a,ha'⟩ := r.exists_multiplicityCoordinates act.representation Ks s hs horbit hgen
  let W := SourceOrbit.selectedOrbitUpper act.representation r.space
  have hWa : W.toSubmodule = Representation.BinaryOffender.Homogeneous.orbitSpan act.representation ⊤ r.space := rfl
  have hb (k : generalizedFitting E) (v : N) :
      a.symm (σ k v) = sectionMultiplicityAction act.representation Ks.subtype s hs
        (LinearTwo.centralBottom act.representation Ks W) W (r.component.symm k) (a.symm v) := by
    exact inverse_intertwines
      (sectionMultiplicityAction act.representation Ks.subtype s hs
        (LinearTwo.centralBottom act.representation Ks W) W)
      (σ.comp (generalizedFitting E).subtype) r.component a ha' k v
  obtain ⟨A,hA,_⟩ := source_quotient_faithful_quadratic_actor c act
  have hlayers := RankTwo.Native.oneOrTwo_of_ff_orbit act.representation Ks Xs hsq hx.1
    (source_external_common_centralizer c X hx) s hs hmark hg hn ho hcard e' W
    σ hσ hff r.component.symm a.symm hb
    (by rw [hWa]; exact orbitSpan_ne_bot _ r.irrPlus)
    (by rw [hWa]; exact orbitSpan_full_commutator _ (by rw [normalizer_eq_top]) r.irrPlus)
    A hA.1 hA.2.2
  exact source_external_natural_false c act hKH B₀ (map_subtype_le _)
    hcentral s hs (Or.inr ⟨B,hn,ho,e',hmarkB,
      RankTwo.oneOrTwo_tensor_layers act.representation Ks.subtype s hs e' ho hcard hlayers hgen⟩)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original FF multiplicity action supplies an actual natural or dual
Irr⁺ subspace in the original module. The central kernel vanishes by the
natural cohomology calculation, and its cubic translate is disjoint. No
invariance under the entire source actor is asserted. -/
theorem source_external_linearThree_constituent
    [(Source.starImage H K).Normal]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2^n)
    (e : Source.starImage H K ≃* PSL(3,F)) :
    ∃ s : S₃ →* Source.Hstar H,
      Function.Injective s ∧
      (∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g)) ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X ∧
      ∃ (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
        (hI : IsIrrPlus act.representation (Source.starImage H K) I),
        Disjoint I (fixedSpace act.representation (Source.starImage H K)) ∧
        Disjoint I (I.map (act.representation (s cubic))) ∧
        IsProjectiveNaturalOrDual ho hF
          ((invariantSubspace act.representation (Source.starImage H K) I hI.choose).toRepresentation.comp
            e.symm.toMonoidHom) ∧ Module.finrank (ZMod 2) I = 3*n := by
  let Ks := Source.starImage H K
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  obtain ⟨s,hsi,hmark,hfree,A,_,hs,μ,hμ,hf,hoff,hfit,hS⟩ :=
    source_external_ff_multiplicity c act X ha hx hseed
  subst μ
  let E := Ks ⊔ A
  let K₀ := Ks.subgroupOf E
  let j := (multiplicitySpace (act.representation.comp s)).subtype
  let μ := multiplicity (act.representation.comp s) (act.representation.comp E.subtype)
    (ambient_commute act.representation E.subtype s hs)
  let b : K₀ ≃* Ks := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv b.symm
  have hfit₀ : generalizedFitting E = K₀ := hfit
  let : K₀.Normal := hfit₀ ▸ generalizedFitting_normal
  have hKm : K₀.map E.subtype = Ks := map_subgroupOf_eq_of_le le_sup_left
  have hz : center K₀ = ⊥ := RankTwo.CubicFF.component_center K₀ ho hF (b.trans e)
  obtain ⟨B,I,_,hI,hJI,hB4,hFF,hfit',_⟩ :=
    faithful_irreducible_ff_section μ hf K₀ hfit₀ hz hS ⟨A.subgroupOf E,hoff⟩
  let r := LinearTwo.centralImageRealization μ K₀ (K₀ ⊔ B) hz le_sup_left I hI hJI hfit'
  let : Finite (centralQuotient μ K₀ I) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective ((fixedSpace μ K₀).comap I.subtype))
  obtain ⟨r',hr'⟩ := r.exists_mapEmbedding μ act.representation E.subtype E.subtype_injective
    j (multiplicitySpace _).subtype_injective (fun _ _ => rfl) Ks hKm
  let τ := centralSectionRepresentation μ K₀ (K₀ ⊔ B) I hJI le_normalizer_of_normal
  let σ := imageRepresentation τ
  have hqnat := (RankTwo.Native.naturalOrDual_and_ratio σ hB4 hFF hn ho hF
    (centralQuotientRepresentation act.representation Ks r'.space r'.irrPlus.choose) e
    r'.component.symm r'.linearEquiv.symm
      (inverse_intertwines
        (centralQuotientRepresentation act.representation Ks r'.space r'.irrPlus.choose)
        (σ.comp (generalizedFitting (actionImage τ)).subtype)
        r'.component r'.linearEquiv r'.component_intertwines)).1
  have hnat := RankTwo.CubicFF.CentralSplitting.naturalOrDual hn ho hF
    act.representation Ks e r'.space r'.irrPlus hqnat
  have hd := RankTwo.CubicFF.CentralSplitting.disjoint_fixedSpace hn ho hF
    act.representation Ks e r'.space r'.irrPlus hqnat
  have hdim : Module.finrank (ZMod 2) r'.space = 3*n :=
    RankTwo.CubicFF.naturalOrDual_finrank ho hF _ hnat
  have hpair : Disjoint r'.space (r'.space.map (act.representation (s cubic))) := by
    have hh := RankTwo.CubicFF.PairSaturation.cubic_pair_disjoint act.representation Ks s
      hfree r'.space r'.irrPlus hd
      (by rw [hdim]; exact (by decide : Odd 3).mul ho)
    exact hh
  exact ⟨s,hsi,(fun k g => hs ⟨k,mem_sup_left k.property⟩ g),hmark,
    r'.space,r'.irrPlus,hd,hpair,hnat,hdim⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open Representation.BinaryOffender.Homogeneous
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)] [(Source.starImage H K).Normal]

/-- Natural coordinates on the actual constituent suffice for the original
contradiction once its two-conjugate orbit is invariant. No FF realization
or universal classification implication is required at this boundary. -/
theorem source_external_linearThree_natural_pair_false
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H)
    (hcentral : LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G))
    (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (B : BinaryField) (hn : 1 < B.degree) (ho : Odd B.degree)
    (e : Source.starImage H K ≃* PSL(3,B.Carrier))
    (hB : ((LocalBorel.borelStar H K (T : Subgroup G) hT).subgroupOf (Source.starImage H K)).map
      e.toMonoidHom = Matrix.PSL3.LinearThree.borel B.Carrier)
    (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hI : IsIrrPlus act.representation (Source.starImage H K) I)
    (hd : Disjoint I (fixedSpace act.representation (Source.starImage H K)))
    (hp : Disjoint I (I.map (act.representation (s cubic))))
    (hnat : IsProjectiveNaturalOrDual ho B.card_eq
      ((invariantSubspace act.representation (Source.starImage H K) I hI.choose).toRepresentation.comp
        e.symm.toMonoidHom))
    (horbit : Representation.BinaryOffender.Homogeneous.orbitSpan act.representation ⊤ I = I ⊔ I.map (act.representation (s cubic))) : False := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Xs.Normal := hx.2.2.1
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  obtain ⟨_,_,_,_,hg,_,_⟩ := source_external_cubic_action act X ha hx hseed
  have hgen : subspaceCommutator act.representation ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤ := by
    rw [hmark]; exact hg
  let W := SourceOrbit.selectedOrbitUpper act.representation I
  have hWa : W.toSubmodule = Representation.BinaryOffender.Homogeneous.orbitSpan act.representation ⊤ I := rfl
  obtain ⟨a,ha'⟩ := RankTwo.CubicFF.PairSaturation.multiplicity_coordinates
    act.representation Ks s hs (ambient_fixedFree_of_commutator _ _ hgen)
    I hI hd hp W (hWa.trans horbit)
  have hfirst : IsProjectiveNaturalOrDual ho B.card_eq
      (RankTwo.projectiveMultiplicity act.representation Ks.subtype s hs e ⊥ W) := by
    rcases hnat with ⟨f,hf⟩ | ⟨f,hf⟩
    · exact Or.inl ⟨a.trans f, fun g v => by
        change f (a (sectionMultiplicityAction act.representation Ks.subtype s hs ⊥ W (e.symm g) v)) = _
        rw [ha']; exact hf g (a v)⟩
    · exact Or.inr ⟨a.trans f, fun g v => by
        change f (a (sectionMultiplicityAction act.representation Ks.subtype s hs ⊥ W (e.symm g) v)) = _
        rw [ha']; exact hf g (a v)⟩
  obtain ⟨A,hA,_⟩ := source_quotient_faithful_quadratic_actor c act
  have hlayers := RankTwo.Native.oneOrTwo_of_first_layer act.representation Ks Xs hsq hx.1
    (source_external_common_centralizer c X hx) s hs hmark hg hn ho B.card_eq e W
    ⊥ bot_le bot_le hfirst
    (by rw [hWa]; exact orbitSpan_ne_bot _ hI)
    (by rw [hWa]; exact orbitSpan_full_commutator _ (by rw [normalizer_eq_top]) hI)
    A hA.1 hA.2.2
  exact source_external_natural_false c act hKH _ (map_subtype_le _) hcentral s hs
    (Or.inr ⟨B,hn,ho,e,hB,
      RankTwo.oneOrTwo_tensor_layers act.representation Ks.subtype s hs e ho B.card_eq hlayers hgen⟩)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open Representation.BinaryOffender.Homogeneous
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)] [(Source.starImage H K).Normal]

/-- Construct the literal natural cubic pair and apply the original Borel
obstruction. An external odd PSL₃ branch forces this pair to escape whole-actor
invariance. Closing that invariant-orbit step remains part of the field task. -/
theorem source_external_linearThree_candidate
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H)
    (hcentral : LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G))
    {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : ClassicalGroup.IsPSL (Source.starImage H K) 3 (2^n)) :
    ∃ (B : BinaryField) (hd : B.degree = n) (e : Source.starImage H K ≃* PSL(3,B.Carrier)),
      ((LocalBorel.borelStar H K (T : Subgroup G) hT).subgroupOf (Source.starImage H K)).map
        e.toMonoidHom = Matrix.PSL3.LinearThree.borel B.Carrier ∧
      ∃ s : S₃ →* Source.Hstar H,
        Function.Injective s ∧
        (∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g)) ∧
        (alternatingGroup (Fin 3)).map s = Source.starImage H X ∧
        ∃ (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
          (hI : IsIrrPlus act.representation (Source.starImage H K) I),
          Disjoint I (fixedSpace act.representation (Source.starImage H K)) ∧
          Disjoint I (I.map (act.representation (s cubic))) ∧
          IsProjectiveNaturalOrDual (hd.symm ▸ ho) B.card_eq
            ((invariantSubspace act.representation (Source.starImage H K) I hI.choose).toRepresentation.comp
              e.symm.toMonoidHom) ∧ Module.finrank (ZMod 2) I = 3*n ∧
          ¬ (⊤ : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer act.representation
            (I ⊔ I.map (act.representation (s cubic))) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  obtain ⟨F,hF,hfin,hcard,⟨e₀⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let B : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := hcard }
  let S := LocalBorel.sourceSylow H K (T : Subgroup G) hT
  obtain ⟨e,hBe⟩ := RankTwo.exists_borel_marking (by omega : 0 < n) hcard e₀ S
  have hB : ((LocalBorel.borelStar H K (T : Subgroup G) hT).subgroupOf (Source.starImage H K)).map
      e.toMonoidHom = Matrix.PSL3.LinearThree.borel F := by
    rw [show (LocalBorel.borelStar H K (T : Subgroup G) hT).subgroupOf (Source.starImage H K) =
      normalizer (S : Set (Source.starImage H K)) from
      comap_map_eq_self_of_injective (Source.starImage H K).subtype_injective _]
    exact hBe
  obtain ⟨s,hsi,hs,hmark,I,hI,hd,hp,hnat,hdim⟩ :=
    source_external_linearThree_constituent c act ha hx hseed hn ho hcard e
  refine ⟨B,rfl,e,hB,s,hsi,hs,hmark,I,hI,hd,hp,hnat,hdim,?_⟩
  intro hstable
  have horbit : Representation.BinaryOffender.Homogeneous.orbitSpan act.representation ⊤ I = I ⊔ I.map (act.representation (s cubic)) := by
    apply le_antisymm (orbitSpan_le _ le_sup_left hstable)
    exact sup_le (le_orbitSpan _ _ _)
      (le_iSup (fun g : (⊤ : Subgroup (Source.Hstar H)) => I.map (act.representation g))
        ⟨s cubic,mem_top _⟩)
  exact source_external_linearThree_natural_pair_false c act ha hx hseed hKH hT hcentral
    s hs hmark B hn ho e hB I hI hd hp hnat horbit
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
