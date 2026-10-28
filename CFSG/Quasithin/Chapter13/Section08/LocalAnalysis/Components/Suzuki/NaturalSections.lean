module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Natural
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.MovedSpace
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.OrbitSections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SeedComparison
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.PairQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Source carrier and central-section targets in the Suzuki cases

The source carrier is Additive (U_H/V₁), and the actor is H/O₂(H).
Conjugation descends to this actor; the earlier centralizer equality gives
faithfulness. The literal seed Ṽ₃ has spanning H*-orbit. Its earlier
irreducibility and dimension two imply Ṽ₃=[Ṽ₃,L₁*].

We retain K₀=⟨K^T⟩ and W=[Ũ_H,K₀*], in both orbit cases. Quasisimplicity
of K* proves [W,K₀*]=W, and faithfulness proves W is nonzero. The two
output predicates use W/C_W(K₀*) itself and surjective maps to the
concrete actors. The invariant single-component branch now constructs
this output from the full B.4/B.5 inputs: its chosen Irr⁺ section is
proved to equal all of W before recognition. The source must still
supply that invariant section and the F.9.18 bounded actor and trivial
two-core. The complete single and swapped F.9.18 case assembly remains
unfinished; no natural-section existence is asserted without those inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.16,
printed pp.952–953; F.9.18(4–7), pp.325–326; B.4.2/B.4.5, pp.86–87;
B.5.1/B.5.6, pp.99 and 105. No direct-sum decomposition of W is asserted.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The constructed source representation, on the literal quotient carrier. -/
noncomputable def sourceAction
    (hn : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁) :=
  (exists_sourceAction H V₃ V₁ hn hQ).choose

/-- Each representative acts by its ambient conjugation. -/
theorem sourceAction_conjugation
    (hn : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    IsSourceAction H V₃ V₁ (sourceAction H V₃ V₁ hn hQ) :=
  (exists_sourceAction H V₃ V₁ hn hQ).choose_spec

/-- The source identity Q_H=C_H(Ũ_H) makes the constructed action faithful. -/
theorem sourceAction_faithful
    (hn : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hker : ∀ h : H, (∀ u : Source.UH H V₃, ⁅(h : G), (u : G)⁆ ∈ V₁) →
      h ∈ pCore 2 H) :
    Function.Injective (sourceAction H V₃ V₁ hn hQ) :=
  sourceAction_injective H V₃ V₁ _ (sourceAction_conjugation H V₃ V₁ hn hQ) hker

variable (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))

/-- The literal image K₀* of the complete T-conjugate span. -/
abbrev orbitActor (K T : Subgroup G) : Subgroup (Source.Hstar H) :=
  Source.starImage H (conjugateSpanBy K T)

/-- The entire commutator subspace, not a selected irreducible constituent. -/
noncomputable def movedSpace (K T : Subgroup G) : Submodule (ZMod 2) (SourceSpace H V₃ V₁) :=
  subspaceCommutator ρ ⊤ (orbitActor H K T)

/-- K₀* stabilizes its full commutator subspace. -/
theorem movedSpace_stable (K T : Subgroup G) :
    orbitActor H K T ≤ subspaceStabilizer ρ (movedSpace H V₃ V₁ ρ K T) :=
  subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by simp)) (orbitActor H K T).le_normalizer

/-- Every normalizer of K₀* also stabilizes W; this includes its centralizer. -/
theorem movedSpace_stable_of_normalizes (K T : Subgroup G) (L : Subgroup (Source.Hstar H))
    (hn : L ≤ normalizer (orbitActor H K T : Set (Source.Hstar H))) :
    L ≤ subspaceStabilizer ρ (movedSpace H V₃ V₁ ρ K T) :=
  subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp)) hn

/-- Quasisimplicity of K* supplies commutator generation for both orbit cases. -/
theorem movedSpace_generated (K T : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H)
    [IsQuasisimple (Source.starImage H K)] :
    subspaceCommutator ρ (movedSpace H V₃ V₁ ρ K T) (orbitActor H K T) =
      movedSpace H V₃ V₁ ρ K T := by
  let := componentOrbitStar_perfect H K T hKH hTH
  exact perfect_movedSpace_generated ρ _

/-- The faithful source representation has nonzero full component commutator. -/
theorem movedSpace_ne_bot (K T : Subgroup G)
    [IsQuasisimple (Source.starImage H K)] (hfaith : Function.Injective ρ) :
    movedSpace H V₃ V₁ ρ K T ≠ ⊥ := by
  intro he
  apply componentOrbitStar_not_fixed H K T ρ hfaith
  intro v _ k
  have hm : ρ k v - v ∈ movedSpace H V₃ V₁ ρ K T :=
    Submodule.subset_span ⟨k, k.property, v, Submodule.mem_top, rfl⟩
  rw [he, Submodule.mem_bot] at hm
  exact sub_eq_zero.mp hm

/-- The earlier irreducible binary plane gives the source seed identity,
without assuming the desired commutator equality. -/
theorem sourceSeed_generated
    (hρ : IsSourceAction H V₃ V₁ ρ) (L : Subgroup G)
    (hn : L ≤ normalizer (V₃ : Set G))
    (hi : IsAtom (invariantSubspace ρ (Source.starImage H L)
      (sourceSeedSpace H V₃ V₁) (sourceSeed_stable H V₃ V₁ ρ hρ L hn)))
    (hdim : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2) :
    subspaceCommutator ρ (sourceSeedSpace H V₃ V₁) (Source.starImage H L) =
      sourceSeedSpace H V₃ V₁ :=
  irreducible_seed_generated ρ _ _ (sourceSeed_stable H V₃ V₁ ρ hρ L hn) hi (by omega)

/-- Relative normality from the Borel argument propagates the seed identity
to the whole source module through its actual spanning orbit. -/
theorem source_generated_of_seed_plane
    (hρ : IsSourceAction H V₃ V₁ ρ) (L : Subgroup G)
    (hn : L ≤ normalizer (V₃ : Set G))
    (hi : IsAtom (invariantSubspace ρ (Source.starImage H L)
      (sourceSeedSpace H V₃ V₁) (sourceSeed_stable H V₃ V₁ ρ hρ L hn)))
    (hdim : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2)
    (hLn : (Source.starImage H L).Normal) :
    subspaceCommutator ρ ⊤ (Source.starImage H L) = ⊤ := by
  let := hLn
  apply commutator_top_of_orbit_seed ρ ⊤ (Source.starImage H L)
    (sourceSeedSpace H V₃ V₁) le_normalizer_of_normal
  · exact sourceSeed_generated H V₃ V₁ ρ hρ L hn hi hdim
  · simpa using sourceSeed_orbit_span H V₃ V₁ ρ hρ

/-- The required single-factor output, retaining the literal central quotient
of the entire W and a surjection onto the actual Suzuki matrix group. -/
def HasNaturalCentralSection (K T : Subgroup G) (m : ℕ) : Prop :=
  ∃ φ : orbitActor H K T →* SuzukiMatrixGroup m, Function.Surjective φ ∧
    ∃ e : centralQuotient ρ (orbitActor H K T) (movedSpace H V₃ V₁ ρ K T) ≃ₗ[ZMod 2]
      (Fin 4 → BinaryGaloisField (2 * m + 1)),
      ∀ k v, e (centralQuotientRepresentation ρ (orbitActor H K T)
        (movedSpace H V₃ V₁ ρ K T) (movedSpace_stable H V₃ V₁ ρ K T) k v) =
          natural m (φ k) (e v)

/-- The required swapped output has two independent concrete actors.
A diagonal action on two copies does not satisfy its surjectivity clause. -/
def HasPairedNaturalCentralSection (K T : Subgroup G) (m : ℕ) : Prop :=
  ∃ φ : orbitActor H K T →* (SuzukiMatrixGroup m × SuzukiMatrixGroup m),
    Function.Surjective φ ∧
    ∃ e : centralQuotient ρ (orbitActor H K T) (movedSpace H V₃ V₁ ρ K T) ≃ₗ[ZMod 2]
      ((Fin 4 → BinaryGaloisField (2 * m + 1)) × (Fin 4 → BinaryGaloisField (2 * m + 1))),
      ∀ k v, e (centralQuotientRepresentation ρ (orbitActor H K T)
        (movedSpace H V₃ V₁ ρ K T) (movedSpace_stable H V₃ V₁ ρ K T) k v) =
          naturalPair m (φ k) (e v)

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections

end

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]
  (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))

/-- The actual K₀*T* actor used in the F.9.18 and B.5 argument. -/
abbrev orbitExtension (H K T : Subgroup G) : Subgroup (Source.Hstar H) :=
  orbitActor H K T ⊔ Source.starImage H T

/-- The invariant branch of the single Suzuki orbit, including saturation
onto the entire W=[Ũ_H,K₀*]. The Irr⁺ witness, its invariance and the
bounded quadratic actor are precise remaining source inputs; no natural
module equivalence or identification of I with W is assumed. -/
theorem naturalCentralSection_of_invariant_irrPlus
    (K T : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    [IsQuasisimple (Source.starImage H K)]
    (hsingle : conjugateSpanBy K T = K) (hT : IsPGroup 2 T)
    {m : ℕ} (hm : 0 < m) (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m)
    {κ : GroupClass.{u}} (hSQ : IsSQTK κ H)
    (h₂ : pCore 2 (orbitExtension H K T) = ⊥)
    (hB5 : CompleteClassificationInput.{u,u} κ)
    (hB42 : Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.FullB42.{u,u} κ)
    (hB45 : RatioRecognition.SmallRatioSource.FullB45.{u,u} κ)
    (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hI : IsIrrPlus ρ (orbitActor H K T) I)
    (hs : orbitExtension H K T ≤ subspaceStabilizer ρ I)
    (A : Subgroup (orbitExtension H K T)) (hA : IsElementaryTwo A)
    (hquad : IsQuadratic (ρ.comp (orbitExtension H K T).subtype) A)
    (hbound : fixedCodim (ρ.comp (orbitExtension H K T).subtype) A ≤ 2 * rank A) :
    HasNaturalCentralSection H V₃ V₁ ρ K T m := by
  have hSQstar : IsSQTK κ (Source.Hstar H) := by
    refine ⟨?_, hSQ.isKGroup.quotient (pCore 2 H)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hSQ.stronglyQuasithin p hp ho)
  let D := orbitExtension H K T
  let K₀ := orbitActor H K T
  have hKD : K₀ ≤ D := le_sup_left
  have hTN : Source.starImage H T ≤ normalizer (K₀ : Set (Source.Hstar H)) := by
    change Source.starImage H T ≤ normalizer (Source.starImage H (conjugateSpanBy K T) : Set _)
    rw [starImage_conjugateSpan H K T hKH hTH]
    exact le_normalizer_conjugateSpanBy _ _
  let : (K₀.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hKD).mpr
    (sup_le K₀.le_normalizer hTN)
  have hTstar : IsPGroup 2 (Source.starImage H T) := by
    unfold Source.starImage
    exact hT.comap_subtype.map _
  have hquot : IsPGroup 2 (D ⧸ K₀.subgroupOf D) := by
    apply isPGroup_quotient_of_sup_eq_top _ ((Source.starImage H T).subgroupOf D)
      hTstar.comap_subtype
    rw [← subgroupOf_sup hKD (show Source.starImage H T ≤ D from le_sup_right)]
    exact subgroupOf_self D
  let e₀ : K₀ ≃* Source.starImage H K :=
    MulEquiv.subgroupCongr (congrArg (Source.starImage H) hsingle)
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv e₀.symm
  let e : K₀ ≃* SuzukiMatrixGroup m := e₀.trans (starModelEquiv H K hKH hK m eK)
  let f : K₀.subgroupOf D ≃* K₀ := subgroupOfEquivOfLe hKD
  let : IsQuasisimple (K₀.subgroupOf D) := IsQuasisimple.of_mulEquiv f.symm
  have hI' := (IsIrrPlus.subgroupOf_iff ρ K₀ D hKD I).mpr hI
  have hs' : (⊤ : Subgroup D) ≤ subspaceStabilizer (ρ.comp D.subtype) I := by
    intro d _
    exact hs d.property
  have hsat := OrbitSections.invariant_irrPlus_eq_moved (ρ.comp D.subtype)
    hB5 (hSQstar.subgroup D) h₂ (K₀.subgroupOf D) hquot hm (f.trans e) I hI' hs' A hA hbound
  have hmove : subspaceCommutator (ρ.comp D.subtype) ⊤ (K₀.subgroupOf D) =
      movedSpace H V₃ V₁ ρ K T := by
    unfold movedSpace subspaceCommutator
    congr 1
    ext v
    constructor
    · rintro ⟨k, hk, w, hw, rfl⟩
      exact ⟨k, hk, w, hw, rfl⟩
    · rintro ⟨k, hk, w, hw, rfl⟩
      exact ⟨⟨k, hKD hk⟩, hk, w, hw, rfl⟩
  rw [hmove] at hsat
  subst I
  have hC := OrbitSections.centralizer_eq_bot_of_centerless_two_quotient (K₀.subgroupOf D)
    (SectionRecognition.center_eq_bot_of_equiv_suzuki (f.trans e)) hquot h₂
  obtain ⟨a⟩ := SectionRecognition.invariant_natural_section_in_subgroup ρ K₀ D hKD
    hm e (hSQstar.subgroup D) hquot _ hI hs A hA hquad hbound
    (by rw [hC]; exact disjoint_bot_right) hB42 hB45
  exact ⟨a.groupEquiv.toMonoidHom, a.groupEquiv.surjective, a.linearEquiv, a.intertwines⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections

end
