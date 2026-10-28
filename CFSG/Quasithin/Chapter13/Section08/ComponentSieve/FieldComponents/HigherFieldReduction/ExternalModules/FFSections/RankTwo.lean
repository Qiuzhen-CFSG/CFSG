module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryProjection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.FieldGraph
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.FullList
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.ActionSieve
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NaturalSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Natural

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.QuotientLayers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.Invariance
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.SectionModel
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections
/-!
# The external unitary exclusion and odd-degree L₃ tensor layers

The even-degree special unitary projection is an actual isomorphism.
The full B.4.2 split retains natural SL₃ action coordinates and every other
model. Field transport, inverse transpose, and the field trace give concrete
binary natural/dual comparisons. For each actual invariant section we also
construct its tensor coordinates under the specified component equivalence.

The complete B.4.2 sieve now excludes even-degree unitary constituents and
recognizes odd-degree SL₃ constituents in the original marking. Compatible
faithful-image and multiplicity maps construct a natural tensor layer on the
literal central quotient of the orbit. The full F.9.18(6) section inequality
then gives one or two layers: cubic pairing excludes both strong-FF cases,
and recognizes the quotient's full moved module with zero bottom. Its lifted
upper space is exactly the original moved module.

`source_natural_sections` proves this conditional family deduction on the
literal source action, deriving the common-centralizer bound from H = KL₁T
and the complete earlier Fitting alternative. The actual T-invariant Irr⁺ FF
constituent, its two-conjugate orbit and compatible maps remain explicit
SourceOrbit inputs. The complete universal B.4.2 implication remains an input;
B.1.5 invariance is discharged using the proved B.7.2 theorem. Sylow conjugacy
aligns the original Borel once, and both natural or binary dual-natural layers
use that marking. `oneOrTwo_tensor_layers` constructs their actual section
maps. Final 13.8.20 assembly belongs to the parent FFSections task.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955, B.4.2,
printed p.86, and F.9.18(6), printed pp.325–326.
-/

@[expose] public noncomputable section

open Representation Representation.BinaryOffender Representation.HigherFieldBorelFixedSpaces
open InvertedCubicTensor
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The defining-field dual satisfies the consumer's binary-dual convention. -/
theorem fieldDual_isProjectiveNaturalOrDual
    {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n) :
    IsProjectiveNaturalOrDual hn hF (projectiveBinaryFieldDual hn hF) :=
  Or.inr ⟨traceDualEquiv 3, traceDualEquiv_projective_intertwines hn hF⟩

variable {G K V : Type*} [Group G] [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (f : K →* G) (s : S₃ →* G)
  (hs : ∀ k g, Commute (f k) (s g)) (e : K ≃* PSL(3,F))
  (C D : Subrepresentation ρ)

/-- The literal inverter-fixed multiplicity action in the fixed projective marking. -/
def projectiveMultiplicity : Representation (ZMod 2) PSL(3,F) (SectionMultiplicity ρ s C D) :=
  (sectionMultiplicityAction ρ f s hs C D).comp e.symm.toMonoidHom

/-- Tensor coordinates on the literal section, with no new choice of component marking. -/
def projectiveTensorLayer (hCD : C ≤ D)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    NaturalLayers.TensorLayer (ρ.comp f) (projectiveMultiplicity ρ f s hs e C D) e
      C.toSubmodule D.toSubmodule :=
  tensorLayer ρ f s hs C D (projectiveMultiplicity ρ f s hs e C D) e
    (LinearEquiv.refl _ _) hCD hgen (by
      intro k v
      change sectionMultiplicityAction ρ f s hs C D k v =
        sectionMultiplicityAction ρ f s hs C D (e.symm (e k)) v
      rw [e.symm_apply_apply])

/-- The output of the F.9.18 argument. Centrality is
on the original module, and both multiplicity factors use the same marking.
The actual tensor maps are constructed by `projectiveTensorLayer`. -/
def OneOrTwoNaturalSections {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n) : Prop :=
  ∃ C D : Subrepresentation ρ,
    C ≤ D ∧ C.toSubmodule ≤ Representation.invariants (ρ.comp f) ∧
    IsProjectiveNaturalOrDual hn hF (projectiveMultiplicity ρ f s hs e C D) ∧
    ((∀ k v, ρ (f k) v - v ∈ D.toSubmodule) ∨
      ∃ W : Subrepresentation ρ, D ≤ W ∧
        IsProjectiveNaturalOrDual hn hF (projectiveMultiplicity ρ f s hs e D W) ∧
        ∀ k v, ρ (f k) v - v ∈ W.toSubmodule)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

open Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

universe u v
variable {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
  {G K V : Type*} [Group G] [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (f : K →* G) (s : S₃ →* G)
  (hs : ∀ k g, Commute (f k) (s g)) (e : K ≃* PSL(3,F))
  (C D : Subrepresentation ρ)
  {E : Type u} [Group E] [Finite E]
  {U : Type v} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
  (σ : Representation (ZMod 2) E U)
  {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
  (h : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
  (a : generalizedFitting E ≃* K)
  (b : U ≃ₗ[ZMod 2] SectionMultiplicity ρ s C D)
  (hb : ∀ (g : generalizedFitting E) v,
    b (σ g v) = sectionMultiplicityAction ρ f s hs C D (a g) (b v))

include hn hB42 h hff a b hb

/-- The actual faithful constituent, with compatible component and section
maps, recognizes the literal multiplicity space under the supplied marking. -/
theorem multiplicity_naturalOrDual_of_ff :
    IsProjectiveNaturalOrDual ho hF (projectiveMultiplicity ρ f s hs e C D) :=
  naturalOrDual_of_ff_coordinates σ hB42 h hff hn ho hF
    (sectionMultiplicityAction ρ f s hs C D) e a b hb

/-- Construct both naturality and the actual tensor coordinates on D/C.
The inputs contain no naturality, field identification, or tensor layer. -/
theorem natural_tensor_layer_of_ff (hCD : C ≤ D)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    IsProjectiveNaturalOrDual ho hF (projectiveMultiplicity ρ f s hs e C D) ∧
      Nonempty (NaturalLayers.TensorLayer (ρ.comp f)
        (projectiveMultiplicity ρ f s hs e C D) e C.toSubmodule D.toSubmodule) :=
  ⟨multiplicity_naturalOrDual_of_ff hn ho hF ρ f s hs e C D σ hB42 h hff a b hb,
    ⟨projectiveTensorLayer ρ f s hs e C D hCD hgen⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

open Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

universe u v
variable {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
  {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
  (s : S₃ →* G) (hs : ∀ (k : K) g, Commute (k : G) (s g))
  (e : K ≃* PSL(3,F)) (W : Subrepresentation ρ)
  {E : Type u} [Group E] [Finite E]
  {U : Type v} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
  (σ : Representation (ZMod 2) E U)
  {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
  (h : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
  (a : generalizedFitting E ≃* K)
  (b : U ≃ₗ[ZMod 2] SectionMultiplicity ρ s (LinearTwo.centralBottom ρ K W) W)
  (hb : ∀ (g : generalizedFitting E) v,
    b (σ g v) = sectionMultiplicityAction ρ K.subtype s hs
      (LinearTwo.centralBottom ρ K W) W (a g) (b v))

include hn hB42 h hff a b hb

/-- For the actual orbit, its intersection with C_V(K) is the central bottom.
The full B.4.2 input and compatible quotient maps supply its natural tensor layer. -/
theorem centralOrbit_natural_layer_of_ff
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    (LinearTwo.centralBottom ρ K W).toSubmodule ≤ Representation.invariants (ρ.comp K.subtype) ∧
      IsProjectiveNaturalOrDual ho hF
        (projectiveMultiplicity ρ K.subtype s hs e (LinearTwo.centralBottom ρ K W) W) ∧
      Nonempty (NaturalLayers.TensorLayer (ρ.comp K.subtype)
        (projectiveMultiplicity ρ K.subtype s hs e (LinearTwo.centralBottom ρ K W) W) e
        (LinearTwo.centralBottom ρ K W).toSubmodule W.toSubmodule) :=
  ⟨LinearTwo.centralBottom_central ρ K W,
    natural_tensor_layer_of_ff hn ho hF ρ K.subtype s hs e
      (LinearTwo.centralBottom ρ K W) W σ hB42 h hff a b hb
      (LinearTwo.centralBottom_le ρ K W) hgen⟩

/-- F.9.18(6a), once selected, yields the one-layer output on the literal
module. Its central quotient follows from moved-space equality. -/
theorem oneLayer_of_ff_moved
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ K) :
    OneOrTwoNaturalSections ρ K.subtype s hs e ho hF := by
  refine ⟨LinearTwo.centralBottom ρ K W, W, LinearTwo.centralBottom_le ρ K W,
    LinearTwo.centralBottom_central ρ K W, ?_, Or.inl ?_⟩
  · exact multiplicity_naturalOrDual_of_ff hn ho hF ρ K.subtype s hs e
      (LinearTwo.centralBottom ρ K W) W σ hB42 h hff a b hb
  · exact LinearTwo.central_quotient_of_moved_eq ρ K W hW

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
open LinearTwo.NoStrongMoved
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K X : Subgroup D)
    [K.Normal] [X.Normal] [IsQuasisimple K]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hInv : FullIrrInvariance.{u,v})
    (hS : IsSQTK 𝒦 D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (W : Subrepresentation ρ)
    {E : Type u} [Group E] [Finite E]
    {U : Type v} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (σ : Representation (ZMod 2) E U)
    (hσ : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (a : generalizedFitting E ≃* K)
    (b : U ≃ₗ[ZMod 2] SectionMultiplicity ρ s (LinearTwo.centralBottom ρ K W) W)
    (hb : ∀ (g : generalizedFitting E) v,
      b (σ g v) = sectionMultiplicityAction ρ K.subtype s hs
        (LinearTwo.centralBottom ρ K W) W (a g) (b v))

include hB42 hInv hS hx hc hs hmark hg hn ho hF e hσ hff a b hb in
/-- The full F.9.18 section argument gives one or two natural tensor layers.
The first layer comes from the actual faithful FF constituent and its compatible
multiplicity map; the second is proved by cubic FF recognition and quotient lifting. -/
theorem oneOrTwo_of_ff_orbit
    (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    OneOrTwoNaturalSections ρ K.subtype s hs e ho hF := by
  by_cases he : W.toSubmodule = subspaceCommutator ρ ⊤ K
  · exact oneLayer_of_ff_moved hn ho hF ρ K s hs e W σ hB42 hσ hff a b hb he
  obtain ⟨M, hWM, hM, hnat⟩ := QuotientLayers.second_layer ρ K X hB42 hInv hS hx hc
    s hs hmark hg hn ho hF e W hW hfull he A hA hbound
  exact ⟨LinearTwo.centralBottom ρ K W, W, LinearTwo.centralBottom_le ρ K W,
    LinearTwo.centralBottom_central ρ K W,
    multiplicity_naturalOrDual_of_ff hn ho hF ρ K.subtype s hs e
      (LinearTwo.centralBottom ρ K W) W σ hB42 hσ hff a b hb,
    Or.inr ⟨M, hWM, hnat, LinearTwo.central_quotient_of_moved_eq ρ K M hM⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

variable {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
  {K : Type*} [Group K] [Finite K] (e : K ≃* PSL(3,F)) (S : Sylow 2 K)

omit [Algebra (ZMod 2) F] in
include hn hF e in
/-- Align the original Sylow normalizer with the standard projective Borel.
The resulting single component marking may be used for both tensor layers. -/
theorem exists_borel_marking : ∃ e' : K ≃* PSL(3,F),
    (normalizer (S : Set K)).map e'.toMonoidHom = Matrix.PSL3.LinearThree.borel F := by
  obtain ⟨g, _, hg⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylow_normalizer_conjugate
    F hn hF (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨e.trans (MulAut.conj g).symm, ?_⟩
  change (normalizer (S : Set K)).map ((MulAut.conj g).symm.toMonoidHom.comp e.toMonoidHom) = _
  rw [← Subgroup.map_map, ← S.coe_coe, map_equiv_normalizer_eq]
  change (normalizer (S.mapSurjective (f := e.toMonoidHom) e.surjective : Set PSL(3,F))).map _ = _
  rw [← hg, Subgroup.map_map]
  simp

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {G K V : Type*} [Group G] [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (f : K →* G) (s : S₃ →* G)
    (hs : ∀ k g, Commute (f k) (s g)) (e : K ≃* PSL(3,F))
    {n : ℕ} (ho : Odd n) (hF : Nat.card F = 2^n)

/-- Construct the actual section maps for both independently oriented layers.
Central bottom and top quotient remain on the literal original module. -/
theorem oneOrTwo_tensor_layers
    (h : OneOrTwoNaturalSections ρ f s hs e ho hF)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    ∃ C D : Subrepresentation ρ,
      C.toSubmodule ≤ Representation.invariants (ρ.comp f) ∧
      IsProjectiveNaturalOrDual ho hF (projectiveMultiplicity ρ f s hs e C D) ∧
      Nonempty (NaturalLayers.TensorLayer (ρ.comp f)
        (projectiveMultiplicity ρ f s hs e C D) e C.toSubmodule D.toSubmodule) ∧
      ((∀ k v, ρ (f k) v - v ∈ D.toSubmodule) ∨
        ∃ W : Subrepresentation ρ,
          IsProjectiveNaturalOrDual ho hF (projectiveMultiplicity ρ f s hs e D W) ∧
          Nonempty (NaturalLayers.TensorLayer (ρ.comp f)
            (projectiveMultiplicity ρ f s hs e D W) e D.toSubmodule W.toSubmodule) ∧
          ∀ k v, ρ (f k) v - v ∈ W.toSubmodule) := by
  obtain ⟨C, D, hCD, hc, hn, htop⟩ := h
  refine ⟨C, D, hc, hn, ⟨projectiveTensorLayer ρ f s hs e C D hCD hgen⟩, ?_⟩
  rcases htop with hq | ⟨W, hDW, hn', hq⟩
  · exact Or.inl hq
  · exact Or.inr ⟨W, hn', ⟨projectiveTensorLayer ρ f s hs e D W hDW hgen⟩, hq⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
open LinearTwo.NoStrongMoved

private theorem orbit_eq_of_two_conjugates
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (W : Subrepresentation ρ)
    (I : Submodule (ZMod 2) U) (x : D)
    (he : W.toSubmodule = I ⊔ I.map (ρ x)) : W.toSubmodule = orbitSpan ρ ⊤ I := by
  apply le_antisymm
  · rw [he]
    exact sup_le (le_orbitSpan ρ ⊤ I)
      (le_iSup (fun g : (⊤ : Subgroup D) => I.map (ρ g)) ⟨x, mem_top x⟩)
  · apply orbitSpan_le ρ (by rw [he]; exact le_sup_left)
    apply le_subspaceStabilizer
    intro g _ v hv
    exact W.apply_mem_toSubmodule g hv

private theorem solvable_centralizer_of_supplement {D : Type*} [Group D]
    (K P : Subgroup D) [K.Normal] [Group.IsSolvable P]
    (hg : K ⊔ P = ⊤) (hz : center K = ⊥) :
    Group.IsSolvable (centralizer (K : Set D)) := by
  let q := QuotientGroup.mk' K
  have hmap : P.map q = ⊤ := by
    have he := congrArg (map q) hg
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using he
  have hf : Function.Surjective (q.comp P.subtype) := by
    intro y
    have hy : y ∈ P.map q := by rw [hmap]; trivial
    obtain ⟨p,hp,he⟩ := hy
    exact ⟨⟨p,hp⟩,he⟩
  let : Group.IsSolvable (D ⧸ K) := Group.isSolvable_of_surjective hf
  exact centralizer_solvable_of_centerless_quotient K hz

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The odd L₃ family deduction in the genuine external source setup.
The complete earlier Fitting alternative and solvable supplement give the
small common centralizer; the actual two-conjugate Irr⁺ orbit is fully moved.
All F.9.18(6) branches are handled, and Sylow conjugacy preserves the original
Borel. Naturality, section faithfulness, and the second layer are conclusions.
The parent supplies the displayed SourceOrbit and earlier source inputs. -/
theorem source_natural_sections
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,u} 𝒦)
    (H K X L L₁ L₁plus V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(K.subgroupOf H).Normal] [(X.subgroupOf H).Normal]
    [(Source.starImage H K).Normal]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [Group.IsSolvable (L₁ ⊔ (T : Subgroup G) : Subgroup G)]
    (hH : IsSQTK 𝒦 H) (hgen : H = K ⊔ L₁ ⊔ (T : Subgroup G))
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus))
    (hfit : SolvableExclusion.ResidualAlternative L L₁ L₁plus
      (Components.Fitting.twoFittingResidual H))
    (hK : IsComponent (Source.Hstar H) (Source.starImage H K))
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (n : ℕ) (hn : 1 < n) (ho : Odd n) (hcard : Nat.card F = 2^n)
    (eK : Source.starImage H K ≃* PSL(3,F))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (_hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (s : S₃ →* Source.Hstar H) (hinj : Function.Injective s)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hcubic : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    {E N : Type u} [Group E] [Finite E]
    [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N) (hσ : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (r : LinearTwo.FiveReconstruction.ConstituentRealization ρ (Source.starImage H K) σ
      (generalizedFitting E))
    (hactor : r.actor = Source.starImage H K ⊔ Source.starImage H (T : Subgroup G))
    (W : Subrepresentation ρ)
    (_hne : r.space ≠ r.space.map (ρ (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic)))
    (a : N ≃ₗ[ZMod 2] SectionMultiplicity ρ s (LinearTwo.centralBottom ρ (Source.starImage H K) W) W)
    (ha : ∀ (k : generalizedFitting E) v,
      a (σ k v) = sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs
        (LinearTwo.centralBottom ρ (Source.starImage H K) W) W (r.component.symm k) (a v))
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (_hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (_hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (S : Sylow 2 (Source.starImage H K)) (B₀ : Subgroup (Source.Hstar H))
    (hB : B₀.subgroupOf (Source.starImage H K) = normalizer (S : Set (Source.starImage H K))) :
    Source.starImage H (T : Subgroup G) ≤ subspaceStabilizer ρ r.space ∧
    ∃ e : Source.starImage H K ≃* PSL(3,F),
      (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F ∧
      OneOrTwoNaturalSections ρ (Source.starImage H K).subtype s hs e ho hcard := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Xs.Normal := (inferInstance : (X.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple Ks := hK.2
  have hSQ : IsSQTK 𝒦 (Source.Hstar H) :=
    IrreducibleReduction.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup
  have hx : Nat.card Xs = 3 := by
    change Nat.card (Source.starImage H X) = 3
    rw [← hmark, Subgroup.card_map_of_injective hinj, nat_card_alternatingGroup]
    norm_num
  have hgen' : H = K ⊔ (L₁ ⊔ (T : Subgroup G)) := by simpa only [sup_assoc] using hgen
  have hKH : K ≤ H := by rw [hgen']; exact le_sup_left
  have hPH : L₁ ⊔ (T : Subgroup G) ≤ H := by rw [hgen']; exact le_sup_right
  let P := Source.starImage H (L₁ ⊔ (T : Subgroup G))
  let : Group.IsSolvable P := by
    let : Group.IsSolvable ((L₁ ⊔ (T : Subgroup G)).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hPH).toMonoidHom) (subgroupOfEquivOfLe hPH).injective
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective ((L₁ ⊔ (T : Subgroup G)).subgroupOf H))
  have hGP : Ks ⊔ P = ⊤ := by
    change Source.starImage H K ⊔ Source.starImage H (L₁ ⊔ (T : Subgroup G)) = ⊤
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup hKH hPH, ← hgen']
    simp [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hF : fittingSubgroup (Source.Hstar H) ≤ Xs := by
    rw [← Components.Fitting.twoFittingResidual_star H]
    rcases Structure.selected_fitting_alternative H L L₁ L₁plus X hlocal hfit with hf | hf
    · simp [hf, Source.starImage]
    · rw [hf]
  have hz : center Ks = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro k hk
    have hh := (centerCongr eK ⟨k,hk⟩).property
    change eK k ∈ center PSL(3,F) at hh
    rw [projectiveThree_center_eq_bot ho hcard, mem_bot] at hh
    exact mem_bot.mpr (eK.injective (hh.trans eK.map_one.symm))
  have hc := common_centralizer_le Ks Xs (solvable_centralizer_of_supplement Ks P hGP hz) hF
  have he := orbit_eq_of_two_conjugates ρ W r.space (s cubic) horbit
  obtain ⟨e, hBe⟩ := exists_borel_marking (by omega : 0 < n) hcard eK S
  refine ⟨le_trans (by rw [hactor]; exact le_sup_right) r.stable,
    e, by rw [hB]; exact hBe, ?_⟩
  apply oneOrTwo_of_ff_orbit ρ Ks Xs hB42 LinearTwo.fullIrrInvariance hSQ hx hc
    s hs hmark hcubic hn ho hcard e W σ hσ hff r.component.symm a ha
  · rw [he]
    exact orbitSpan_ne_bot ρ r.irrPlus
  · rw [he]
    exact orbitSpan_full_commutator ρ (by rw [normalizer_eq_top]) r.irrPlus
  · exact hA
  · exact hbound

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
