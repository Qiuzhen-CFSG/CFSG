module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule.Multiplicity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.Multiplicity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.NaturalOrbit

/-!
# The outside odd-degree linear-three module obstruction

The faithful FF multiplicity action supplies an actual component constituent.
Native recognition and natural cohomology identify its literal lift as natural
or dual. Every ambient conjugate has zero fixed space for the original Borel
residual. Ambient irreducibility makes their sum the whole module, excluding
any nonzero Borel-fixed seed.

Source: Aschbacher–Smith 14.7.42 and 13.8.20(a), printed pp.1061–1062,954–955.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

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
variable {D V : Type u} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Native recognition of an actual constituent in the original module,
retaining its given odd-degree linear-three component marking. -/
theorem linear_constituent
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(3,F)) :
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I),
      IsProjectiveNaturalOrDual ho hF
        ((invariantSubspace ρ K I hI.choose).toRepresentation.comp e.symm.toMonoidHom) := by
  obtain ⟨hsE,hfaith,hoff,hfit⟩ :=
    faithful_ff_multiplicity ρ hf K X hx hcommon s hs hmark hg A hA hquad hbound
  let E := K ⊔ A
  let K₀ := K.subgroupOf E
  let j := (multiplicitySpace (ρ.comp s)).subtype
  let μ := multiplicity (ρ.comp s) (ρ.comp E.subtype)
    (ambient_commute ρ E.subtype s hsE)
  let b : K₀ ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv b.symm
  have hfit₀ : generalizedFitting E = K₀ := hfit
  let : K₀.Normal := hfit₀ ▸ generalizedFitting_normal
  have hKm : K₀.map E.subtype = K := map_subgroupOf_eq_of_le le_sup_left
  have hz : center K₀ = ⊥ := RankTwo.CubicFF.component_center K₀ ho hF (b.trans e)
  obtain ⟨B,I,_,hI,hJI,hB4,hFF,hfit',_⟩ :=
    faithful_irreducible_ff_section μ hfaith K₀ hfit₀ hz (hS.subgroup E) ⟨A.subgroupOf E,hoff⟩
  let r := LinearTwo.centralImageRealization μ K₀ (K₀ ⊔ B) hz le_sup_left I hI hJI hfit'
  let : Finite (centralQuotient μ K₀ I) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective ((fixedSpace μ K₀).comap I.subtype))
  obtain ⟨r',_⟩ := r.exists_mapEmbedding μ ρ E.subtype E.subtype_injective
    j (multiplicitySpace _).subtype_injective (fun _ _ => rfl) K hKm
  let τ := centralSectionRepresentation μ K₀ (K₀ ⊔ B) I hJI le_normalizer_of_normal
  let σ := imageRepresentation τ
  have hqnat := (RankTwo.Native.naturalOrDual_and_ratio σ hB4 hFF hn ho hF
    (centralQuotientRepresentation ρ K r'.space r'.irrPlus.choose) e
    r'.component.symm r'.linearEquiv.symm
      (inverse_intertwines
        (centralQuotientRepresentation ρ K r'.space r'.irrPlus.choose)
        (σ.comp (generalizedFitting (actionImage τ)).subtype)
        r'.component r'.linearEquiv r'.component_intertwines)).1
  exact ⟨r'.space,r'.irrPlus,RankTwo.CubicFF.CentralSplitting.naturalOrDual hn ho hF
    ρ K e r'.space r'.irrPlus hqnat⟩

/-- An irreducible outside odd-degree linear-three action has no fixed vector
for the literal marked Borel residual. -/
theorem linear_fixedSpace_eq_bot
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(3,F)) (B : Subgroup K)
    (hB : B.map e.toMonoidHom =
      Representation.HigherFieldBorelFixedSpaces.twoResidualImage (Matrix.PSL3.LinearThree.borel F)) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ := by
  obtain ⟨I,hI,hnat⟩ := linear_constituent ρ hf K X hS hx hcommon s hs hmark hg
    A hA hquad hbound hn ho hF e
  let W : Subrepresentation ρ :=
    ⟨orbitSpan ρ ⊤ I, fun g v hv => (orbitSpan_invariant ρ ⊤ I (mem_top g) v).2 hv⟩
  have hW : W ≠ ⊥ := by
    intro he
    exact orbitSpan_ne_bot ρ hI (congrArg Subrepresentation.toSubmodule he)
  have ht : W = ⊤ := (hi.eq_bot_or_eq_top W).resolve_left hW
  have hWt : orbitSpan ρ ⊤ I = ⊤ := congrArg Subrepresentation.toSubmodule ht
  have hz := RankTwo.NaturalOrbit.orbit_inf_fixedSpace_eq_bot hn ho hF ρ K e B hB I hI hnat
  simpa only [hWt,top_inf_eq] using hz

/-- A nonzero seed fixed by the marked Borel residual excludes this outside
linear-three action. -/
theorem linear_fixed_seed_false
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(3,F)) (B : Subgroup K)
    (hB : B.map e.toMonoidHom =
      Representation.HigherFieldBorelFixedSpaces.twoResidualImage (Matrix.PSL3.LinearThree.borel F))
    (v : V) (hv : v ≠ 0) (hfix : ∀ b : B, ρ b.val.val v = v) : False := by
  have hz := linear_fixedSpace_eq_bot ρ hf hi K X hS hx hcommon s hs hmark hg
    A hA hquad hbound hn ho hF e B hB
  have hh : v ∈ fixedSpace (ρ.comp K.subtype) B := hfix
  exact hv (by simpa only [hz,Submodule.mem_bot] using hh)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule
