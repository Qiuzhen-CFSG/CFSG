module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Heads

/-!
# The unique head of the literal source module

The marked-parabolic calculation supplies one actor identification for every
maximal quotient. The actual image of the source Sylow subgroup is Sylow in
H/O₂(H), so its natural fixed space has dimension one. The generating seed
therefore gives a unique maximal submodule. If the whole module is not natural,
that maximal submodule is nonzero and contains an irreducible submodule.

The source theorem below constructs the seed from V₃/V₁ and its conjugate span;
neither natural heads nor uniqueness are assumptions. The universal B.4 input
retains its faithful, irreducible, small-quadratic-ratio hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed pp.960–961, PDF pp.977–978. Chief-factor exclusion is a separate step.
-/

public section

open Representation Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The nonzero fixed generator ensures that the finite module has a maximal
submodule, even when the whole module is already natural. -/
theorem exists_maximal_of_generatingSeed (ρ : Representation (ZMod 2) H U)
    (s : GeneratingSeed ρ) : ∃ W : Subrepresentation ρ, IsCoatom W := by
  let : IsCoatomic (Subrepresentation ρ) :=
    SimpleHeadQuotient.subrepresentation_coatomic ρ
  obtain ⟨v, _, hv, _, _⟩ := s.exists_fixed_generator ρ
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro he
    exact hv (show v ∈ (⊥ : Subrepresentation ρ) from
      he.symm ▸ (show v ∈ (⊤ : Subrepresentation ρ) from by trivial))
  obtain ⟨W, hW, _⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  exact ⟨W, hW⟩

/-- Retain one maximal submodule for both uniqueness and the later choice of
an irreducible submodule under failure of the natural-module conclusion. -/
theorem unique_head_and_atom (ρ : Representation (ZMod 2) H U)
    (s : GeneratingSeed ρ) (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (T : Sylow 2 H) (hs : s.sylow = (T : Subgroup H))
    (hheads : AllNaturalHeads ρ eH) :
    ∃ W : Subrepresentation ρ, IsCoatom W ∧
      (∀ X : Subrepresentation ρ, IsCoatom X → X = W) ∧
      (¬ IsNatural ρ eH → W ≠ ⊥ ∧
        ∃ I : Subrepresentation ρ, IsAtom I ∧ I ≤ W) := by
  obtain ⟨W, hW⟩ := exists_maximal_of_generatingSeed ρ s
  have hu := unique_maximal_of_natural_heads ρ s eH T hs hheads W hW
  refine ⟨W, hW, hu, ?_⟩
  intro hn
  obtain ⟨X, I, hX, hX0, hI, hIX⟩ :=
    exists_nonzero_maximal_and_atom_of_not_natural ρ s eH hheads hn
  have he := hu X hX
  exact ⟨he ▸ hX0, I, hI, he ▸ hIX⟩

section Source
open Alignment Representation.BinaryOffender
open scoped IsMulCommutative
open Chapter2.ComponentRefinement.LieType.Binary
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearReduction.Parabolics
universe v
variable {G : Type v} [Group G] [Finite G]

/-- The source Sylow subgroup maps to a Sylow subgroup of the literal actor. -/
theorem exists_source_sylow (H T : Subgroup G) (hT : Chapter1.IsSylowIn 2 T H) :
    ∃ S : Sylow 2 (Source.Hstar H), Source.starImage H T = (S : Subgroup _) := by
  obtain ⟨S, hS⟩ := hT
  have hS' : (S : Subgroup H) = T.subgroupOf H := by
    rw [← hS, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)), ?_⟩
  change (T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) =
    (S : Subgroup H).map (QuotientGroup.mk' (pCore 2 H))
  rw [hS']

/-- The common natural heads, their marked plane and their unique maximal
kernel, proved from the earlier source setup. Under failure of the whole-module
natural conclusion the same kernel is nonzero and contains an atom. -/
theorem source_heads_unique_maximal
    (H K M L T V V₁ V₃ Uγ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hT : Chapter1.IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hindex : V₁.relIndex V₃ = 4)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      one L T V₁ ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hquad : IsQuadratic ρ (Source.starImage H Uγ))
    (hbound : fixedCodim ρ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hB4 : ∀ e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace, LinearB4.{v} e) :
    ∃ (e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (P : Submodule (ZMod 2) NaturalSpace) (W : Subrepresentation ρ),
      Module.finrank (ZMod 2) P = 2 ∧
      (Source.starImage H (one L T V₁ ⊔ T)).map e.toMonoidHom = BinaryLinear.parabolic P ∧
      AllNaturalHeads ρ e ∧ IsCoatom W ∧
      (∀ X : Subrepresentation ρ, IsCoatom X → X = W) ∧
      (¬ IsNatural ρ e → W ≠ ⊥ ∧
        ∃ I : Subrepresentation ρ, IsAtom I ∧ I ≤ W) := by
  obtain ⟨_, _, _, _, e, P, _, _, _, _, _, _, hd, hmark, hheads⟩ :=
    exists_marked_allNaturalHeads_of_source H K M L T V V₁ V₃ Uγ d ρ hρ
      hKH hLK hLM hTM hK hKn hT hKT hcover hfactor hrel hNM eK hindex hirr
      hA hquad hbound hB4
  have hTH := (Chapter1.isSylowIn_iff.mp hT).2.1
  have ht := (Chapter1.isSylowIn_iff.mp hT).1
  have hPH : one L T V₁ ⊔ T ≤ H := sup_le (hLK.trans hKH) hTH
  have hN : one L T V₁ ⊔ T ≤ normalizer (V₃ : Set G) := by
    apply sup_le _ d.seed_stable
    rw [hfactor]
    exact sup_le d.plus_normalizes_seed
      ((d.zero_centralizes.trans (centralizer_le d.seed_le)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hline : V₁ < V₃ := lt_of_le_of_ne d.line_le_seed (by
    intro he
    rw [he, relIndex_self] at hindex
    contradiction)
  let s := sourceSeedOfEarlier H V₃ V₁ ρ hρ (one L T V₁ ⊔ T) T hPH le_sup_right ht hN
    hline (fun X hx hy hn => hirr X hx hy (le_sup_left.trans hn)) hindex
  obtain ⟨S, hS⟩ := exists_source_sylow H T hT
  obtain ⟨W, hW, hu, hn⟩ := unique_head_and_atom ρ s e S hS hheads
  exact ⟨e, P, W, hd, hmark, hheads, hW, hu, hn⟩

end Source
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
