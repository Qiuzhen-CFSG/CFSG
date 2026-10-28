module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.CentralOverlap
public import Theory.Representation.BinaryParabolicNatural.Basic
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.IrreducibleFixedPoints

/-!
# Ordinary fixed-moving vectors on the original component support

Orbit counting supplies an S-fixed nonzero vector of W/Z. Fixed-free
component action makes it moving, and the central-overlap support argument
supplies suitability. This applies with W=U_K,1 in the normal-component
cases and W=U_K in the exchanged-component case, once those actual
sections and their literal normalizers have been constructed.

The natural specialization derives fixed-freeness from a surjective
component marking in the full binary linear group. No assertion about the
fixed radical of an A6 cover is made here.
Source: Aschbacher--Smith, vector choice before 14.6.24, p.1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Select the actual fixed-moving involution on an ordinary section.
The normalizer S remains the literal subgroup supplied by the branch. -/
theorem source_exists_of_fixed_free_central_overlap
    (K W S A : Subgroup G) [Group.IsPerfect K]
    (d : CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    (τ : Representation (ZMod 2) A V)
    (c : BinaryConjugationSection A W (centralInvolutions T) τ)
    (hSA : S ≤ A) (hfree : fixed (τ.comp (K.subgroupOf A).subtype) = ⊥) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le d.support_le
  have hZW : centralInvolutions T < W := by
    apply lt_of_le_of_ne c.kernel_le
    intro he
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    have hz := (c.coordinates_eq_one_iff u).mpr (he.symm ▸ u.property)
    rw [hu] at hz
    exact hv hz
  have hSZ : S ≤ centralizer (centralInvolutions T : Set G) :=
    d.sylow_le.trans (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T))
  obtain ⟨u,hu,huz,huf⟩ := Theory.GroupAction.exists_nonidentity_fixed_modulo
    S W (centralInvolutions T)
    (T.isPGroup'.of_injective (inclusion d.sylow_le)
      (inclusion_injective d.sylow_le))
    (hSA.trans c.normalized) hSZ hZW
  let v := (c.coordinates ⟨u,hu⟩).toAdd
  have hv0 : v ≠ 0 := by
    intro hv
    exact huz ((c.coordinates_eq_one_iff ⟨u,hu⟩).mp hv)
  apply source_exists_of_central_overlap_section_vector
    hG T hempty hM hunique hmany hcard e hab K W S A d τ c hSA v
  · intro s hs
    exact (c.fixed_coordinate_iff_commutator_mem ⟨s,hSA hs⟩ ⟨u,hu⟩).mpr (huf s hs)
  · rw [hfree]
    exact hv0

/-- A full natural marking discharges the fixed-free input in the ordinary
case; the map is on the actual component intersection with its support actor. -/
theorem source_exists_of_natural_central_overlap
    (K W S A : Subgroup G) [Group.IsPerfect K]
    (d : CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (q : A →* BinaryLinear.GL V)
    (hq : Function.Surjective (q.comp (K.subgroupOf A).subtype))
    (c : BinaryConjugationSection A W (centralInvolutions T)
      ((BinaryParabolicNatural.natural V).comp q))
    (hSA : S ≤ A) (hdim : 2 ≤ Module.finrank (ZMod 2) V) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  apply source_exists_of_fixed_free_central_overlap
    hG T hempty hM hunique hmany hcard e hab K W S A d _ c hSA
  apply bot_unique
  intro v hv
  have hn : v ∈ (BinaryParabolicNatural.natural V).invariants := by
    intro g
    obtain ⟨k,rfl⟩ := hq g
    exact hv k
  rwa [BinaryParabolicNatural.natural_invariants hdim] at hn

/-- An ordinary natural A6 section has a fixed-moving vector for its
literal S action. The specified component marking is surjective, and
irreducibility of the actual four-dimensional natural module discharges
fixed-freeness. The five-dimensional cover is handled separately. -/
theorem source_exists_of_alternating_six_natural_central_overlap
    (K W S A : Subgroup G) [Group.IsPerfect K]
    (d : CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    (q : A →* alternatingGroup (Fin 6))
    (hq : Function.Surjective (q.comp (K.subgroupOf A).subtype))
    (c : BinaryConjugationSection A W (centralInvolutions T)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 6)).comp q))
    (hSA : S ≤ A) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  let σ := BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
  let : σ.IsIrreducible := BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  let : Nontrivial (BinaryPermutation.natural (Fin 6)) :=
    Subrepresentation.irreducible_module_nontrivial σ
  have hdim : 2 ≤ Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 6)) := by
    rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  have hf := fixed_eq_bot_of_irreducible_finrank σ hdim
  apply source_exists_of_fixed_free_central_overlap
    hG T hempty hM hunique hmany hcard e hab K W S A d _ c hSA
  apply bot_unique
  intro v hv
  have hn : v ∈ fixed σ := by
    intro g
    obtain ⟨k,rfl⟩ := hq g
    exact hv k
  rwa [hf] at hn

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
