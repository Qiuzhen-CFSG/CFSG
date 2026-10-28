module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Incidence
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.Mathieu.M24.LocalGeometry.Stabilizers.Generation

/-!
# Native octad action and literal stabilizer cosets

The octad action is faithful by simplicity and its nontrivial orbit. The
existing native octad–sextet generation theorem supplies global generation
for the marked flag. Orbit–stabilizer gives an explicit equivariant bijection
from left cosets of the actual octad stabilizer to the 759 native vertices;
its edge-orbit graph is exactly the disjoint-octad graph. Edge stabilizers
preserve the unique actual trio through their ends.

Source: Aschbacher, *Sporadic Groups* (1994), §20 and §41, pp.219–222.
The local generation identities and the cycle-base condition are separate
obligations in constructing the full uniqueness system.
-/

@[expose] public section
noncomputable section
open scoped Pointwise
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph
open PairOvergroups
open Theory.GroupTheory.GraphUniquenessSystem

/-- There are 759 native vertices. -/
theorem card_vertices : Nat.card Octad = 759 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using m24Blocks_cardinality

/-- The octad action is faithful: its kernel is normal in simple M24, and its orbit is nontrivial. -/
theorem faithful (g : M24) (hg : ∀ O : Octad, g • O = O) : g = 1 := by
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  let f := MulAction.toPermHom M24 Octad
  have hk : f.ker = ⊥ := by
    rcases f.normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, ha⟩ := vertex_transitive first second
      have hm : a ∈ f.ker := by rw [h]; trivial
      have he : a • first = first := congrArg (fun e : Equiv.Perm Octad => e first) hm
      exact False.elim (first_adj_second.ne (he.symm.trans ha))
  have hm : g ∈ f.ker := Equiv.ext hg
  rwa [hk] at hm

/-- The global generation axiom uses the literal marked octad and sextet. -/
theorem generate : sextetStabilizer standardSextet ⊔ MulAction.stabilizer M24 first = ⊤ := by
  rw [stabilizer_octad, sup_comm]
  exact Stabilizers.standard_pair_generates

/-- The quotient map retains the literal left-coset convention. -/
def cosetToOctad (O : Octad) (q : M24 ⧸ octadStabilizer O) : Octad :=
  ⟨MulAction.ofQuotientStabilizer M24 O.val q, by
    have h := MulAction.ofQuotientStabilizer_mem_orbit M24 O.val q
    rw [orbit_octad] at h
    exact h⟩

@[simp] theorem cosetToOctad_mk (O : Octad) (g : M24) :
    cosetToOctad O (QuotientGroup.mk g) = g • O := rfl

theorem cosetToOctad_bijective (O : Octad) : Function.Bijective (cosetToOctad O) := by
  constructor
  · intro a b he
    exact MulAction.injective_ofQuotientStabilizer M24 O.val (congrArg Subtype.val he)
  · intro P
    obtain ⟨g, hg⟩ := vertex_transitive O P
    exact ⟨QuotientGroup.mk g, hg⟩

/-- Equivariant identification of native octads with cosets of their actual stabilizer. -/
def cosetEquiv (O : Octad) : (M24 ⧸ octadStabilizer O) ≃ Octad :=
  Equiv.ofBijective (cosetToOctad O) (by exact cosetToOctad_bijective O)

@[simp] theorem cosetEquiv_mk (O : Octad) (g : M24) :
    cosetEquiv O (QuotientGroup.mk g) = g • O := rfl

theorem cosetEquiv_smul (O : Octad) (g : M24) (q : M24 ⧸ octadStabilizer O) :
    cosetEquiv O (g • q) = g • cosetEquiv O q :=
  Subtype.ext (MulAction.ofQuotientStabilizer_smul M24 O.val g q)

/-- The orbit graph on the literal cosets is exactly the native octad graph. -/
theorem coset_graph_adj_iff (t : M24) (ht : t • first = second)
    (a b : M24 ⧸ octadStabilizer first) :
    Cosets.Adj (octadStabilizer first) t a b ↔
      graph.Adj (cosetEquiv first a) (cosetEquiv first b) := by
  constructor
  · rintro ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simpa only [Cosets.vertex, cosetEquiv_mk, mul_smul, ht] using
        preserves g first_adj_second
    · simpa only [Cosets.vertex, cosetEquiv_mk, mul_smul, ht] using
        (preserves g first_adj_second).symm
  · intro h
    obtain ⟨g, h1, h2⟩ := edge_transitive h
    refine ⟨g, Or.inl ⟨(cosetEquiv first).injective h1, ?_⟩⟩
    apply (cosetEquiv first).injective
    simpa only [Cosets.vertex, cosetEquiv_mk, mul_smul, ht] using h2

/-- Fixing the ends of a native edge preserves its unique line. -/
theorem edgeFixer_le_trio {O P : Octad} (hOP : graph.Adj O P) {T : Trio}
    (hO : OnLine O T) (hP : OnLine P T) : edgeFixer M24 O P ≤ trioStabilizer T := by
  intro g hg
  have hOT : OnLine O (g • T) := by
    have h := (onLine_smul_iff g O T).mpr hO
    rwa [show g • O = O from hg.1] at h
  have hPT : OnLine P (g • T) := by
    have h := (onLine_smul_iff g P T).mpr hP
    rwa [show g • P = P from hg.2] at h
  have he : g • T = T := (existsUnique_line hOP).unique ⟨hOT,hPT⟩ ⟨hO,hP⟩
  exact congrArg Trio.parts he

/-- Reversing an edge also preserves its unique actual trio. -/
theorem edgeStabilizer_le_trio {O P : Octad} (hOP : graph.Adj O P) {T : Trio}
    (hO : OnLine O T) (hP : OnLine P T) : edgeStabilizer M24 O P ≤ trioStabilizer T := by
  intro g hg
  rcases hg with hf | hs
  · exact edgeFixer_le_trio hOP hO hP hf
  · have hOT : OnLine O (g • T) := by
      simpa only [hs.2] using (onLine_smul_iff g P T).mpr hP
    have hPT : OnLine P (g • T) := by
      simpa only [hs.1] using (onLine_smul_iff g O T).mpr hO
    exact congrArg Trio.parts ((existsUnique_line hOP).unique ⟨hOT,hPT⟩ ⟨hO,hP⟩)

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph
