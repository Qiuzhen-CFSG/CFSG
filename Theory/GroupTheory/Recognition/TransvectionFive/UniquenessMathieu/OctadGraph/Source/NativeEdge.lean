module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeLine
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.System

/-!
# The native edge fixer in the actual trio action

The affine quotient's three-letter permutation is the literal action on
the three native octads. Fixing the two marked octads is equivalent to
triviality of that permutation. The point–line group fixes one letter,
so its commutators fix the entire edge, while a lifted transposition of
the other letters supplies an element outside the edge fixer.

`AlignEdge` uses these facts and the source derived-subgroup description
to preserve the actual edge under the simultaneous row-flag comparison.
Source: Aschbacher, *Sporadic Groups* (1994), 20.2, p.97, and 41.4, p.222.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativeLine
open M24ChapterHStabilizers M24ChapterHStabilizers.OctadAction
open PairOvergroups PairOvergroups.QuotientConstruction
open MathieuCode.TrioCalculation

/-- The actual action of the marked trio stabilizer on its three octads. -/
@[expose] def lineAction : trioStabilizer standardTrio →* Equiv.Perm (Fin 3) :=
  (MonoidHom.fst _ _).comp standardAffineHom

theorem lineAction_surjective : Function.Surjective lineAction := by
  intro p
  obtain ⟨g,hg⟩ := standardAffineHom_surjective (p,1)
  exact ⟨g,congrArg Prod.fst hg⟩

/-- Fixing a native octad is exactly fixing its label in the trio action. -/
theorem lineAction_fix_iff (g : trioStabilizer standardTrio) (i : Fin 3) :
    lineAction g i = i ↔ (g : M24) • standardTrioOctad i = standardTrioOctad i := by
  obtain ⟨t,ht⟩ := affineQuotient_spec affineCoverage g
  change HasAffineForm g (standardAffineHom g) t at ht
  constructor
  · intro hg
    apply Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_smul_finset])
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨⟨j,v⟩,rfl⟩ := point.surjective y
    have hj := (point_mem_octad_iff j i v).mp hy
    subst j
    change g.val.val (point (i,v)) ∈ _
    rw [ht]
    change point (lineAction g i,_) ∈ _
    rw [hg]
    exact point_mem_octad i _
  · intro hg
    have hh := (MulAction.mem_stabilizer_finset'.mp
      (show (g : M24) ∈ MulAction.stabilizer M24 (standardTrioOctad i) from hg))
      (point_mem_octad i 0)
    change g.val.val (point (i,0)) ∈ _ at hh
    rw [ht] at hh
    exact (point_mem_octad_iff _ _ _).mp hh

/-- The full native edge fixer is the embedded kernel of this three-point action. -/
theorem lineAction_edge_iff (g : trioStabilizer standardTrio) :
    lineAction g = 1 ↔ (g : M24) ∈ system.edgeGroup := by
  change _ ↔ (g : M24) ∈ MulAction.stabilizer M24 first ∧
    (g : M24) ∈ MulAction.stabilizer M24 second
  have h0 : lineAction g 0 = 0 ↔ (g : M24) ∈ MulAction.stabilizer M24 first := by
    rw [lineAction_fix_iff]
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  have h1 : lineAction g 1 = 1 ↔ (g : M24) ∈ MulAction.stabilizer M24 second := by
    rw [lineAction_fix_iff]
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  rw [← h0,← h1]
  exact (by decide : ∀ p : Equiv.Perm (Fin 3), p = 1 ↔ p 0 = 0 ∧ p 1 = 1) _

/-- Native edge elements lie in the literal standard trio stabilizer. -/
theorem edge_le_trio : system.edgeGroup ≤ trioStabilizer standardTrio :=
  edgeFixer_le_trio first_adj_second first_on_standardTrio second_on_standardTrio

/-- Commutators of the native point–line group fix the entire marked edge. -/
theorem pointLine_commutator_le :
    ⁅octadStabilizer first ⊓ trioStabilizer standardTrio,
      octadStabilizer first ⊓ trioStabilizer standardTrio⁆ ≤ system.edgeGroup := by
  apply commutator_le.mpr
  rintro a ⟨haO,haT⟩ b ⟨hbO,hbT⟩
  let a' : trioStabilizer standardTrio := ⟨a,haT⟩
  let b' : trioStabilizer standardTrio := ⟨b,hbT⟩
  apply (lineAction_edge_iff ⁅a',b'⁆).mp
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact (by decide : ∀ p q : Equiv.Perm (Fin 3),
    p 0 = 0 → q 0 = 0 → p * q = q * p) _ _
    ((lineAction_fix_iff a' 0).mpr haO) ((lineAction_fix_iff b' 0).mpr hbO)

/-- The native point–line group acts nontrivially on the two octads other
than its fixed vertex. -/
theorem exists_pointLine_not_edge :
    ∃ n : octadStabilizer first,
      (n : M24) ∈ trioStabilizer standardTrio ∧ (n : M24) ∉ system.edgeGroup := by
  obtain ⟨n,hn⟩ := lineAction_surjective (Equiv.swap 1 2)
  have hO : (n : M24) ∈ octadStabilizer first :=
    (lineAction_fix_iff n 0).mp (by rw [hn]; decide)
  refine ⟨⟨n,hO⟩,n.property,?_⟩
  intro he
  have hh := (lineAction_edge_iff n).mpr he
  rw [hn] at hh
  exact (by decide : (Equiv.swap (1 : Fin 3) 2) ≠ 1) hh

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativeLine
