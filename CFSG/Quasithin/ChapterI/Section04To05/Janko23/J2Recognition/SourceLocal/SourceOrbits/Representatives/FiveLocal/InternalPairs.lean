module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Vertices
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdges

/-!
# Two marked cubic pairs in the five-local component

Transport the natural three-cycles (012), (013), and (034) through an
actual A₅ equivalence. The existing generation proofs identify their A₄
and A₅ joins. A small kernel-checked calculation identifies the literal
common normalizer of the A₅-generating pair with the subgroup generated
by (12)(34), giving an actual C₂ equivalence. Sylow conjugacy retains
conjugating elements inside the ambient component.

These are the internal constructions in Aschbacher, *Sporadic Groups*
(1994), 47.5, printed p.263. Root marking and ambient normalizer control
are separate obligations; neither is assumed to follow from the pair data.
-/

@[expose] public section

open Subgroup
open alternatingGroup.FiveLocalGeometry alternatingGroup.FiveLocalGeometry.CubicEdges
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal

def pairInvolution : A5 := ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel⟩

theorem pairInvolution_order : orderOf pairInvolution = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem normalizer_inf_nonedge :
    normalizer (C 0 : Set A5) ⊓ normalizer (C 5 : Set A5) = zpowers pairInvolution := by
  have hc : ∀ g : A5,
      (g * cycle 0 * g⁻¹ = 1 ∨ g * cycle 0 * g⁻¹ = cycle 0 ∨
        g * cycle 0 * g⁻¹ = (cycle 0)⁻¹) →
      (g * cycle 5 * g⁻¹ = 1 ∨ g * cycle 5 * g⁻¹ = cycle 5 ∨
        g * cycle 5 * g⁻¹ = (cycle 5)⁻¹) → g = 1 ∨ g = pairInvolution := by
    decide +kernel
  apply le_antisymm
  · intro g hg
    rcases hc g ((mem_C _ _).mp ((hg.1 _).mp (mem_zpowers _)))
      ((mem_C _ _).mp ((hg.2 _).mp (mem_zpowers _))) with h | h
    · exact h ▸ one_mem _
    · exact h ▸ mem_zpowers _
  · apply zpowers_le.mpr
    constructor <;> apply mem_normalizer_iff_map_conj_eq.mpr <;>
      apply map_C_of_cycle <;> decide +kernel

noncomputable def nonedgeFixerEquiv :
    ↥(normalizer (C 0 : Set A5) ⊓ normalizer (C 5 : Set A5)) ≃*
      Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr normalizer_inf_nonedge).trans
    (involutionZpowersEquiv pairInvolution pairInvolution_order).symm


open Theory.GroupTheory.GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G]

/-- The actual two pairs inside a specified A₅ containing X, before ambient
normalizer and root identification. -/
structure InternalPairs (D : Seed G) (L : Subgroup G) where
  edge : D.Vertex
  edge_le : edge.val ≤ L
  edge_conjugate : ∃ g : L, D.X.map (MulAut.conj (g : G)).toMonoidHom = edge.val
  edge_join : (D.X ⊔ edge.val : Subgroup G) ≃* alternatingGroup (Fin 4)
  five : D.Vertex
  five_le : five.val ≤ L
  five_conjugate : ∃ g : L, D.X.map (MulAut.conj (g : G)).toMonoidHom = five.val
  five_join : D.X ⊔ five.val = L
  internalFixerEquiv :
    ↥(normalizer (D.X.subgroupOf L : Set L) ⊓
      normalizer (five.val.subgroupOf L : Set L)) ≃* Multiplicative (ZMod 2)

/-- Construct the two pairs by transporting the marked three-cycles. -/
theorem internalPairs_nonempty (D : Seed G) (L : Subgroup G)
    (e : L ≃* A5) (hX : D.X ≤ L) : Nonempty (InternalPairs D L) := by
  have hPX : Nat.card (D.X.subgroupOf L) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv, D.card_X]
  obtain ⟨g, hg⟩ := cubic_conjugate (MulEquiv.refl A5)
    ((D.X.subgroupOf L).map e.toMonoidHom) (C 0)
    (by rw [card_map_of_injective e.injective, hPX]) (card_C 0)
  let a := e.trans (MulAut.conj g)
  have ha : (D.X.subgroupOf L).map a.toMonoidHom = C 0 := by
    rw [map_map] at hg
    exact hg
  let f := L.subtype.comp a.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp a.symm.injective
  have hzero : (C 0).map f = D.X := by
    rw [← ha, map_map]
    have he : f.comp a.toMonoidHom = L.subtype := by
      ext x
      simp [f]
    rw [he, map_subgroupOf_eq_of_le hX]
  let T (i : Fin 10) : Subgroup G := (C i).map f
  have hle (i : Fin 10) : T i ≤ L := by
    rintro _ ⟨x, _, rfl⟩
    exact (a.symm x).property
  have hcard (i : Fin 10) : Nat.card (T i) = 3 := by
    rw [card_map_of_injective hf, card_C]
  let V (i : Fin 10) : D.Vertex := ⟨T i,
    AlternatingFiveGeometry.mem_vertex_of_card_three D L e hX (T i) (hcard i) (hle i)⟩
  have hsup (i : Fin 10) : D.X ⊔ (V i).val = (C 0 ⊔ C i).map f := by
    rw [Subgroup.map_sup, hzero]
  have htop : (⊤ : Subgroup A5).map f = L := by
    rw [show f = L.subtype.comp a.symm.toMonoidHom from rfl, ← map_map,
      map_top_of_surjective _ a.symm.surjective]
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hfive : D.X ⊔ (V 5).val = L := by
    rw [hsup, nonedge_join, htop]
  have hcoord (i : Fin 10) : ((V i).val.subgroupOf L).map a.toMonoidHom = C i := by
    apply map_injective (f := f) hf
    rw [map_map]
    have he : f.comp a.toMonoidHom = L.subtype := by ext x; simp [f]
    rw [he, map_subgroupOf_eq_of_le (hle i)]
  let N : Subgroup L := normalizer (D.X.subgroupOf L : Set L) ⊓
    normalizer ((V 5).val.subgroupOf L : Set L)
  have hn : N.map a.toMonoidHom =
      normalizer (C 0 : Set A5) ⊓ normalizer (C 5 : Set A5) := by
    rw [map_inf _ _ _ a.injective, map_equiv_normalizer_eq,
      map_equiv_normalizer_eq, ha, hcoord]
  refine ⟨{
    edge := V 1
    edge_le := hle 1
    edge_conjugate := AlternatingFiveGeometry.conjugate_of_card_three D L e hX _ (hcard 1) (hle 1)
    edge_join := (MulEquiv.subgroupCongr (hsup 1)).trans
      (((C 0 ⊔ C 1).equivMapOfInjective f hf).symm.trans modelEquiv)
    five := V 5
    five_le := hle 5
    five_conjugate := AlternatingFiveGeometry.conjugate_of_card_three D L e hX _ (hcard 5) (hle 5)
    five_join := hfive
    internalFixerEquiv := (N.equivMapOfInjective a.toMonoidHom a.injective).trans
      ((MulEquiv.subgroupCongr hn).trans nonedgeFixerEquiv) }⟩


end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
