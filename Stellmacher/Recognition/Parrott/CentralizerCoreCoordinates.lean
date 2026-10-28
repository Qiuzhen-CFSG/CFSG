module

public import Stellmacher.Recognition.Parrott.CentralizerCoreCoordinatesData
public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Theory.ElementaryAbelian.OrderedBinaryCoordinates

/-!
# Ordered binary coordinates on Parrott's actual core

Let J = O₂(C_G(z)). The supplied a,b,c,d generate its ambient image, and the
literal quotient J/J′ is elementary abelian of order sixteen. Their quotient
images therefore give an ordered binary basis. Transport along the canonical
isomorphism from J to its ambient image gives a homomorphism whose kernel is
exactly the ambient image of J′.

The construction keeps the supplied elementary subgroup, fusion witnesses and
Sylow frame literally. It uses neither a quotient action nor a tensor model.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.678–681.
-/

open Subgroup

namespace Stellmacher.Recognition
open ParrottCore

/-- The supplied Sylow frame gives ordered binary coordinates on the actual
core, with kernel exactly its actual derived subgroup. All frame data is retained. -/
public theorem parrott_core_coordinates {G : Type*} [Group G] [Finite G] {z : G}
    (h : ParrottCentralizerHypotheses z)
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowGeneratorData n) : Nonempty (Coordinates f) := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let Q := J ⧸ D
  let E : J ≃* Core z := J.equivMapOfInjective H.subtype Subtype.val_injective
  let q : Core z →* Q := (QuotientGroup.mk' D).comp E.symm.toMonoidHom
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective D).comp E.symm.surjective
  let w : Fin 4 → G := ![f.a, f.b, f.c, f.d]
  have hw : Set.range w = ({f.a, f.b, f.c, f.d} : Set G) := by
    ext x
    simp [w, or_comm, or_left_comm]
  have hwm (i : Fin 4) : w i ∈ Core z := by
    change w i ∈ J.map H.subtype
    rw [← f.core_generators]
    apply Subgroup.subset_closure
    rw [← hw]
    exact ⟨i, rfl⟩
  let v : Fin 4 → Core z := fun i => ⟨w i, hwm i⟩
  have hgen : closure (Set.range v) = ⊤ := by
    apply Subgroup.map_injective (f := (Core z).subtype) Subtype.val_injective
    rw [MonoidHom.map_closure]
    have himg : (Core z).subtype '' Set.range v = Set.range w := by
      rw [← Set.range_comp]
      rfl
    rw [himg, hw, f.core_generators]
    exact (Core z).range_subtype.symm.trans (MonoidHom.range_eq_map _)
  have hgenQ : closure (Set.range (fun i => q (v i))) = ⊤ := by
    rw [Set.range_comp', ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective q hq
  obtain ⟨hQ, hcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 Q := hQ
  obtain ⟨c, hc⟩ := elementarySixteen_ordered_coordinates (fun i => q (v i)) hgenQ hcard
  let φ := c.toMonoidHom.comp q
  have hker (g : Core z) : φ g = 1 ↔ (g : G) ∈ Derived z := by
    change c (q g) = 1 ↔ _
    rw [map_eq_one_iff c c.injective]
    change (E.symm g : J ⧸ D) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hg
      refine mem_map.mpr ⟨E.symm g, hg, ?_⟩
      change ((E.symm g : J) : G) = g
      exact congrArg Subtype.val (E.apply_symm_apply g)
    · intro hg
      change (g : G) ∈ D.map (H.subtype.comp J.subtype) at hg
      obtain ⟨j, hj, heq⟩ := mem_map.mp hg
      have hh : E j = g := Subtype.ext heq
      rw [← hh, E.symm_apply_apply]
      exact hj
  have hmap (i : Fin 4) (g : Core z) (hg : (g : G) = w i) :
      (φ g).toAdd = Pi.single i 1 := by
    have heq : g = v i := Subtype.ext hg
    rw [heq]
    exact congrArg Multiplicative.toAdd (hc i)
  refine ⟨⟨φ, hker, ?_, ?_, ?_, ?_⟩⟩
  · intro g hg
    rw [hmap 0 g hg]
    ext i; fin_cases i <;> simp
  · intro g hg
    rw [hmap 1 g hg]
    ext i; fin_cases i <;> simp
  · intro g hg
    rw [hmap 2 g hg]
    ext i; fin_cases i <;> simp
  · intro g hg
    rw [hmap 3 g hg]
    ext i; fin_cases i <;> simp

end Stellmacher.Recognition
