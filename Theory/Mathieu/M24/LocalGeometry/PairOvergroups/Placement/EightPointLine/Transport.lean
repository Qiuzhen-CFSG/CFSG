module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.Alternatives
/-!
# Transport of the eight-point invariant-line problem

An actual group equivalence carries an invariant order-three subgroup to
an invariant order-three subgroup and preserves setwise permutability.
Sylow conjugacy therefore reduces the A₈ problem to one fixed Sylow
subgroup. The final result here is conditional on the calculation for that
fixed subgroup; it does not assert that the calculation has been completed.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511;
GLS3, Table 5.3e. Conjugators in the line condition remain elements of A₈.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint

/-- An order-three subgroup fixed by the common inner normalizer. -/
def HasInvariantLine {G : Type*} [Group G] (P D : Subgroup G) : Prop :=
  ∃ C : Subgroup G, C ≤ D ∧ Nat.card C = 3 ∧
    ∀ g ∈ P ⊓ normalizer (D : Set G), ∀ x ∈ C, g * x * g⁻¹ ∈ C

/-- Transport of an invariant line through an actual group equivalence. -/
theorem HasInvariantLine.map {G H : Type*} [Group G] [Group H]
    {P D : Subgroup G} (h : HasInvariantLine P D) (e : G ≃* H) :
    HasInvariantLine (P.map e.toMonoidHom) (D.map e.toMonoidHom) := by
  obtain ⟨C, hCD, hcard, hC⟩ := h
  refine ⟨C.map e.toMonoidHom, map_mono hCD,
    (card_map_of_injective e.injective).trans hcard, ?_⟩
  intro g hg x hx
  obtain ⟨g, hgP, rfl⟩ := hg.1
  obtain ⟨x, hxC, rfl⟩ := hx
  have hgN : g ∈ normalizer (D : Set G) := by
    have hh := hg.2
    rw [← map_equiv_normalizer_eq D e] at hh
    simpa using mem_map_equiv.mp hh
  simpa only [map_mul, map_inv] using
    mem_map_of_mem e.toMonoidHom (hC g ⟨hgP, hgN⟩ x hxC)

/-- The permutability hypothesis is preserved by a group equivalence. -/
theorem permutes_map {G H : Type*} [Group G] [Group H]
    (P D : Subgroup G) (e : G ≃* H)
    (h : (D : Set G) * (P : Set G) = (P : Set G) * (D : Set G)) :
    (D.map e.toMonoidHom : Set H) * (P.map e.toMonoidHom : Set H) =
      (P.map e.toMonoidHom : Set H) * (D.map e.toMonoidHom : Set H) := by
  simpa only [coe_map, Set.image_mul] using congrArg (Set.image e.toMonoidHom) h

/-- Conjugating the Sylow subgroup reduces the problem to any fixed Sylow.
Only inner elements of the ambient group occur as line stabilizers. -/
theorem eightPointPairLine_of_fixedSylow
    (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (hQ : ∀ D : Subgroup (alternatingGroup (Fin 8)), Nat.card D = 9 →
      (D : Set (alternatingGroup (Fin 8))) * (Q : Set (alternatingGroup (Fin 8))) =
        (Q : Set (alternatingGroup (Fin 8))) * (D : Set (alternatingGroup (Fin 8))) →
      HasInvariantLine Q.toSubgroup D) : EightPointPairLine := by
  intro P D _ hcard hperm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) P Q
  let e := MulAut.conj g
  have hP : P.toSubgroup.map e.toMonoidHom = Q.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  have hd : Nat.card (D.map e.toMonoidHom) = 9 :=
    (card_map_of_injective e.injective).trans hcard
  have hp := permutes_map P.toSubgroup D e hperm
  rw [hP] at hp
  have hh := (hQ (D.map e.toMonoidHom) hd hp).map e.symm
  have hbackP : Q.toSubgroup.map e.symm.toMonoidHom = P.toSubgroup := by
    rw [← hP, map_map]
    simp
  have hbackD : (D.map e.toMonoidHom).map e.symm.toMonoidHom = D := by
    rw [map_map]
    simp
  change HasInvariantLine P.toSubgroup D
  simpa only [hbackP, hbackD] using hh

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
end
