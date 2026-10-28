module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdgeIncidence

/-!
# Four common cubic neighbors in A₅

An A₅-generating pair of cubic subgroups is conjugate to the subgroups
(012) and (034). The cubics (013), (014), (024), (023) are four distinct
common neighbors, in cyclic order, with every displayed edge generating
an actual A₄. The marking and square are transported to any isomorphic
carrier with their literal subgroup embeddings retained.

Source: Aschbacher, *Sporadic Groups* (1994), 47.7(3), p.265. The source
J₂ application combines this square with the ambient four-neighbor count;
the intrinsic calculation alone does not exclude extra ambient neighbors.
-/

@[expose] public section
open Subgroup
namespace alternatingGroup.FiveLocalGeometry.CubicNonedges
open CubicEdges

private theorem nonedge_marking_model (P Q : Subgroup A5) (hP : Nat.card P = 3)
    (hQ : Nat.card Q = 3) (hJ : P ⊔ Q = ⊤) :
    ∃ g : A5, P.map (MulAut.conj g).toMonoidHom = C 0 ∧
      Q.map (MulAut.conj g).toMonoidHom = C 5 := by
  obtain ⟨a, ha⟩ := cubic_conjugate (MulEquiv.refl A5) P (C 0) hP (card_C 0)
  obtain ⟨i, hi⟩ := cubic_representative (Q.map (MulAut.conj a).toMonoidHom)
    (by rw [card_map_of_injective (MulAut.conj a).injective, hQ])
  have hp : P.map (MulAut.conj (adjustment i * a)).toMonoidHom = C 0 := by
    rw [conj_map_mul, ha, (adjustment_maps i).1]
  have hq : Q.map (MulAut.conj (adjustment i * a)).toMonoidHom = C (representative i) := by
    rw [conj_map_mul, hi, (adjustment_maps i).2]
  have hc : Nat.card (C 0 ⊔ C (representative i) : Subgroup A5) = 60 := by
    rw [← hp, ← hq, ← Subgroup.map_sup, card_map_of_injective (MulAut.conj _).injective,
      hJ, card_top, card]
  have cases : representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
    have h : ∀ i, representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
      decide +kernel
    exact h i
  rcases cases with h | h | h
  · rw [h, sup_idem, card_C] at hc
    omega
  · rw [h, model_card] at hc
    omega
  · exact ⟨adjustment i * a, hp, h ▸ hq⟩

/-- Mark a pair of cubic subgroups generating the actual A₅ carrier. -/
theorem exists_nonedge_marking {H : Type*} [Group H] (e : H ≃* A5)
    (P Q : Subgroup H) (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (hJ : P ⊔ Q = ⊤) :
    ∃ a : H ≃* A5, P.map a.toMonoidHom = C 0 ∧ Q.map a.toMonoidHom = C 5 := by
  obtain ⟨g, hp, hq⟩ := nonedge_marking_model (P.map e.toMonoidHom) (Q.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective, hP])
    (by rw [card_map_of_injective e.injective, hQ]) (by
      rw [← Subgroup.map_sup, hJ, map_top_of_surjective _ e.surjective])
  exact ⟨e.trans (MulAut.conj g), by rw [map_map] at hp; exact hp,
    by rw [map_map] at hq; exact hq⟩

private def squareIndex (i : Fin 4) : Fin 10 := ![1,2,4,3] i
private def edgeLeft (i : Fin 12) : Fin 10 := ![0,0,0,0,5,5,5,5,1,2,4,3] i
private def edgeRight (i : Fin 12) : Fin 10 := ![1,2,4,3,1,2,4,3,2,4,3,1] i

private theorem square_edges (i : Fin 12) :
    Nonempty (↥(C (edgeLeft i) ⊔ C (edgeRight i)) ≃* alternatingGroup (Fin 4)) := by
  have ht : ∀ i : Fin 12, ∃ g : A5,
      (g * cycle 0 * g⁻¹ = cycle (edgeLeft i) ∨
        g * cycle 0 * g⁻¹ = (cycle (edgeLeft i))⁻¹) ∧
      (g * cycle 1 * g⁻¹ = cycle (edgeRight i) ∨
        g * cycle 1 * g⁻¹ = (cycle (edgeRight i))⁻¹) := by
    decide +kernel
  obtain ⟨g, hg, hg'⟩ := ht i
  have he : (C 0 ⊔ C 1).map (MulAut.conj g).toMonoidHom =
      C (edgeLeft i) ⊔ C (edgeRight i) := by
    rw [Subgroup.map_sup, map_C_of_cycle hg, map_C_of_cycle hg']
  exact ⟨(MulEquiv.subgroupCongr he.symm).trans
    (((C 0 ⊔ C 1).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans modelEquiv)⟩

/-- Four distinct common neighbors of an A₅-generating cubic pair form a square.
All edges are actual A₄ joins, and the witnesses lie in the original carrier. -/
theorem exists_common_square {H : Type*} [Group H] (e : H ≃* A5)
    (P Q : Subgroup H) (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (hJ : P ⊔ Q = ⊤) :
    ∃ R : Fin 4 → Subgroup H, Function.Injective R ∧
      (∀ i, Nat.card (R i) = 3) ∧
      (∀ i, Nonempty (↥(P ⊔ R i) ≃* alternatingGroup (Fin 4))) ∧
      (∀ i, Nonempty (↥(Q ⊔ R i) ≃* alternatingGroup (Fin 4))) ∧
      (∀ i, Nonempty (↥(R i ⊔ R (i + 1)) ≃* alternatingGroup (Fin 4))) := by
  obtain ⟨a, hp, hq⟩ := exists_nonedge_marking e P Q hP hQ hJ
  let R (i : Fin 4) := (C (squareIndex i)).map a.symm.toMonoidHom
  have hr (i : Fin 4) : (R i).map a.toMonoidHom = C (squareIndex i) := by
    simp [R, map_map]
  have hinj : Function.Injective R := by
    intro i j h
    have hi := CubicEdgeIncidence.C_injective (by
      simpa only [hr] using congrArg (map a.toMonoidHom) h)
    exact (show Function.Injective squareIndex by decide +kernel) hi
  have lift (U V : Subgroup H) (i : Fin 12)
      (hu : U.map a.toMonoidHom = C (edgeLeft i))
      (hv : V.map a.toMonoidHom = C (edgeRight i)) :
      Nonempty (↥(U ⊔ V) ≃* alternatingGroup (Fin 4)) := by
    have he : (U ⊔ V).map a.toMonoidHom = C (edgeLeft i) ⊔ C (edgeRight i) := by
      rw [Subgroup.map_sup, hu, hv]
    exact ⟨((U ⊔ V).equivMapOfInjective _ a.injective).trans
      ((MulEquiv.subgroupCongr he).trans (square_edges i).some)⟩
  refine ⟨R, hinj, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [card_map_of_injective a.symm.injective, card_C]
  · intro i
    fin_cases i
    · exact lift P (R 0) 0 hp (hr 0)
    · exact lift P (R 1) 1 hp (hr 1)
    · exact lift P (R 2) 2 hp (hr 2)
    · exact lift P (R 3) 3 hp (hr 3)
  · intro i
    fin_cases i
    · exact lift Q (R 0) 4 hq (hr 0)
    · exact lift Q (R 1) 5 hq (hr 1)
    · exact lift Q (R 2) 6 hq (hr 2)
    · exact lift Q (R 3) 7 hq (hr 3)
  · intro i
    fin_cases i
    · exact lift (R 0) (R 1) 8 (hr 0) (hr 1)
    · exact lift (R 1) (R 2) 9 (hr 1) (hr 2)
    · exact lift (R 2) (R 3) 10 (hr 2) (hr 3)
    · exact lift (R 3) (R 0) 11 (hr 3) (hr 0)

end alternatingGroup.FiveLocalGeometry.CubicNonedges
