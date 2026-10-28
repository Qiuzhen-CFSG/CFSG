module

public import Theory.GroupTheory.DoubleCoverCentralizer.InvertedDisplacement

/-!
# Transport of non-two-central displacements

A group isomorphism sends the witness x for an automorphism b to e(x) for
its transported action. It preserves both the order of the displacement
and the failure of centrality in every Sylow two-subgroup.

This is the transport used in the exceptional quotient-model calculations
of Aschbacher–Smith I.2.2, observation (iii), printed p.411 / PDF p.422.
The actual model witnesses are constructed in the specific-group modules.
-/

public section
namespace Theory.GroupTheory.DoubleCoverCentralizer

/-- Transport both the carrier witness and its non-two-central mark. -/
theorem HasNonTwoCentralDisplacement.map {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) (b : MulAut G) (hb : HasNonTwoCentralDisplacement b) :
    HasNonTwoCentralDisplacement (MulAut.congr e b) := by
  obtain ⟨x, hx, hn⟩ := hb
  have hd : e x * ((MulAut.congr e b) (e x))⁻¹ = e (x * (b x)⁻¹) := by
    simp [MulAut.congr_apply]
  refine ⟨e x, ?_, ?_⟩
  · rw [hd, e.orderOf_eq, hx]
  · rw [hd]
    intro h
    let : Finite H := Finite.of_equiv G e.toEquiv
    exact hn (by simpa using h.map e.symm)

end Theory.GroupTheory.DoubleCoverCentralizer
