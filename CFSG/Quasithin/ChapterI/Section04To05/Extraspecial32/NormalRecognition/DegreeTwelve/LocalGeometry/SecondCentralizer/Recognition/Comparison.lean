module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.Kernel

/-!
# Full centralizer marking and the A₄ extension branch

Every involution is internally conjugate into the seed's odd-index image.
Thus an equivalence agreeing with the literal local inclusion preserves the
entire ambient first class; its agreement also preserves the distinguished t.

In the A₄ kernel branch, the index-four formula gives centralizer order 48.
The seed embedding is then surjective and its inverse is already the required
marked C₂ × S₄ equivalence. Only the A₅ branch requires an extension theorem.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.2.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Equiv Equiv.Perm
variable {G : Type*} [Group G] [Finite G] {z t : G}

namespace LocalExtension
variable {s : LocalSeed z t} {n : ℕ} {hn : 4 ≤ n} (c : LocalExtension s n hn)

omit [Finite G] in
theorem central : c.equiv (distinguished t) = centralInvolution n := by
  rw [← s.central, c.agrees_on_local, modelInclusion_central]

theorem first (hz : orderOf z = 2) (a : Centralizer t) :
    IsConj z (a : G) ↔ FirstClass (c.equiv a) := by
  by_cases ha : orderOf a = 2
  · obtain ⟨x, hx⟩ := s.involution_conjugate_into_range a ha
    have hG := (Centralizer t).subtype.map_isConj hx
    have hM := c.equiv.toMonoidHom.map_isConj hx
    have hfirst : FirstClass (c.equiv a) ↔ FirstClass x :=
      (firstClass_conj_iff hM).trans (by
        change FirstClass (c.equiv (s.embed x)) ↔ FirstClass x
        rw [c.agrees_on_local]
        exact modelInclusion_first n hn x)
    exact ⟨fun h => hfirst.mpr ((s.first x).mp (h.trans hG)),
      fun h => ((s.first x).mpr (hfirst.mp h)).trans hG.symm⟩
  · apply iff_of_false
    · intro h
      exact ha ((Subgroup.orderOf_coe a).symm.trans ((conjugate_order h).symm.trans hz))
    · intro h
      exact ha ((c.equiv.orderOf_eq a).symm.trans h.1)

def markedModel (hz : orderOf z = 2) : MarkedModel z t n where
  equiv := c.equiv
  central := c.central
  first := c.first hz
end LocalExtension


noncomputable def LocalSeed.markedModel_of_card (s : LocalSeed z t)
    (hcard : Nat.card (Centralizer t) = 48) : MarkedModel z t 4 := by
  have hr : s.embed.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [Subgroup.card_top, s.range_card, hcard])
  let e : Model 4 ≃* Centralizer t := MulEquiv.ofBijective s.embed
    ⟨s.injective, MonoidHom.range_eq_top.mp hr⟩
  refine ⟨e.symm, ?_, ?_⟩
  · exact e.symm_apply_eq.mpr s.central.symm
  · intro a
    have ha := s.first (e.symm a)
    have he : s.embed (e.symm a) = a := e.apply_symm_apply a
    rwa [he] at ha

noncomputable def TransferKernel.markedModel_four {s : LocalSeed z t} (d : TransferKernel s)
    (e : d.K ≃* alternatingGroup (Fin 4)) : MarkedModel z t 4 := by
  have hK : Nat.card d.K = 12 := (Nat.card_congr e.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by simp))
  apply s.markedModel_of_card
  have h := d.K.card_mul_index
  rw [hK, d.index] at h
  exact h.symm

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
end
