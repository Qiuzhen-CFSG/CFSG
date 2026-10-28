module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Basic
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry

/-!
# Outer conjugacy and the actual inner centralizer in degree five

Symmetric Gram factorization gives an explicit inner conjugator carrying
any outer involution to inverse transpose. The faithful conjugation map
identifies its fixed subgroup in GL₅(2) with its centralizer inside the
inner subgroup of Aut(GL₅(2)). The existing compatible fixed-group model
then gives the actual symmetric-six centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
two assertions of H.9.2(1), printed p.390 (PDF p.401).
The module decomposition is a separate assertion.
-/

@[expose] public section

open BinaryLinear BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.FiveActors

theorem outer_conjugate_graph (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    ∃ g : G, MulAut.conj (MulAut.conj g) t = graphLinear 5 := by
  obtain ⟨k, hk, rfl⟩ := SixSylowActors.Five.exists_symmetric_twist t ht hout
  obtain ⟨h, hh⟩ := SixSylowActors.Five.symmetric_gram k hk
  refine ⟨slEquivLinear 5 h, ?_⟩
  apply MulEquiv.ext
  intro x
  change MulAut.conj (slEquivLinear 5 h)
    ((graphLinear 5 * MulAut.conj (slEquivLinear 5 k))
      ((MulAut.conj (slEquivLinear 5 h))⁻¹ x)) = graphLinear 5 x
  rw [SixSylowActors.Five.gram_intertwines k h hh]
  exact congrArg (graphLinear 5) ((MulAut.conj _).apply_symm_apply x)

theorem outer_conjugate (s t : M) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hsout : s ∉ L) (htout : t ∉ L) :
    ∃ a : M, MulAut.conj a s = t := by
  obtain ⟨g, hg⟩ := outer_conjugate_graph s hs hsout
  obtain ⟨h, hh⟩ := outer_conjugate_graph t ht htout
  refine ⟨(MulAut.conj h)⁻¹ * MulAut.conj g, ?_⟩
  have he := congrArg (MulAut.conj ((MulAut.conj h)⁻¹)) (hg.trans hh.symm)
  simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using he

def innerCentralizer (t : M) : Subgroup M :=
  L ⊓ Subgroup.centralizer {t}

theorem fixed_iff_inner_centralizer (t : M) (g : G) :
    g ∈ t.fixedSubgroup ↔ MulAut.conj g ∈ innerCentralizer t := by
  have hi := MulAut.conj_injective_of_center_eq_bot center_eq_bot
  rw [MulAut.mem_fixedSubgroup]
  constructor
  · intro hg
    refine ⟨⟨g, rfl⟩, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, hg]
  · intro hg
    apply hi
    have hc := (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
    have he : MulAut.conj (t g) = t * MulAut.conj g * t⁻¹ := by
      ext x
      simp
    rw [he, ← hc, mul_inv_cancel_right]

noncomputable def fixedInnerCentralizerEquiv (t : M) :
    t.fixedSubgroup ≃* innerCentralizer t :=
  MulEquiv.ofBijective
    (((MulAut.conj : G →* M).comp t.fixedSubgroup.subtype).codRestrict
      (innerCentralizer t) (fun g => (fixed_iff_inner_centralizer t g).mp g.property))
    ⟨fun x y h => Subtype.ext
      ((MulAut.conj_injective_of_center_eq_bot center_eq_bot) (congrArg Subtype.val h)), by
      intro a
      obtain ⟨g, hg⟩ := a.property.1
      refine ⟨⟨g, (fixed_iff_inner_centralizer t g).mpr ?_⟩, ?_⟩
      · simpa only [hg] using a.property
      · exact Subtype.ext hg⟩

theorem innerCentralizer_equiv_six (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    Nonempty (innerCentralizer t ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨m⟩ := SixSylowActors.Five.exists_fixedModel t ht hout
  exact ⟨(fixedInnerCentralizerEquiv t).symm.trans m.equiv⟩

end BinaryNaturalDual.FiveActors
