module

public import Theory.Mathieu.M12.Properties.SylowAutomorphisms
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Automorphisms centralizing arbitrary M₁₂ Sylow two-subgroups

Sylow conjugacy moves the subgroup to the marked common Sylow subgroup of
the concrete Witt-design model. Its pointwise automorphism stabilizer consists
of the identity and conjugation by the marked central involution. Transporting
back proves innerness, without any restriction on the automorphism's order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.6,
printed p.1172. This supplies the intrinsic M₁₂ case; covers are treated by
the separate perfect central-quotient transport.
-/

namespace Sporadic.Mathieu
open Subgroup M12SmallPair

/-- Every automorphism fixing any Sylow two-subgroup of the concrete M₁₂
pointwise is inner. In particular this retains arbitrary two-elements. -/
public theorem m12_automorphism_inner_of_fixes_sylow (r : MulAut M12) (S : Sylow 2 M12)
    (hS : ∀ x ∈ S, r x = x) : ∃ g : M12, r = MulAut.conj g := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 commonSylow S
  let e : MulAut M12 := MulAut.conj g
  have hfixed (x : M12) (hx : x ∈ sylowCandidate) :
      MulAut.congr e.symm r x = x := by
    have hmem : e x ∈ S := by
      rw [← hg]
      change e x ∈ sylowCandidate.map e.toMonoidHom
      exact mem_map_of_mem e.toMonoidHom hx
    change e.symm (r (e x)) = x
    rw [hS _ hmem]
    exact e.symm_apply_apply x
  apply (MulAut.congr_inner_iff e.symm r).mp
  rcases SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow _ hfixed with h | h
  · exact ⟨1, h.trans (map_one MulAut.conj).symm⟩
  · exact ⟨z, h⟩

end Sporadic.Mathieu
