module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.DerivedAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction
public import Theory.SpecificGroups.ReeF4.DerivedTits

/-!
# Every automorphism of the full binary Ree group is inner

The actual derived subgroup of the full binary Ree group is isomorphic to
Parrott's Tits group, and conjugation by the full group acts bijectively on
the automorphisms of its derived subgroup. These two proved inputs construct
an actual multiplicative equivalence with the full Tits automorphism group.
The automorphism-tower theorem for a centerless simple group then gives
innerness for every automorphism of the full binary Ree group, and hence for
those of two-power order.

Source: Aschbacher–Smith F.1.12, printed pp.263–264 of
`refs/quasithin.pdf`. The source identifies `Aut(²F₄(2)')` with `²F₄(2)`
and excludes further binary extensions. Here `Model 0` is the actual
exceptional-twist fixed subgroup. The unconditional `binary_inner` and its
two-power specialization discharge both comparison inputs. They supply the
binary automorphism assertion needed by the source's extension argument;
the other local and amalgam conclusions of F.1.12 are separate results.
-/

public section

namespace ReeF4.Parabolics.OuterLocal

/-- An actual comparison with the full Tits automorphism group transports
the proved automorphism-tower innerness theorem to the binary Ree carrier. -/
theorem binary_inner_of_titsAut_equiv
    (e : Model 0 ≃* MulAut Tits.ParrottGroup) (α : MulAut (Model 0)) :
    ∃ g : Model 0, MulAut.conj g = α := by
  obtain ⟨β, hβ⟩ := Tits.aut_parrottGroup_inner (MulAut.congr e α)
  obtain ⟨g, hg⟩ := (MulAut.congr_inner_iff e α).mp ⟨β, hβ.symm⟩
  exact ⟨g, hg.symm⟩

/-- The two independent comparison inputs suffice for binary Ree innerness. -/
theorem binary_inner_of_derived_action
    (e : commutator (Model 0) ≃* Tits.ParrottGroup)
    (h : Function.Bijective binaryDerivedAction) (α : MulAut (Model 0)) :
    ∃ g : Model 0, MulAut.conj g = α :=
  binary_inner_of_titsAut_equiv (binaryTitsAutEquiv e h) α

/-- Every automorphism of the full exceptional fixed matrix group ²F₄(2)
is inner. The derived-group comparison and full automorphism coverage are
both supplied by their concrete constructions. -/
theorem binary_inner (α : MulAut (Model 0)) :
    ∃ g : Model 0, MulAut.conj g = α := by
  obtain ⟨e⟩ := ReeF4.DerivedTits.nonempty_derived_equiv
  exact binary_inner_of_derived_action e (binaryDerivedAction_bijective e) α

/-- The full binary Ree group has no further two-power outer automorphisms,
as needed in the binary extension case of Aschbacher–Smith F.1.12. -/
theorem binary_inner_of_twoPower (α : MulAut (Model 0)) (n : ℕ)
    (_hpow : α ^ (2 ^ n) = 1) : ∃ g : Model 0, MulAut.conj g = α :=
  binary_inner α

end ReeF4.Parabolics.OuterLocal
