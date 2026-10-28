module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ParabolicTransport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCohomology

/-!
# B.5.1(6) on the original moved module

For the actual natural-plus-dual branch, first cohomology vanishing gives
V = [V,L] + C_V(G). The full group equals L in this branch. The concrete
SL Sylow-centralizer theorem transports through the specified action
equivalence and then through this fixed supplement. Its core, quotient and
offender assertions therefore concern the original representation and its
literal Sylow fixed space.

This proves the complete clause-(6) implication independently of the
classification induction. No splitting, centralizer or cohomology hypothesis
is added. The classification owner still has to establish which action
alternative occurs.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Every parabolic and offender assertion in B.5.1(6), on the literal source action. -/
theorem MovedSection.sylowFixedCentralizer_of_naturalDual {L : Subgroup G}
    (s : MovedSection ρ L) {d : ℕ} (hd : d = 4 ∨ d = 5) (hL : L = ⊤)
    (hnat : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d)
    (T : Sylow 2 G) : Nonempty (SylowFixedCentralizer ρ L d T) := by
  have hsum := s.fixed_supplement_of_naturalDual ρ (by omega : 4 ≤ d) hL hnat
  subst L
  obtain ⟨e⟩ := hnat
  let f := e.ofTop
  let S := T.mapSurjective (f := f.groupEquiv.toMonoidHom) f.groupEquiv.surjective
  obtain ⟨hS⟩ := NaturalDualCentralizer.sylowFixedCentralizer_naturalPlusDual hd S
  have hS' : SylowFixedCentralizer (naturalPlusDual d)
      ((⊤ : Subgroup G).map f.groupEquiv.toMonoidHom) d S := by
    simpa only [Subgroup.map_top_of_surjective f.groupEquiv.toMonoidHom f.groupEquiv.surjective] using hS
  obtain ⟨hU⟩ := sylowFixedCentralizer_transport f ⊤ d T hS'
  exact sylowFixedCentralizer_of_fixed_supplement ρ s.space hsum ⊤ d T hU

end CFSG.Quasithin.ChapterB.QuasisimpleSource
