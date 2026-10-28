module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.Omega
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.Suzuki
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.ConjugateSpan
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.SmallLinear
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson

/-!
# Weak closure in the linear and Suzuki branches of the Bender geometry

The center-free odd-outer-index route proves V = Ω₁(T). The Suzuki branch
discharges the automorphism premise through its actual model and removes
the exceptional cover using the genuine ambient covered-case exclusion.
The conjugate-family calculation proves the source span identity from
universal inner placement and the actual LocalAction.

For PSL₂(4), the universal earlier-source exclusion 16.4.6 gives inner
placement for every applicable conjugate configuration, and hence the
conjugate-family span identity. For PSL₂(2ⁿ), n > 2, the actual semilinear
action excludes outer offenders and gives the elementary Thompson identity.
This includes even field degrees; no odd-outer-index assumption is made
in the linear branch.

`space_weakly_closed` combines all these branches, discharging centerlessness
through the ambient Suzuki-cover exclusion and deriving the Delta-zero
containment from LocalAction. Its conclusion is exactly the weak-closure
input of `GeometryConstruction.geometry_of_local_action`. LocalAction and
the genuine earlier cover, Sylow, transport, centralizer, faithfulness and
universally quantified 16.4.6 inputs remain explicit. Their construction and
the final source Proposition 16.5.1 remain with the geometry assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194. The source J(T) is the maximum-elementary Thompson
subgroup of Definition B.2.2, printed pp.74–75.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
open Subgroup CoverAndSylowElimination

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}

/-- The three center-free cases: conjugate span in degree two, the maximum
elementary Thompson subgroup in larger linear degree, and omega for Suzuki.
The 16.4.6 input retains all applicable conjugate-centralizer configurations. -/
theorem space_weakly_closed_of_center_eq_bot
    (h : IntersectionSetup T z L g R) (hZ : center L = ⊥)
    (hn : 2 ≤ n) (hmodel : RankOneAt (L ⧸ center L) n)
    (hunitary : ¬ ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n))
    (d : LocalAction T L R n)
    (hconj : R = (commutingSylow T L).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (h1646 : n = 2 → SmallLinear.FiveOuterPGLExclusion T z L) :
    ∀ a : G, (benderSpace T L).conjBy a ≤ (T : Subgroup G) →
      (benderSpace T L).conjBy a = benderSpace T L := by
  rcases hmodel with hlinear | hunitary' | ⟨m, hm, _, ⟨e⟩⟩
  · by_cases hn2 : n = 2
    · subst n
      exact SmallLinear.space_weakly_closed h hZ (by simpa using hlinear)
        d hconj hfaith (h1646 rfl)
    · exact LinearThompson.space_weakly_closed_psl2 h.toStandardSetup hZ
        (by omega) hlinear d
  · exact (hunitary hunitary').elim
  · exact space_weakly_closed_suzuki h.toStandardSetup hZ hm e d

/-- Weak closure of the actual Bender space in every nonunitary rank-one case.
The exceptional central cover is excluded using the genuine earlier-source
data, rather than discarded as a model case. Neither weak closure, a span
identity, a Thompson identity nor an offender bound is assumed. -/
theorem space_weakly_closed
    (h : IntersectionSetup T z L g R)
    (hcover : center L ≠ ⊥ → SuzukiCoverInput T L ∧ Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (eR : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hn : 2 ≤ n) (hmodel : RankOneAt (L ⧸ center L) n)
    (d : LocalAction T L R n)
    (h1646 : n = 2 → SmallLinear.FiveOuterPGLExclusion T z L) :
    ¬ ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
      ∀ a : G, (benderSpace T L).conjBy a ≤ (T : Subgroup G) →
        (benderSpace T L).conjBy a = benderSpace T L := by
  have hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L :=
    d.omega_le.trans (sup_le
      (((omegaOneAmbient_le _).trans inf_le_right).trans le_sup_left)
      (((omegaOneAmbient_le _).trans inf_le_right).trans le_sup_right))
  have hZ := TorusConstruction.CoveredCase.center_eq_bot
    h hcover hR eR htransport hdelta hfaith
  intro hunitary
  exact space_weakly_closed_of_center_eq_bot h hZ hn hmodel hunitary d
    (h.eq_conjugate_commutingSylow hR htransport) hfaith h1646

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
