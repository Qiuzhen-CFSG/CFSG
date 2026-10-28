module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.LocalAction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Assembly
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoverObstruction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Linear
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Unitary
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.SuzukiSimple

/-!
# Construction of the Bender torus action

`exists_localAction` constructs every field of the published `LocalAction`
interface. The ambient covered-case exclusion first proves Z(L) = 1 from
the earlier cover reduction and the genuine Sylow, centralizer, transport,
Δ₀ and faithfulness inputs. Each remaining rank-one alternative supplies
an actual cyclic matrix torus aligned with the prescribed component Sylow.
The common omega argument then places Ω₁(R) in V and makes its commuting
factor elementary. Coprime action supplies the fixed subgroup and direct
decomposition, and pointwise coverage of the component omega normalizer
gives equality of the actual action images.

The source owner must supply the explicit earlier 16.1/I.2/16.4 conclusions
and complete the geometry and J₁ identification. No actor or action output,
nor triviality of Z(L), is assumed by `exists_localAction`. The common omega
and decomposition APIs still allow U_C and U_L to intersect, and all cover
obstruction diagnostics remain available. The unitary parameter is the
fixed-field order, so the q = 4 case uses matrices over a field of order 16.

Source: Aschbacher–Smith, Proposition 16.5.1, printed pp.1194–1195, with
16.4.10–11 and I.2.2(4), combined manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction

open Subgroup CoverAndSylowElimination

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}

/-- Construct the intrinsic torus and its full omega-normalizer action in
each center-free rank-one model, using the actual quotient by Z(L). -/
theorem exists_componentTorus_of_center_eq_bot (hlocal : CentralComponentSetup T z L)
    (hZ : center L = ⊥) (hn : 2 ≤ n) (hmodel : RankOneAt (L ⧸ center L) n) :
    ∃ d : ComponentTorus T L n, OmegaNormalizerAction T L d.actor := by
  rcases hmodel with hlinear | hunitary | ⟨m, hm, rfl, ⟨e⟩⟩
  · exact exists_componentTorus_psl2 hlocal hZ hn hlinear
  · exact exists_componentTorus_psu3 hlocal hZ hn hunitary
  · exact exists_componentTorus_suzuki hlocal hZ hm e

/-- The local torus action of the first and third paragraphs of 16.5.1.
The extra inputs are precisely the earlier cover reduction (16.1.2/I.2.2),
the Sylow conclusion (16.4.10), and the centralizer equivalence and transport
from 16.4.2(1),(4). The genuine Δ₀ containment and faithfulness are retained;
every field of `LocalAction`, including the actor itself, is constructed. -/
theorem exists_localAction (h : IntersectionSetup T z L g R)
    (hcover : center L ≠ ⊥ → SuzukiCoverInput T L ∧ Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (e : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hn : 2 ≤ n) (hmodel : RankOneAt (L ⧸ center L) n) :
    Nonempty (LocalAction T L R n) := by
  have hZ := CoveredCase.center_eq_bot h hcover hR e htransport hdelta hfaith
  obtain ⟨d, hnorm⟩ := exists_componentTorus_of_center_eq_bot
    h.toStandardSetup.toCentralComponentSetup hZ hn hmodel
  exact localAction_of_componentTorus h hR htransport
    (involutionLifting_of_center_eq_bot hZ) hdelta hfaith hn d hnorm

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
