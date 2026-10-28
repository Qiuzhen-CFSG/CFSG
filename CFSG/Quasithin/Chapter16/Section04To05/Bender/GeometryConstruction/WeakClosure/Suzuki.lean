module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.Omega
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase.Exclusion
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Weak closure for the Suzuki quotient

The actual central-quotient isomorphism and centerlessness identify L with
the concrete Suzuki matrix group. Its proved odd outer index makes every
two-element act inner, so the omega argument proves weak closure of V.

The second theorem removes the centerlessness premise using the ambient
covered-case exclusion. It retains the exceptional cover reduction, center
order bound, relative Sylow and transport inputs, 16.4.2(1) equivalence,
Delta-zero containment and faithfulness. These are explicit earlier-source
inputs; this module does not construct them or the LocalAction datum.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, with 16.1.2 and I.2.2(4) for the permitted cover.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
open Subgroup BenderSuzuki.MatrixGroups
open CoverAndSylowElimination
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z g : G}
  {L R : Subgroup G} {n m : ℕ}

/-- Discharge two-element innerness through the actual Suzuki model. -/
theorem space_weakly_closed_suzuki (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hm : 1 ≤ m) (e : (L ⧸ center L) ≃* SuzukiMatrixGroup m)
    (d : LocalAction T L R n) (a : G)
    (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L := by
  let c : L ≃* SuzukiMatrixGroup m :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  apply space_weakly_closed_of_inner h hZ _ d a ha
  intro α k hα
  have hp : (MulAut.congr c α) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hα, map_one]
  obtain ⟨b, hb⟩ := MulAut.inner_of_two_pow_eq_one_of_odd_index
    (suzuki_odd_outer_index m hm) (MulAut.congr c α) hp
  refine ⟨c.symm b, (MulAut.congr c).injective ?_⟩
  rw [MulAut.congr_conj, c.apply_symm_apply]
  exact hb

/-- The ambient cover exclusion handles the nontrivial-center branch. -/
theorem space_weakly_closed_suzuki_of_cover_reduction
    (h : IntersectionSetup T z L g R)
    (hcover : center L ≠ ⊥ → SuzukiCoverInput T L ∧ Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (eR : R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hm : 1 ≤ m) (e : (L ⧸ center L) ≃* SuzukiMatrixGroup m)
    (d : LocalAction T L R n) (a : G)
    (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L := by
  have hZ := TorusConstruction.CoveredCase.center_eq_bot
    h hcover hR eR htransport hdelta hfaith
  exact space_weakly_closed_suzuki h.toStandardSetup hZ hm e d a ha

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
