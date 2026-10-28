module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Centralizer
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.EndpointReduction.Order21
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.EndpointReduction.LinearNormalizer
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.EndpointReduction.Covers
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.EndpointReduction.UnitaryFrattini

/-!
# Reducing the exceptional Bender action to the linear endpoint

The exceptional cardinalities force n = 2, excluding the Suzuki alternative
whose field exponent is 2m+1 with m ≥ 1. The order-21 action generates an
irreducible action on V. In the unitary case the two generating actors preserve
the embedded Frattini subgroup of T_L. The concrete unitary Sylow calculation
in `UnitaryFrattini` proves Φ(T_L) = Ω₁(T_L). After removing the component
center using the cover data, this is a nonzero proper invariant subgroup,
a contradiction.

The remaining linear isomorphism is transported through the actual center
quotient and the checked field-four matrix comparison. The normalizer equality
then follows from `LinearNormalizer`, without an assumed equality or a J₁
recognition hypothesis. `Covers` discharges the center condition from (E1) and
the genuine restricted cover datum. `Geometry.linear_endpoint_of_source_cover`
discharges the Frattini premise of the earlier conditional reductions. The
source proposition's owner supplies the geometry, exceptional action
cardinalities, earlier faithfulness and genuine cover datum. The order-21
cardinality of the actual action image suffices here; its nonabelianness
from the exceptional O'Nan outcome requires no additional hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1194–1195, Proposition 16.5.1.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G]

/-- Degree two leaves only the two actual classical quotient models. -/
theorem Geometry.quotient_models_at_four {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n)
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8) :
    ClassicalGroup.IsPSL (L ⧸ center L) 2 4 ∨
      ClassicalGroup.IsPSU (L ⧸ center L) 3 4 := by
  have hn := d.degree_eq_two hUC hV
  rcases d.model with hp | hu | ⟨m, hm, hnm, _⟩
  · exact Or.inl (by simpa [hn] using hp)
  · exact Or.inr (by simpa [hn] using hu)
  · omega

/-- Compare any field-four linear model with the specified carrier through A₅. -/
theorem pslFour_equiv_of_isPSL {A : Type*} [Group A]
    (h : ClassicalGroup.IsPSL A 2 4) : Nonempty (A ≃* PSLFour) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  obtain ⟨g⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; decide)
  exact ⟨e.trans (f.trans g.symm)⟩

variable [Finite G]

/-- Conditional assembly after the two precise component-model facts.
The center and Frattini premises still have to be discharged from source inputs. -/
theorem Geometry.linear_endpoint_of_center_and_frattini {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) (h : StandardSetup T z L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21)
    (hc : center L = ⊥)
    (hphi : ClassicalGroup.IsPSU (L ⧸ center L) 3 4 →
      (frattini (componentSylow T L)).map (componentSylow T L).subtype =
        omegaOneAmbient (componentSylow T L)) :
    Nonempty (L ≃* PSLFour) ∧
      normalizer (L : Set G) = L ⊔ centralizer (L : Set G) := by
  rcases d.quotient_models_at_four hUC hV with hp | hu
  · let eQ : L ≃* (L ⧸ center L) :=
      (QuotientGroup.quotientBot (G := L)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hc).symm
    obtain ⟨e⟩ := pslFour_equiv_of_isPSL (hp.of_mulEquiv eQ)
    exact ⟨⟨e⟩, d.normalizer_eq_join_of_pslFour h e hA⟩
  · exact False.elim (d.unitary_frattini_contradiction h hfaith hUC hV hA hc
      (by simpa [d.degree_eq_two hUC hV] using hu) (hphi hu))

/-- The endpoint reduction with the central cover removed using source inputs.
Only the intrinsic unitary Frattini calculation remains an extra premise. -/
theorem Geometry.linear_endpoint_of_source_cover_and_frattini {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) (h : StandardSetup T z L)
    (heven : HasEvenTypeCentralizers G)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21)
    (hcover : center L ≠ ⊥ →
      Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hphi : ClassicalGroup.IsPSU (L ⧸ center L) 3 4 →
      (frattini (componentSylow T L)).map (componentSylow T L).subtype =
        omegaOneAmbient (componentSylow T L)) :
    Nonempty (L ≃* PSLFour) ∧
      normalizer (L : Set G) = L ⊔ centralizer (L : Set G) :=
  d.linear_endpoint_of_center_and_frattini h hfaith hUC hV hA
    (d.center_eq_bot_of_source_cover h heven hUC hV hcover) hphi

/-- The exceptional Bender endpoint, with both intrinsic component-model
conditions proved. The genuine cover datum and the O'Nan cardinalities remain
source inputs; no Frattini identity, irreducibility, actor generation or
normalizer equality is assumed. -/
theorem Geometry.linear_endpoint_of_source_cover {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) (h : StandardSetup T z L)
    (heven : HasEvenTypeCentralizers G)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21)
    (hcover : center L ≠ ⊥ →
      Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    Nonempty (L ≃* PSLFour) ∧
      normalizer (L : Set G) = L ⊔ centralizer (L : Set G) := by
  have hc := d.center_eq_bot_of_source_cover h heven hUC hV hcover
  exact d.linear_endpoint_of_center_and_frattini h hfaith hUC hV hA hc
    (componentSylow_frattini_eq_omega_of_psuFour h.sylow_normalizes hc)

end CFSG.Quasithin.Chapter16.Intersections.Bender
