module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Assembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Models
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.MathieuExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Uniqueness
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds

/-!
# Distinguished-plane uniqueness with the Held residual retained

Failure of the source uniqueness theorem produces a triple-Mathieu section
of the actual partner residual. The existing structural alternatives exclude
that section by solvability or abelian Sylow three-subgroups. The additional
Held row excludes it by its order: a group with two-core quotient Held has
order prime to eleven, whereas the triple-Mathieu cover has an eleven-factor.

Consequently original 15.2.15 needs neither the short structural list nor
an ambient Held exclusion. The actual residual identity, earlier wreath
quotients, and original source hypotheses are retained. This does not exclude
Held from 15.2.12(2), or discharge its later partner-core branch in 15.2.27.

Source: Aschbacher--Smith, 15.2.12 and the final proof of 15.2.15,
printed pp.1111 and 1118; the imported concrete Held odd-order bound.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open Sporadic.Mathieu
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B ZS : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

namespace ChosenGeometry

/-- A retained Held residual has order prime to eleven, including its whole two-core. -/
theorem HeldResidualCase.eleven_coprime_card
    (hh : HeldResidualCase T H Mc) : Nat.Coprime 11 (Nat.card (partnerSpan H Mc)) := by
  obtain ⟨P,_,_,_,_,_,_,_,_,_,_,_,⟨e⟩⟩ := hh
  have hHe : Nat.Coprime 11 (Nat.card Held.He) :=
    (by decide : Nat.Coprime 11 (2 ^ 12 * (3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17))).of_dvd_right
      Held.OddPrimary.card_dvd
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := partnerSpan H Mc)).exists_card_eq
  rw [(pCore 2 (partnerSpan H Mc)).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr e.toEquiv,hn]
  exact hHe.mul_right ((by decide : Nat.Coprime 11 2).pow_right n)

/-- The actual Held residual cannot contain the terminal triple-Mathieu section. -/
theorem HeldResidualCase.no_mathieu_section
    (hh : HeldResidualCase T H Mc) (R : Subgroup G) (hR : R ≤ partnerSpan H Mc)
    (e : (R ⧸ pCore 2 R) ≃* M22TripleCover) : False := by
  have hc : Nat.card (R ⧸ pCore 2 R) = 1330560 :=
    (Nat.card_congr e.toEquiv).trans M22TripleCover.card
  have hd : 11 ∣ Nat.card (partnerSpan H Mc) :=
    (show 11 ∣ Nat.card (R ⧸ pCore 2 R) by rw [hc]; decide).trans
      ((card_quotient_dvd_card _).trans (card_dvd_of_le hR))
  exact ((by decide : Nat.Prime 11).coprime_iff_not_dvd.mp hh.eleven_coprime_card) hd

/-- The complete retained residual reduction suffices for the literal terminal section exclusion. -/
theorem ResidualInput.no_mathieu_section
    (r : ResidualInput h H B) (d : PlaneUniquenessPreceding h H ZS)
    (R : Subgroup G) (hR : R ≤ smallActionKc H Mc)
    (e : (R ⧸ pCore 2 R) ≃* M22TripleCover) : False := by
  rcases r.structural_or_held with hs | hh
  · rcases hs with he | ho
    · have hKMc : smallActionKc H Mc ≤ Mc :=
        conjugateSpanBy_le_self ((map_subtype_le _).trans d.geometry.in_partner)
      exact r.no_mathieu_section_in_partner_of_eq he R (hR.trans hKMc) e
    · exact OrdinaryComponents.no_mathieu_section_in_partner d (Or.inr ho) R hR e
  · exact hh.no_mathieu_section R hR e

end ChosenGeometry

/-- Original plane uniqueness using the actual residual input, with no short-list premise. -/
theorem PlaneUniquenessPreceding.source_15_2_15_of_residualInput
    (d : PlaneUniquenessPreceding h H ZS) (r : ResidualInput h H B)
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (ha : letI := h.prepared.elementary;
      Nonempty (internalActionImage M V h.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hi : PlaneUniquenessPreceding.OmegaAction.PlaneInverter h ZS) :
    maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc} := by
  have horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G) := by
    rcases r.component_orbit with he | ⟨P,L,_,_,hL,_,_,_,_,he,_⟩
    · exact Or.inl he
    · exact Or.inr ⟨L,hL.1,he⟩
  by_contra hne
  obtain ⟨R,hR,⟨e⟩⟩ :=
    OrdinaryComponents.exists_mathieu_section_of_nonunique d hquotient horbit ha hi hne
  exact r.no_mathieu_section d R hR e

/-- Application to the original offender plane. Only the actual residual identity and
the preceding wreath recognition remain beyond `ResidualInput`. -/
theorem ChosenGeometry.ResidualInput.plane_uniqueness_of_residual
    (r : ResidualInput h H B)
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (hres : partnerSpan H Mc = threePrimeResidual Mc) :
    maximalTwoLocalOvergroups (Mc ⊓ centralizer (⁅V,B⁆ : Subgroup G)) = {Mc} := by
  let := h.prepared.elementary
  have c := r.constructed_plane
  let d : PlaneUniquenessPreceding h H ⁅V,B⁆ := {
    geometry := c.geometry
    two_maximals := r.two_overgroups
    partner_eq := c.partner_eq
    seed_le := c.seed_le
    center_cases := c.alternatives.elim (fun he => Or.inl he.2) (fun he => Or.inr he.2)
    omega_center := c.omega_center
    residual_centralizes := r.residual_centralizes_plane
    orbit_residual := hres.trans (threePrimeResidual_eq Mc)
    intersection := c.intersection.trans c.centralizer_product }
  rcases c.alternatives with he | ha
  · exact d.unique_of_seed_eq he.2
  have a := h.actionPreceding_of_residual r.outside r.quotient r.two_overgroups hres
  obtain ⟨A,hA,hcard,hm,_,hplanes⟩ := a.common_plane
  let : IsCyclic A := isCyclic_of_prime_card hcard
  obtain ⟨b,hb⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hfix : ⁅V,B⁆ = ambientSpace V
      (fixedSpace (imageRepresentation M V h.prepared.normalized) A) :=
    (hplanes B r.offender).2.2.1.trans (hplanes B r.offender).2.2.2.1
  let i : PlaneUniquenessPreceding.OmegaAction.PlaneInverter h ⁅V,B⁆ := {
    involution := b
    in_sylow := hA (hb ▸ mem_zpowers b)
    order_two := by rw [←Nat.card_zpowers,hb,hcard]
    moves_odd_core := by rw [hb]; exact hm.symm
    fixed_plane := by
      intro v
      rw [hfix,mem_ambientSpace,←hb,mem_fixedSpace_zpowers_iff]
      rfl }
  exact d.source_15_2_15_of_residualInput r hquotient ha.1 i

end CFSG.Quasithin.Chapter15.Section02
