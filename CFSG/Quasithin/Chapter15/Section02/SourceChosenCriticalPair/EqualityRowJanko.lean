module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.MathieuExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualTerminalReduction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.JankoResidual

/-!
# The equality-row Janko-four terminal obstruction

For the actual marked ordinary component, the two-residual of the fixed
subgroup has two-core quotient 3.M22.  The central seed has order two, so
fixing its nonidentity element places this residual directly in Mc.  The
solvable cubic closure of Mc excludes that section in the equality row.

This retains the original component, automorphism and ambient embedding.
It needs neither placement of the fixed residual in Kc nor the identity
Kc = O^{3′}(Mc), and takes no PlaneUniquenessPreceding packet.  The last
application derives the equality row and seed order from the checked
chosen-action terminal reduction.

Source: Aschbacher--Smith, final proof of 15.2.15, printed p.1118,
using 15.2.12(4) and 15.2.14(2), refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Candidates.ComponentStructure OrdinaryComponents
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V} {P : Sylow 2 I} {z : G}

/-- The literal J₄ fixed residual is excluded directly inside Mc.  The
original quotient map is preserved without identifying that residual with Kc. -/
theorem ResidualInput.janko_four_fixed_residual_false_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (hc : Nat.card (centralInvolutions T) = 2)
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (e : (c.component ⧸ pCore 2 c.component) ≃* Janko4.Model)
    (hai : TwoCentralInner a) : False := by
  have ho : orderOf z = 2 := by
    have hd : orderOf (⟨z,hz⟩ : centralInvolutions T) ∣ 2 :=
      hc ▸ orderOf_dvd_natCard (⟨z,hz⟩ : centralInvolutions T)
    rw [← Subgroup.orderOf_coe] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (by simpa using hzne)
  have hZ : zpowers z = centralInvolutions T := eq_of_le_of_card_ge
    (zpowers_le.mpr hz) (by rw [Nat.card_zpowers,ho,hc])
  have hcentral : centralizer ({z} : Set G) = Mc := by
    rw [r.partner_eq_centralizer,←hZ,zpowers_eq_closure,centralizer_closure]
  obtain ⟨er⟩ := janko_four_fixed_residual_quotient c a e hai
  let R := pResidual 2 a.fixedSubgroup
  let f := I.subtype.comp (c.component.subtype.comp a.fixedSubgroup.subtype)
  have hf : Function.Injective f :=
    I.subtype_injective.comp
      (c.component.subtype_injective.comp a.fixedSubgroup.subtype_injective)
  let eR := R.equivMapOfInjective f hf
  have hR : markedFixedResidual c a ≤ Mc := by
    rintro x ⟨y,_,rfl⟩
    apply hcentral.le
    apply mem_centralizer_singleton_iff.mpr
    have hh := ha y
    rw [(MulAut.mem_fixedSubgroup _ _).mp y.property] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  exact r.no_mathieu_section_in_partner_of_eq he (markedFixedResidual c a) hR
    ((QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans er)

/-- On a surviving original input, the terminal reduction supplies the
equality row and seed order; the actual J₄ marking is then impossible. -/
theorem ResidualInput.janko_four_fixed_residual_false
    (r : ResidualInput h H B)
    (hquotient : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((J ⧸ pCore 2 J) ≃* Wreath))
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (e : (c.component ⧸ pCore 2 c.component) ≃* Janko4.Model)
    (hai : TwoCentralInner a) : False := by
  obtain ⟨he,_,hc,_⟩ := source_chosen_index_two_equality_row h r hquotient
  exact r.janko_four_fixed_residual_false_of_eq he hc c hz hzne a ha e hai

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
