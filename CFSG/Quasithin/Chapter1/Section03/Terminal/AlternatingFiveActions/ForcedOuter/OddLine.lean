module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.ForcedOuter.Setup

/-!
# The genuine odd line and quotient action

The inclusion of P ∩ B in B/O₂(B) is injective whenever P is an odd
p-group. It follows that an actor normalizing P and B and fixing this
quotient image centralizes the original intersection. The actual quotient
normalizer action is used throughout. Membership in B C_G(B/O₂(B))
is also converted to an explicit inner conjugator for that action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, Lemma 1.3.9(1), printed p.514.
These are transports; they do not assert that inner actors fix the image.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.ChapterA.Section04
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
variable {G : Type*} [Group G] {p : ℕ} {P B : Subgroup G}

/-- The actual inclusion followed by the intrinsic two-core quotient. -/
def oddLineQuotientMap (P B : Subgroup G) : (P ⊓ B : Subgroup G) →* XiQuotient B :=
  (QuotientGroup.mk' (pCore 2 B)).comp (inclusion inf_le_right)

/-- Coprimality with the intrinsic two-core makes the odd intersection inject. -/
theorem oddLineQuotientMap_injective (hp : Odd p) (hP : IsPGroup p P) :
    Function.Injective (oddLineQuotientMap P B) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hcore : (a : G) ∈ B.pCoreIn 2 := mem_map_of_mem B.subtype
    ((QuotientGroup.eq_one_iff _).mp ha)
  have hd : Disjoint (B.pCoreIn 2) P :=
    (isPGroup_pCoreIn 2 B).disjoint_of_coprime hP hp.coprime_two_left
  exact Subtype.ext (hd.le_bot ⟨hcore, a.property.1⟩)

/-- An actor preserving P and B that fixes the odd quotient image centralizes P ∩ B. -/
theorem centralizes_oddLine_of_quotient_fixes (hp : Odd p) (hP : IsPGroup p P)
    {s : G} (hsP : s ∈ normalizer P) (hsB : s ∈ normalizer B)
    (hfix : ∀ a : B, (a : G) ∈ P →
      twoQuotientNormalizerAction B ⟨s, hsB⟩ (QuotientGroup.mk' (pCore 2 B) a) =
        QuotientGroup.mk' (pCore 2 B) a) :
    s ∈ centralizer (P ⊓ B : Set G) := by
  intro a ha
  change a ∈ P ∧ a ∈ B at ha
  let a₀ : (P ⊓ B : Subgroup G) := ⟨a, ha⟩
  let a₁ : (P ⊓ B : Subgroup G) := ⟨s * a * s⁻¹,
    (mem_normalizer_iff.mp hsP a).mp ha.1,
    (mem_normalizer_iff.mp hsB a).mp ha.2⟩
  have he : oddLineQuotientMap P B a₁ = oddLineQuotientMap P B a₀ := by
    change QuotientGroup.mk' (pCore 2 B) (B.normalizerMonoidHom ⟨s, hsB⟩ ⟨a, ha.2⟩) =
      QuotientGroup.mk' (pCore 2 B) ⟨a, ha.2⟩
    rw [← twoQuotientNormalizerAction_mk]
    exact hfix ⟨a, ha.2⟩ ha.1
  have hval : s * a * s⁻¹ = a :=
    congrArg Subtype.val (oddLineQuotientMap_injective hp hP he)
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- Conjugation by an element of B induces its actual quotient conjugation. -/
theorem quotient_action_component (b : B) :
    twoQuotientNormalizerAction B ⟨b, B.le_normalizer b.property⟩ =
    MulAut.conj (QuotientGroup.mk' (pCore 2 B) b) := by
  ext x
  induction x using Quotient.inductionOn with
  | h a =>
    rw [show (⟦a⟧ : XiQuotient B) = QuotientGroup.mk' (pCore 2 B) a from rfl,
      twoQuotientNormalizerAction_mk, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

private theorem quotient_action_sectionCentralizer {c : G} (hc : c ∈ twoSectionCentralizer B ⊤) :
    twoQuotientNormalizerAction B ⟨c, hc.2.1⟩ = 1 := by
  apply MulEquiv.ext
  intro x
  induction x using Quotient.inductionOn with
  | h a =>
    change twoQuotientNormalizerAction B ⟨c, hc.2.1⟩
      (QuotientGroup.mk' (pCore 2 B) a) = QuotientGroup.mk' (pCore 2 B) a
    rw [twoQuotientNormalizerAction_mk]
    have hb : B.normalizerMonoidHom ⟨c, hc.2.1⟩ a * a⁻¹ ∈ pCore 2 B := by
      obtain ⟨b, hb, he⟩ := hc.2.2 a a.property
      change (b : G) = ⁅c, (a : G)⁆ at he
      have hbe : b = B.normalizerMonoidHom ⟨c, hc.2.1⟩ a * a⁻¹ := by
        apply Subtype.ext
        simpa only [coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe,
          commutatorElement_def] using he
      exact hbe ▸ hb
    have hq : QuotientGroup.mk' (pCore 2 B)
        (B.normalizerMonoidHom ⟨c, hc.2.1⟩ a * a⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hb
    exact mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using hq)

/-- Membership in B C_G(B/O₂(B)) gives an inner conjugator for the actual quotient action. -/
theorem quotient_action_inner_of_mem_innerNormalizer
    (s : normalizer (B : Set G)) (hs : (s : G) ∈ innerTwoQuotientNormalizer B) :
    ∃ b : XiQuotient B, twoQuotientNormalizerAction B s = MulAut.conj b := by
  obtain ⟨b, hb, c, hc, hbc⟩ := (mem_innerTwoQuotientNormalizer_iff B s).mp hs
  let bN : normalizer (B : Set G) := ⟨b, B.le_normalizer hb⟩
  let cN : normalizer (B : Set G) := ⟨c, hc.2.1⟩
  have he : s = bN * cN := Subtype.ext hbc.symm
  refine ⟨QuotientGroup.mk' (pCore 2 B) ⟨b, hb⟩, ?_⟩
  rw [he, map_mul, quotient_action_sectionCentralizer hc, mul_one]
  exact quotient_action_component ⟨b, hb⟩

end CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
