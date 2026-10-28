module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.CentralDecomposition.CubicAction
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The quaternion central decomposition in J.2.4

Write HB = C_Q(B) and HC = C_H(U). The genuine earlier J.2.2(3)
natural section Q/HC and J.2.3(7) quaternion isomorphism imply
HB ≤ HC, HB ∩ U = Z, and HC = HB U.

The quaternion order ensures that B has a nontrivial image in H/Q:
otherwise B lies in the two-group Q and hence is trivial, making HB = Q.
Cauchy's theorem supplies a cubic image. Its fixed-point freeness on the
two natural sections puts HB in HC and its intersection with U in Z.
The reverse intersection inclusion follows from Z ≤ U ≤ Q and B ≤ H.
Finally |Q/HC| = 16 gives |HC| = 128, while |HB U| = 8·32/2 = 128.

Only `NaturalHead` and the actual quaternion isomorphism remain explicit.
These are earlier-source outputs of `qt-j12-parabolic-structure` and
`qt-j12-special-core`; `qt-j-01-02` owns their final discharge. This proves
the central-product input to both `elementaryFusion_of_centralProduct` and
`sourceJ24_of_centralProduct_of_modZ`, without assuming any decomposition,
intersection or fixed-space conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the opening
sentence of the J.2.4 proof, printed p.434 (PDF p.445), using J.2.1–3.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Fusion
open Subgroup Representation
variable {G : Type*} [Group G] [Finite G]

private theorem BSubgroup_le_H (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    BSubgroup d B ≤ d.H := by
  rintro b ⟨b, _, rfl⟩
  obtain ⟨l, _, hl⟩ := b.property
  change (b : G) ∈ d.H
  rw [← hl]
  exact l.property.2

private theorem exists_cubic_image (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hq : Nonempty (HB d.toTypeRuSetup B ≃* QuaternionGroup 2)) :
    ∃ b : BSubgroup d.toTypeRuSetup B,
      orderOf (d.ru2.quotientMap ⟨b, BSubgroup_le_H d.toTypeRuSetup B b.property⟩) = 3 := by
  let D := d.toTypeRuSetup
  let A := BSubgroup D B
  have hAH : A ≤ D.H := BSubgroup_le_H D B
  let f : A →* S5 := d.ru2.quotientMap.comp (inclusion hAH)
  have hA3 : IsPGroup 3 A := B.isPGroup'.map D.L₁.subtype
  have hrange : f.range ≠ ⊥ := by
    intro he
    have hAQ : A ≤ D.Q := by
      intro a ha
      have hf : f ⟨a, ha⟩ = 1 := by
        have hm : f ⟨a, ha⟩ ∈ f.range := ⟨⟨a, ha⟩, rfl⟩
        rw [he] at hm
        exact hm
      have hk : (⟨a, hAH ha⟩ : D.H) ∈ d.ru2.quotientMap.ker := hf
      rw [d.ru2.quotient_kernel] at hk
      exact hk
    have hdis : Disjoint A D.Q := hA3.disjoint_of_coprime
      (isPGroup_pCoreIn 2 D.H) (by decide)
    have habot : A = ⊥ := le_antisymm (fun a ha =>
      (disjoint_iff_inf_le.mp hdis) ⟨ha, hAQ ha⟩) bot_le
    have hHB : HB D B = D.Q := by
      apply inf_eq_left.mpr
      intro q hq a ha
      have ha1 : a = 1 := by
        have ham : a ∈ A := ha
        rw [habot] at ham
        exact ham
      simp [ha1]
    obtain ⟨e⟩ := hq
    have hc : Nat.card (HB D B) = 8 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      decide
    rw [hHB, d.ru2.card_Q d.card_Z] at hc
    omega
  have hr3 : IsPGroup 3 f.range := hA3.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard : 3 ∣ Nat.card f.range := hr3.card_eq_or_dvd.resolve_left
    (fun he => by have hh := (one_lt_card_iff_ne_bot f.range).mpr hrange; omega)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  obtain ⟨b, hb⟩ := c.property
  refine ⟨b, ?_⟩
  change orderOf (f b) = 3
  rw [hb, Subgroup.orderOf_coe, hc]

private theorem Z_le_HB (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : d.Z ≤ HB d B := by
  refine le_inf (d.ru2.natural.kernel_le.trans d.ru2.six.kernel_le) ?_
  intro z hz b hb
  exact ((BSubgroup_le_H d B hb) z hz).symm

private theorem card_HC (d : LocalSetup G) (head : Outer.NaturalHead d.toTypeRuSetup) :
    Nat.card d.toTypeRuSetup.HC = 128 := by
  have hc := head.sectionData.card_section
  rw [d.ru2.card_Q d.card_Z] at hc
  have hw : Nat.card FourSpace = 16 := by
    rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]
  rw [hw] at hc
  omega


/-- The central decomposition required by J.2.4, from the genuine earlier
natural-section and quaternion conclusions. All three fields refer to the
literal subgroups in `Fusion.Statements`. -/
theorem centralProductData_of_naturalHead (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁)
    (head : Outer.NaturalHead d.toTypeRuSetup)
    (hq : Nonempty (HB d.toTypeRuSetup B ≃* QuaternionGroup 2)) :
    CentralProductData d.toTypeRuSetup B := by
  let D := d.toTypeRuSetup
  have hBH := BSubgroup_le_H D B
  obtain ⟨b, hb⟩ := exists_cubic_image d B hq
  have hHB : HB D B ≤ D.HC :=
    head.action.centralizer_le_kernel_of_cubic_image d.ru2.quotientMap head.sectionData hBH b hb
  have hUZ : D.U ⊓ centralizer (BSubgroup D B : Set G) ≤ D.Z :=
    d.ru2.naturalAction.centralizer_le_kernel_of_cubic_image d.ru2.quotientMap d.ru2.natural hBH b hb
  have hinter : HB D B ⊓ D.U = D.Z := le_antisymm
    (fun x hx => hUZ ⟨hx.2, hx.1.2⟩)
    (le_inf (Z_le_HB D B) d.ru2.natural.kernel_le)
  refine ⟨hq, ?_, hinter⟩
  have hprod : HB D B ⊔ D.U ≤ D.HC := sup_le hHB d.U_le_HC
  apply (Subgroup.eq_of_le_of_card_ge hprod ?_).symm
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (HB D B) D.U
    ((le_centralizer_iff.mp (hHB.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨e⟩ := hq
  have hcardB : Nat.card (HB D B) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  rw [hcardB, d.ru2.card_U d.card_Z, hinter, d.card_Z] at hc
  have hcardHC := card_HC d head
  change Nat.card D.HC = 128 at hcardHC
  omega
end CFSG.Quasithin.ChapterJ.Fusion
