module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.G2.Inner
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.G2.Restriction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.G2.ModelComponents
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# G₂ fixed-component restriction by induction on the field degree

A central involution of the acting two-group is either inner, when the proved
parabolic rank obstruction excludes the seven subgroup, or outer. In the outer
case an actual smaller-field fixed-group isomorphism permits restriction of the
whole actor and induction. The binary endpoint uses the order 12096; the trivial
actor uses simplicity and the whole-model order. Both A₇ and its perfect central
three-cover are retained throughout.

The outer fixed-group isomorphisms are still an explicit mathematical input.
They require the separately owned inner-field automorphism coverage and G₂
field-involution descent theorems. Thus `g2_of_outerInvolutionDescent` is a
conditional assembly, not the completed G₂ branch of E.6.18. No component is
promoted from the common fixed group to a single-involution centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252/PDF p.263; Theorem C and Remark A.2.4, printed p.33.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2
open Subgroup Theory.GroupTheory Atlas.G2

/-- The genuine smaller-field fixed-group input for outer involutions.
Automorphism coverage and coefficient descent must both be proved to supply it. -/
def OuterInvolutionDescent : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ a : MulAut (Model F), orderOf a = 2 →
    (∀ g : Model F, a ≠ MulAut.conj g) →
    ∃ m : ℕ, 0 < m ∧ m < n ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = 2 ^ m ∧ Nonempty (a.fixedSubgroup ≃* Model K)

private theorem central_involution {X : Type*} [Group X] [Finite X]
    (P : Subgroup (MulAut X)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ a : P, a ∈ center P ∧ orderOf (a : MulAut X) = 2 := by
  let : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hne
  let : Nontrivial (center P) := hp.center_nontrivial
  obtain ⟨n, hn, hc⟩ := (hp.to_subgroup (center P)).nontrivial_iff_card.mp inferInstance
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 (by
    rw [hc]
    exact dvd_pow_self 2 (by omega))
  exact ⟨a.val, a.property, (Subgroup.orderOf_coe a.val).trans
    ((Subgroup.orderOf_coe a).trans ha)⟩

private theorem fixed_bot (X : Type*) [Group X] :
    FixedPoints.subgroup (⊥ : Subgroup (MulAut X)) X = ⊤ := by
  apply top_unique
  intro x _ a
  have ha : a.val = 1 := mem_bot.mp a.property
  change a.val x = x
  rw [ha]
  rfl

/-- Induction uses the entire restricted actor on the smaller fixed model.
It never asserts that the original component is a component of an individual
involution centralizer. The outer fixed-group classification remains explicit. -/
theorem model_noSevenFixedComponent (hd : OuterInvolutionDescent) (n : ℕ) :
    ∀ (F : Type) [Field F] [Finite F], 0 < n → Nat.card F = 2 ^ n →
      NoSevenFixedComponent (Model F) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F _ _ hn hcard
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    by_cases hn1 : n = 1
    · subst n
      intro P _ L _ _ hs
      have hv := (seven_card_dvd hs).trans L.card_subgroup_dvd_card
      rw [Atlas.G2.card_Model, hcard] at hv
      norm_num at hv
    have hn2 : 2 ≤ n := by omega
    have hq : 4 ≤ Nat.card F := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2
    intro P hp L hLF hc hs
    by_cases hP : P = ⊥
    · subst P
      rw [fixed_bot] at hc
      have he : (L.subgroupOf ⊤).map
          (Subgroup.topEquiv : (⊤ : Subgroup (Model F)) ≃* Model F).toMonoidHom = L := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, mem_top x⟩, hx, rfl⟩
      exact model_component_not_seven hq L (he ▸ hc.map_equiv Subgroup.topEquiv) hs
    obtain ⟨a, hac, hao⟩ := central_involution P hp hP
    have hfixed : FixedPoints.subgroup P (Model F) ≤ a.val.fixedSubgroup := by
      intro x hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx a)
    by_cases hinner : ∃ g : Model F, a.val = MulAut.conj g
    · obtain ⟨g, hg⟩ := hinner
      let : IsQuasisimple (L.subgroupOf (FixedPoints.subgroup P (Model F))) := hc.2
      let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe hLF).toMonoidHom) (subgroupOfEquivOfLe hLF).surjective
      have hgo : orderOf g = 2 := by
        rw [hg, orderOf_injective MulAut.conj
          (conj_injective_of_center_eq_bot
            (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot (by omega)))] at hao
        exact hao
      have hLg : L ≤ centralizer ({g} : Set (Model F)) := by
        rw [hg, MulAut.fixedSubgroup_conj] at hfixed
        exact hLF.trans hfixed
      exact not_seven_centralizing_involution g hgo L hLg hs
    · obtain ⟨m, hm, hmn, K, _, _, hK, ⟨e⟩⟩ := hd F n hn2 hcard a.val hao
        (fun g he => hinner ⟨g, he⟩)
      have hsmall := NoSevenFixedComponent.of_equiv e (ih m hmn K hm hK)
      exact not_seven_of_restriction P hp L a.val.fixedSubgroup hLF hc hfixed
        (centralFixedRestriction P a hac) (centralFixedRestriction_apply P a hac) hsmall hs

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie

/-- The G₂ inspection follows once the genuine outer-involution fixed models
are supplied. The source theorem remains pending until this premise is proved. -/
theorem g2_of_outerInvolutionDescent (hd : G2.OuterInvolutionDescent)
    {S : Type*} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : ClassificationModels.IsG2At S (2 ^ f)) : SevenActionInspection S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact (G2.NoSevenFixedComponent.of_equiv e
    (G2.model_noSevenFixedComponent hd f F (by omega) hF)).inspection

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
