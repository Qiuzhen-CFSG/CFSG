module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.NativeLift
public import Theory.GroupTheory.Amalgam.AutomorphismTransport
public import Theory.GroupTheory.Amalgam.NormalBaseAction
public import Theory.SpecificGroups.Triality.ParabolicNormalizer

/-!
# Coherent native lifts of the marked triality amalgam

The two full native parabolics generate the carrier, so their compatible
restrictions determine an automorphism uniquely. The accepted simultaneous
lifting theorem makes restriction surjective for every m > 1. Consequently
an action on the marked pair has one coherent homomorphism lift. Inner
flag automorphisms are exactly the full native Borel, by self-normalization
of both full parabolics, retaining every Cartan factor.

Source: Aschbacher–Smith 5.3.2, p.659, and F.4.24, pp.287–288.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter5.Section03TrialitySource
open ChapterF.SourceCompletion.TrialityNonbinary

variable {m : ℕ} {hm : 0 < m}

abbrev diagram (m : ℕ) (hm : 0 < m) := nativeAmalgam m hm

def flagAutomorphisms (m : ℕ) (hm : 0 < m) : Subgroup (MulAut (BinaryCarrier m hm)) :=
  MulAction.stabilizer (MulAut (BinaryCarrier m hm))
      (parabolic (binaryParameters m hm) .arms) ⊓
    MulAction.stabilizer (MulAut (BinaryCarrier m hm))
      (parabolic (binaryParameters m hm) .central)

def markedRestriction {U : Type*} [Group U] (P B Q : Subgroup U)
    (hBP : B ≤ P) (hBQ : B ≤ Q) (hB : P ⊓ Q = B) :
    (MulAction.stabilizer (MulAut U) P ⊓ MulAction.stabilizer (MulAut U) Q :
      Subgroup (MulAut U)) →*
    RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B Q hBP hBQ)
      (RankTwoAmalgam.ofSubgroups P B Q hBP hBQ) where
  toFun a :=
    { left := (a.val.subgroupMap _).trans (MulEquiv.subgroupCongr a.property.1)
      middle := (a.val.subgroupMap _).trans (MulEquiv.subgroupCongr (by
        rw [←hB, Subgroup.map_inf _ _ _ a.val.injective]
        change (a.val • P) ⊓ (a.val • Q) = _
        rw [a.property.1, a.property.2]))
      right := (a.val.subgroupMap _).trans (MulEquiv.subgroupCongr a.property.2)
      left_commutes _ := rfl
      right_commutes _ := rfl }
  map_one' := by
    apply RankTwoAmalgam.Iso.ext <;> apply MulEquiv.ext <;> intro x <;>
      apply Subtype.ext <;> rfl
  map_mul' a b := by
    apply RankTwoAmalgam.Iso.ext <;> apply MulEquiv.ext <;> intro x <;>
      apply Subtype.ext <;> rfl

def restriction : flagAutomorphisms m hm →*
    RankTwoAmalgam.Iso (diagram m hm) (diagram m hm) :=
  markedRestriction _ _ _ (borel_le_parabolic _ .arms) (borel_le_parabolic _ .central)
    (parabolic_inf_binary (binaryParameters m hm) rfl)

theorem restriction_injective : Function.Injective (restriction (m := m) (hm := hm)) := by
  intro a b he
  apply Subtype.ext
  apply (RankTwoAmalgam.pairRestriction_eq_iff _ _
    (native_generate m hm) a.val b.val a.property.1 a.property.2
      b.property.1 b.property.2).mp
  apply RankTwoAmalgam.Iso.ext
  · exact congrArg (fun e => e.left) he
  · ext x : 1
    apply Subtype.ext
    exact congrArg (fun e => (e.left ⟨x.val,x.property.1⟩).val) he
  · exact congrArg (fun e => e.right) he

def innerBorel : borel (binaryParameters m hm) →* flagAutomorphisms m hm :=
  (MulAut.conj.comp (borel (binaryParameters m hm)).subtype).codRestrict _ (fun g =>
    ⟨mem_normalizer_iff_map_conj_eq.mp
        ((parabolic (binaryParameters m hm) .arms).le_normalizer
          (borel_le_parabolic _ .arms g.property)),
      mem_normalizer_iff_map_conj_eq.mp
        ((parabolic (binaryParameters m hm) .central).le_normalizer
          (borel_le_parabolic _ .central g.property))⟩)

theorem innerBorel_apply (b : borel (binaryParameters m hm)) :
    (innerBorel b).val = MulAut.conj b.val := rfl

theorem inner_flag_iff (g : BinaryCarrier m hm) :
    MulAut.conj g ∈ flagAutomorphisms m hm ↔
      g ∈ borel (binaryParameters m hm) := by
  constructor
  · intro hg
    have hp := normalizer_parabolic_binary (binaryParameters m hm) rfl .arms
    have hq := normalizer_parabolic_binary (binaryParameters m hm) rfl .central
    rw [← parabolic_inf_binary (binaryParameters m hm) rfl]
    exact ⟨(hp ▸ mem_normalizer_iff_map_conj_eq.mpr hg.1),
      (hq ▸ mem_normalizer_iff_map_conj_eq.mpr hg.2)⟩
  · intro hg
    exact (innerBorel (⟨g,hg⟩ : borel (binaryParameters m hm))).property

def reverseHom {A B C : Type*} [Group A] [Group B] [Group C]
    (α : RankTwoAmalgam A B C) :
    RankTwoAmalgam.Iso α α →* RankTwoAmalgam.Iso α.reverse α.reverse where
  toFun := RankTwoAmalgam.Iso.reverse
  map_one' := rfl
  map_mul' _ _ := rfl

def reverseRestriction : flagAutomorphisms m hm →*
    RankTwoAmalgam.Iso (diagram m hm).reverse (diagram m hm).reverse :=
  (reverseHom (diagram m hm)).comp restriction

private theorem reverseHom_injective {A B C : Type*} [Group A] [Group B] [Group C]
    (α : RankTwoAmalgam A B C) : Function.Injective (reverseHom α) := by
  intro a b he
  apply RankTwoAmalgam.Iso.ext
  · exact congrArg (fun e => e.right) he
  · exact congrArg (fun e => e.middle) he
  · exact congrArg (fun e => e.left) he

private theorem reverse_twice {A B C D E F : Type*}
    [Group A] [Group B] [Group C] [Group D] [Group E] [Group F]
    {α : RankTwoAmalgam A B C} {β : RankTwoAmalgam D E F}
    (a : RankTwoAmalgam.Iso α β) : a.reverse.reverse = a := by
  cases a
  rfl

theorem reverseRestriction_injective : Function.Injective (reverseRestriction (m := m) (hm := hm)) :=
  (reverseHom_injective (diagram m hm)).comp restriction_injective

private theorem lift_unique {A B D : Type*} [Group A] [Group B] [Group D]
    (r : A →* B) (hr : Function.Injective r) (ρ : D →* B)
    (hρ : ∀ d, ρ d ∈ r.range) : ∃! σ : D →* A, r.comp σ = ρ := by
  choose f hf using hρ
  let σ : D →* A :=
    { toFun := f
      map_one' := hr (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hr (by rw [hf, map_mul, map_mul, hf, hf]) }
  refine ⟨σ, ?_, ?_⟩
  · ext x : 1; exact hf x
  · intro τ hτ; ext x : 1; apply hr
    exact (congrArg (fun a : D →* B => a x) hτ).trans (hf x).symm

variable {D : Type*} [Group D]

theorem existsUnique_lift (ρ : D →* RankTwoAmalgam.Iso (diagram m hm) (diagram m hm))
    (hρ : ∀ d, ρ d ∈ (restriction (m := m) (hm := hm)).range) :
    ∃! σ : D →* flagAutomorphisms m hm, restriction.comp σ = ρ :=
  lift_unique restriction restriction_injective ρ hρ

theorem existsUnique_reverse_lift
    (ρ : D →* RankTwoAmalgam.Iso (diagram m hm).reverse (diagram m hm).reverse)
    (hρ : ∀ d, ρ d ∈ (reverseRestriction (m := m) (hm := hm)).range) :
    ∃! σ : D →* flagAutomorphisms m hm, reverseRestriction.comp σ = ρ :=
  lift_unique reverseRestriction reverseRestriction_injective ρ hρ

private theorem map_eq_of_marked {U : Type*} [Group U]
    (P : Subgroup U) (f : MulAut U) (a : MulAut P)
    (h : ∀ x : P, f x.val = (a x).val) : P.map f.toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change f x ∈ P
    rw [h ⟨x,hx⟩]
    exact (a ⟨x,hx⟩).property
  · intro x hx
    refine ⟨(a.symm ⟨x,hx⟩).val, (a.symm ⟨x,hx⟩).property, ?_⟩
    exact (h _).trans (congrArg Subtype.val (a.apply_symm_apply ⟨x,hx⟩))

private theorem markedRestriction_surjective {U : Type*} [Group U]
    (P B Q : Subgroup U) (hBP : B ≤ P) (hBQ : B ≤ Q) (hB : P ⊓ Q = B)
    (hlift : ∀ a : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B Q hBP hBQ)
      (RankTwoAmalgam.ofSubgroups P B Q hBP hBQ), ∃ f : MulAut U,
        (∀ x : P, f x.val = (a.left x).val) ∧
        (∀ x : Q, f x.val = (a.right x).val)) :
    Function.Surjective (markedRestriction P B Q hBP hBQ hB) := by
  intro a
  obtain ⟨f,hl,hr⟩ := hlift a
  let u : (MulAction.stabilizer (MulAut U) P ⊓ MulAction.stabilizer (MulAut U) Q :
      Subgroup (MulAut U)) :=
    ⟨f, map_eq_of_marked _ f a.left hl, map_eq_of_marked _ f a.right hr⟩
  refine ⟨u, ?_⟩
  apply RankTwoAmalgam.Iso.ext
  · ext x : 1; exact Subtype.ext (hl x)
  · ext x : 1
    apply Subtype.ext
    exact (hl ((RankTwoAmalgam.ofSubgroups P B Q hBP hBQ).left x)).trans
      (congrArg Subtype.val (a.left_commutes x))
  · ext x : 1; exact Subtype.ext (hr x)

/-- The accepted simultaneous lift is surjective on the entire marked pair. -/
theorem native_amalgam_automorphism_surjective (hm2 : 1 < m) :
    Function.Surjective (restriction (m := m) (hm := hm)) :=
  markedRestriction_surjective _ _ _ _ _ _ (native_amalgam_automorphism hm2)

private theorem reverseHom_surjective {A B C : Type*} [Group A] [Group B] [Group C]
    (α : RankTwoAmalgam A B C) : Function.Surjective (reverseHom α) := by
  intro a
  exact ⟨a.reverse, reverse_twice a⟩

/-- Simultaneous lifting with both endpoint maps reversed coherently. -/
theorem native_amalgam_automorphism_surjective_reverse (hm2 : 1 < m) :
    Function.Surjective (reverseRestriction (m := m) (hm := hm)) :=
  (reverseHom_surjective (diagram m hm)).comp (native_amalgam_automorphism_surjective hm2)

end CFSG.Quasithin.Chapter5.Section03TrialitySource
