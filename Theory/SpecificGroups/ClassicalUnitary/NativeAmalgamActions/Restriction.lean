module
public import Theory.GroupTheory.Amalgam.NormalBaseAction
public import Theory.GroupTheory.Amalgam.Reversal
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Restriction to a native marked pair and coherent action lifting

Automorphisms preserving both endpoints restrict to the entire subgroup
amalgam. The middle may be a separately named subgroup equal to the
intersection, and its original inclusion maps are retained. Generation
makes restriction injective. Surjectivity, when supplied by a native lifting
theorem, gives unique homomorphic lifts of arbitrary actions, in both
orientations. Conjugation by the whole middle has its literal native lift.

This is the intrinsic restriction mechanism used in Aschbacher–Smith
F.2.8 and 5.3.2; no classification or extension-existence theorem is assumed
in these elementary transport results.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] (P Q : Subgroup G)

def flagAutomorphisms : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) P ⊓ MulAction.stabilizer (MulAut G) Q

theorem flagAutomorphisms_mem (a : MulAut G) :
    a ∈ flagAutomorphisms P Q ↔ P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q :=
  Iff.rfl

/-- Agreement on generating endpoints determines the ambient automorphism. -/
theorem endpoint_ext (hgen : P ⊔ Q = ⊤) (f g : MulAut G)
    (hl : ∀ x : P, f x.val = g x.val) (hr : ∀ x : Q, f x.val = g x.val) : f = g := by
  have hP : P ≤ f.toMonoidHom.eqLocus g.toMonoidHom := fun x hx => hl ⟨x, hx⟩
  have hQ : Q ≤ f.toMonoidHom.eqLocus g.toMonoidHom := fun x hx => hr ⟨x, hx⟩
  have hh := hgen ▸ sup_le hP hQ
  ext x
  exact hh (show x ∈ (⊤ : Subgroup G) from trivial)

variable (D : Subgroup G) (hP : D ≤ P) (hQ : D ≤ Q) (hD : P ⊓ Q = D)

/-- Restrict to the literal marked middle, not a substituted Sylow subgroup. -/
def restriction : flagAutomorphisms P Q →*
    RankTwoAmalgam.Iso (.ofSubgroups P D Q hP hQ) (.ofSubgroups P D Q hP hQ) where
  toFun a :=
    { left := (a.val.subgroupMap P).trans (MulEquiv.subgroupCongr a.property.1)
      middle := (a.val.subgroupMap D).trans (MulEquiv.subgroupCongr (by
        rw [← hD, Subgroup.map_inf _ _ _ a.val.injective]
        exact congrArg₂ (· ⊓ ·) a.property.1 a.property.2))
      right := (a.val.subgroupMap Q).trans (MulEquiv.subgroupCongr a.property.2)
      left_commutes _ := rfl
      right_commutes _ := rfl }
  map_one' := by apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl
  map_mul' _ _ := by apply RankTwoAmalgam.Iso.ext <;> ext x <;> rfl

@[simp] theorem restriction_left (a : flagAutomorphisms P Q) (x : P) :
    ((restriction P Q D hP hQ hD a).left x).val = a.val x.val := rfl

@[simp] theorem restriction_middle (a : flagAutomorphisms P Q) (x : D) :
    ((restriction P Q D hP hQ hD a).middle x).val = a.val x.val := rfl

@[simp] theorem restriction_right (a : flagAutomorphisms P Q) (x : Q) :
    ((restriction P Q D hP hQ hD a).right x).val = a.val x.val := rfl

theorem restriction_injective (hgen : P ⊔ Q = ⊤) :
    Function.Injective (restriction P Q D hP hQ hD) := by
  intro a b he
  apply Subtype.ext
  apply endpoint_ext P Q hgen a.val b.val
  · intro x
    exact congrArg (fun z => (z.left x).val) he
  · intro x
    exact congrArg (fun z => (z.right x).val) he

def reverseRestriction : flagAutomorphisms P Q →*
    RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P D Q hP hQ).reverse
      (RankTwoAmalgam.ofSubgroups P D Q hP hQ).reverse where
  toFun a := (restriction P Q D hP hQ hD a).reverse
  map_one' := rfl
  map_mul' _ _ := rfl

theorem reverseRestriction_injective (hgen : P ⊔ Q = ⊤) :
    Function.Injective (reverseRestriction P Q D hP hQ hD) := by
  intro a b he
  apply restriction_injective P Q D hP hQ hD hgen
  exact congrArg (fun e => e.reverse) he

private theorem map_eq_of_marked (P : Subgroup G) (f : MulAut G) (a : MulAut P)
    (h : ∀ x : P, f x.val = (a x).val) : P.map f.toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change f x ∈ P
    rw [h ⟨x, hx⟩]
    exact (a ⟨x, hx⟩).property
  · intro x hx
    refine ⟨(a.symm ⟨x, hx⟩).val, (a.symm ⟨x, hx⟩).property, ?_⟩
    exact (h _).trans (congrArg Subtype.val (a.apply_symm_apply ⟨x, hx⟩))

/-- Exact endpoint extension supplies surjectivity on the whole marked pair. -/
theorem restriction_surjective_of_extensions
    (hext : ∀ a : RankTwoAmalgam.Iso (.ofSubgroups P D Q hP hQ)
        (.ofSubgroups P D Q hP hQ), ∃ f : MulAut G,
        (∀ x : P, f x.val = (a.left x).val) ∧
        (∀ x : Q, f x.val = (a.right x).val)) :
    Function.Surjective (restriction P Q D hP hQ hD) := by
  intro a
  obtain ⟨f, hl, hr⟩ := hext a
  let u : flagAutomorphisms P Q :=
    ⟨f, map_eq_of_marked P f a.left hl, map_eq_of_marked Q f a.right hr⟩
  refine ⟨u, ?_⟩
  apply RankTwoAmalgam.Iso.ext
  · ext x : 1
    exact Subtype.ext (hl x)
  · ext x : 1
    apply Subtype.ext
    exact (hl ((RankTwoAmalgam.ofSubgroups P D Q hP hQ).left x)).trans
      (congrArg Subtype.val (a.left_commutes x))
  · ext x : 1
    exact Subtype.ext (hr x)

theorem reverseRestriction_bijective
    (hr : Function.Bijective (restriction P Q D hP hQ hD)) :
    Function.Bijective (reverseRestriction P Q D hP hQ hD) := by
  constructor
  · intro a b he
    exact hr.1 (congrArg (fun e => e.reverse) he)
  · intro a
    obtain ⟨f, hf⟩ := hr.2 a.reverse
    exact ⟨f, congrArg (fun e => e.reverse) hf⟩

/-- The full native middle, including its odd part, acts by actual conjugation. -/
def innerMiddle : D →* flagAutomorphisms P Q :=
  (MulAut.conj.comp D.subtype).codRestrict _ (fun b =>
    ⟨mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer (hP b.property)),
     mem_normalizer_iff_map_conj_eq.mp (Q.le_normalizer (hQ b.property))⟩)

@[simp] theorem innerMiddle_val (b : D) :
    (innerMiddle P Q D hP hQ b).val = MulAut.conj b.val := rfl

section Coherence
variable {A B C : Type*} [Group A] [Group B] [Group C]

/-- A bijective restriction has a unique homomorphic lift of every action. -/
theorem unique_lift (r : A →* B) (hr : Function.Bijective r) (ρ : C →* B) :
    ∃! σ : C →* A, r.comp σ = ρ := by
  let e := MulEquiv.ofBijective r hr
  refine ⟨e.symm.toMonoidHom.comp ρ, ?_, ?_⟩
  · ext x
    exact e.apply_symm_apply (ρ x)
  · intro σ hσ
    ext x
    apply hr.1
    exact (DFunLike.congr_fun hσ x).trans (e.apply_symm_apply (ρ x)).symm

theorem lift_injective (r : A →* B) (ρ : C →* B) (hρ : Function.Injective ρ)
    (σ : C →* A) (hσ : r.comp σ = ρ) : Function.Injective σ := by
  intro x y he
  apply hρ
  rw [← hσ]
  exact congrArg r he

end Coherence
end Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions
