module
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.ExactLift
public import Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.Restriction

/-!
# Unique and coherent exact lifts in both native unitary rows

Native generation gives uniqueness of an ambient lift. The exact lifting
theorem makes restriction from the flag-preserving automorphisms bijective,
including in the reversed orientation. Inverting this restriction gives the
unique homomorphic lift of every amalgam action; a faithful action stays
faithful. All maps use the native projective carriers and whole middles.

Source: the intrinsic realization needed in Aschbacher–Smith 5.3.2, p.659,
with the exact-marking strengthening supplied by the paired-cover proof.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter5.UnitaryNativeLift
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
namespace Four
open ChapterF.GreenBook.LieModels.UnitaryFour
variable (m : ℕ) (hm : 1 ≤ m)

abbrev flagAutomorphisms := NativeAmalgamActions.flagAutomorphisms (pointParabolic m hm) (planeParabolic m hm)

def restriction : flagAutomorphisms m hm →* RankTwoAmalgam.Iso (amalgam m hm) (amalgam m hm) :=
  NativeAmalgamActions.restriction (pointParabolic m hm) (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right) (exact_overlap m hm)

def reverseRestriction : flagAutomorphisms m hm →*
    RankTwoAmalgam.Iso (amalgam m hm).reverse (amalgam m hm).reverse :=
  NativeAmalgamActions.reverseRestriction (pointParabolic m hm) (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right) (exact_overlap m hm)

/-- Restriction is a bijection, with no extension-image premise. -/
theorem restriction_bijective (hmgt : 1 < m) : Function.Bijective (restriction m hm) :=
  ⟨NativeAmalgamActions.restriction_injective (pointParabolic m hm) (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right) (exact_overlap m hm) (parabolics_generate m hm),
   NativeAmalgamActions.restriction_surjective_of_extensions (pointParabolic m hm) (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right) (exact_overlap m hm)
     (native_automorphism m hm hmgt)⟩

/-- The reversed restriction retains the same native flag subgroup. -/
theorem reverseRestriction_bijective (hmgt : 1 < m) :
    Function.Bijective (reverseRestriction m hm) :=
  NativeAmalgamActions.reverseRestriction_bijective (pointParabolic m hm) (planeParabolic m hm) (overlap m hm) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right) (exact_overlap m hm)
    (restriction_bijective m hm hmgt)

/-- There is exactly one native automorphism with the two specified maps. -/
theorem unique_native_automorphism (hmgt : 1 < m) (a : RankTwoAmalgam.Iso (amalgam m hm) (amalgam m hm)) :
    ∃! f : MulAut (ProjectiveGroup m hm),
      (∀ x : pointParabolic m hm, f x.val = (a.left x).val) ∧
      (∀ x : planeParabolic m hm, f x.val = (a.right x).val) := by
  obtain ⟨f, hl, hr⟩ := native_automorphism m hm hmgt a
  refine ⟨f, ⟨hl, hr⟩, ?_⟩
  intro g hg
  exact NativeAmalgamActions.endpoint_ext (pointParabolic m hm) (planeParabolic m hm) (parabolics_generate m hm) g f
    (fun x => (hg.1 x).trans (hl x).symm) (fun x => (hg.2 x).trans (hr x).symm)

/-- The middle equation follows from the literal left compatibility square. -/
theorem native_middle (a : RankTwoAmalgam.Iso (amalgam m hm) (amalgam m hm))
    (f : MulAut (ProjectiveGroup m hm)) (hl : ∀ x : pointParabolic m hm, f x.val = (a.left x).val)
    (x : overlap m hm) : f x.val = (a.middle x).val :=
  (hl ((amalgam m hm).left x)).trans (congrArg Subtype.val (a.left_commutes x))

/-- Exact endpoint lifting with the original two endpoints interchanged. -/
theorem unique_native_automorphism_reverse (hmgt : 1 < m)
    (a : RankTwoAmalgam.Iso (amalgam m hm).reverse (amalgam m hm).reverse) :
    ∃! f : MulAut (ProjectiveGroup m hm),
      (∀ x : planeParabolic m hm, f x.val = (a.left x).val) ∧
      (∀ x : pointParabolic m hm, f x.val = (a.right x).val) := by
  obtain ⟨f, hl, hr⟩ := native_automorphism m hm hmgt a.reverse
  refine ⟨f, ⟨hr, hl⟩, ?_⟩
  intro g hg
  exact NativeAmalgamActions.endpoint_ext (pointParabolic m hm) (planeParabolic m hm) (parabolics_generate m hm) g f
    (fun x => (hg.2 x).trans (hl x).symm) (fun x => (hg.1 x).trans (hr x).symm)

theorem native_middle_reverse
    (a : RankTwoAmalgam.Iso (amalgam m hm).reverse (amalgam m hm).reverse)
    (f : MulAut (ProjectiveGroup m hm)) (hl : ∀ x : planeParabolic m hm, f x.val = (a.left x).val)
    (x : overlap m hm) : f x.val = (a.middle x).val :=
  (hl ((amalgam m hm).reverse.left x)).trans (congrArg Subtype.val (a.left_commutes x))

/-- Every action has a unique coherent lift into native flag automorphisms. -/
theorem unique_action_lift (hmgt : 1 < m) {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso (amalgam m hm) (amalgam m hm)) :
    ∃! σ : A →* flagAutomorphisms m hm, (restriction m hm).comp σ = ρ :=
  NativeAmalgamActions.unique_lift (restriction m hm) (restriction_bijective m hm hmgt) ρ

/-- Coherent lifting in the reversed orientation. -/
theorem unique_action_lift_reverse (hmgt : 1 < m) {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso (amalgam m hm).reverse (amalgam m hm).reverse) :
    ∃! σ : A →* flagAutomorphisms m hm, (reverseRestriction m hm).comp σ = ρ :=
  NativeAmalgamActions.unique_lift (reverseRestriction m hm)
    (reverseRestriction_bijective m hm hmgt) ρ

/-- Faithfulness is retained by the coherent lift. -/
theorem faithful_action_lift (hmgt : 1 < m) {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso (amalgam m hm) (amalgam m hm)) (hρ : Function.Injective ρ) :
    ∃ σ : A →* flagAutomorphisms m hm,
      (restriction m hm).comp σ = ρ ∧ Function.Injective σ := by
  obtain ⟨σ, hσ, _⟩ := unique_action_lift m hm hmgt ρ
  exact ⟨σ, hσ, NativeAmalgamActions.lift_injective _ ρ hρ σ hσ⟩

theorem faithful_action_lift_reverse (hmgt : 1 < m) {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso (amalgam m hm).reverse (amalgam m hm).reverse)
    (hρ : Function.Injective ρ) :
    ∃ σ : A →* flagAutomorphisms m hm,
      (reverseRestriction m hm).comp σ = ρ ∧ Function.Injective σ := by
  obtain ⟨σ, hσ, _⟩ := unique_action_lift_reverse m hm hmgt ρ
  exact ⟨σ, hσ, NativeAmalgamActions.lift_injective _ ρ hρ σ hσ⟩

end Four

namespace Five
variable (U : ChapterF.GreenBook.UnitaryFive.Model 4)

abbrev flagAutomorphisms := NativeAmalgamActions.flagAutomorphisms (U.leftParabolic) (U.rightParabolic)

def restriction : flagAutomorphisms U →* RankTwoAmalgam.Iso U.amalgam U.amalgam :=
  NativeAmalgamActions.restriction (U.leftParabolic) (U.rightParabolic) (U.overlap) inf_le_left inf_le_right rfl

def reverseRestriction : flagAutomorphisms U →*
    RankTwoAmalgam.Iso U.amalgam.reverse U.amalgam.reverse :=
  NativeAmalgamActions.reverseRestriction (U.leftParabolic) (U.rightParabolic) (U.overlap) inf_le_left inf_le_right rfl

/-- Restriction is a bijection, with no extension-image premise. -/
theorem restriction_bijective : Function.Bijective (restriction U) :=
  ⟨NativeAmalgamActions.restriction_injective (U.leftParabolic) (U.rightParabolic) (U.overlap) inf_le_left inf_le_right rfl (parabolics_generate U),
   NativeAmalgamActions.restriction_surjective_of_extensions (U.leftParabolic) (U.rightParabolic) (U.overlap) inf_le_left inf_le_right rfl
     (native_automorphism U)⟩

/-- The reversed restriction retains the same native flag subgroup. -/
theorem reverseRestriction_bijective :
    Function.Bijective (reverseRestriction U) :=
  NativeAmalgamActions.reverseRestriction_bijective (U.leftParabolic) (U.rightParabolic) (U.overlap) inf_le_left inf_le_right rfl
    (restriction_bijective U)

/-- There is exactly one native automorphism with the two specified maps. -/
theorem unique_native_automorphism (a : RankTwoAmalgam.Iso U.amalgam U.amalgam) :
    ∃! f : MulAut (U.Carrier),
      (∀ x : U.leftParabolic, f x.val = (a.left x).val) ∧
      (∀ x : U.rightParabolic, f x.val = (a.right x).val) := by
  obtain ⟨f, hl, hr⟩ := native_automorphism U a
  refine ⟨f, ⟨hl, hr⟩, ?_⟩
  intro g hg
  exact NativeAmalgamActions.endpoint_ext (U.leftParabolic) (U.rightParabolic) (parabolics_generate U) g f
    (fun x => (hg.1 x).trans (hl x).symm) (fun x => (hg.2 x).trans (hr x).symm)

/-- The middle equation follows from the literal left compatibility square. -/
theorem native_middle (a : RankTwoAmalgam.Iso U.amalgam U.amalgam)
    (f : MulAut (U.Carrier)) (hl : ∀ x : U.leftParabolic, f x.val = (a.left x).val)
    (x : U.overlap) : f x.val = (a.middle x).val :=
  (hl (U.amalgam.left x)).trans (congrArg Subtype.val (a.left_commutes x))

/-- Exact endpoint lifting with the original two endpoints interchanged. -/
theorem unique_native_automorphism_reverse
    (a : RankTwoAmalgam.Iso U.amalgam.reverse U.amalgam.reverse) :
    ∃! f : MulAut (U.Carrier),
      (∀ x : U.rightParabolic, f x.val = (a.left x).val) ∧
      (∀ x : U.leftParabolic, f x.val = (a.right x).val) := by
  obtain ⟨f, hl, hr⟩ := native_automorphism U a.reverse
  refine ⟨f, ⟨hr, hl⟩, ?_⟩
  intro g hg
  exact NativeAmalgamActions.endpoint_ext (U.leftParabolic) (U.rightParabolic) (parabolics_generate U) g f
    (fun x => (hg.2 x).trans (hl x).symm) (fun x => (hg.1 x).trans (hr x).symm)

theorem native_middle_reverse
    (a : RankTwoAmalgam.Iso U.amalgam.reverse U.amalgam.reverse)
    (f : MulAut (U.Carrier)) (hl : ∀ x : U.rightParabolic, f x.val = (a.left x).val)
    (x : U.overlap) : f x.val = (a.middle x).val :=
  (hl (U.amalgam.reverse.left x)).trans (congrArg Subtype.val (a.left_commutes x))

/-- Every action has a unique coherent lift into native flag automorphisms. -/
theorem unique_action_lift {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso U.amalgam U.amalgam) :
    ∃! σ : A →* flagAutomorphisms U, (restriction U).comp σ = ρ :=
  NativeAmalgamActions.unique_lift (restriction U) (restriction_bijective U) ρ

/-- Coherent lifting in the reversed orientation. -/
theorem unique_action_lift_reverse {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso U.amalgam.reverse U.amalgam.reverse) :
    ∃! σ : A →* flagAutomorphisms U, (reverseRestriction U).comp σ = ρ :=
  NativeAmalgamActions.unique_lift (reverseRestriction U)
    (reverseRestriction_bijective U) ρ

/-- Faithfulness is retained by the coherent lift. -/
theorem faithful_action_lift {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso U.amalgam U.amalgam) (hρ : Function.Injective ρ) :
    ∃ σ : A →* flagAutomorphisms U,
      (restriction U).comp σ = ρ ∧ Function.Injective σ := by
  obtain ⟨σ, hσ, _⟩ := unique_action_lift U ρ
  exact ⟨σ, hσ, NativeAmalgamActions.lift_injective _ ρ hρ σ hσ⟩

theorem faithful_action_lift_reverse {A : Type*} [Group A]
    (ρ : A →* RankTwoAmalgam.Iso U.amalgam.reverse U.amalgam.reverse)
    (hρ : Function.Injective ρ) :
    ∃ σ : A →* flagAutomorphisms U,
      (reverseRestriction U).comp σ = ρ ∧ Function.Injective σ := by
  obtain ⟨σ, hσ, _⟩ := unique_action_lift_reverse U ρ
  exact ⟨σ, hσ, NativeAmalgamActions.lift_injective _ ρ hρ σ hσ⟩

end Five

end CFSG.Quasithin.Chapter5.UnitaryNativeLift
