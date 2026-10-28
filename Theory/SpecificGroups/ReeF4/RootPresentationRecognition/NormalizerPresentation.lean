module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.WeylPresentation
public import Theory.SpecificGroups.ReeF4.SmallCompletion.TorusAction
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities.Geometry
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# A faithful full torus--Weyl presentation for every Ree parameter

The abstract sixteen-element dihedral group acts on the entire native fixed
torus through the literal orbit words. Its semidirect product is characterized
by the torus laws, the two involution relations, the mixed eighth-power
relation, and the two torus conjugation equations. Evaluation is constructed
from those equations. The native sixteen Weyl matrices and their disjointness
from the full torus prove its kernel trivial; the native normalizer
factorization proves that its range is the entire N.

This includes m = 0 and does not use simplicity, perfectness, or a supplied
model homomorphism. It proves the normalizer part of the global presentation;
collection involving signed root factors remains to be proved.
Source: GLS3 2.3.2--5, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.NormalizerPresentation
open Subgroup LargeLocalSeeds Parabolics SectionGeometry.BNPair Parabolics.Binary.FixedGeometry
open CentralCovers.OddPrimary.Order WeylPresentation

def side : Bool → Side
  | false => .linear
  | true => .suzuki

theorem weyl_mixed (m : ℕ) :
    (weylLift m (side false) * weylLift m (side true))^8 = 1 :=
  SmallCompletion.reflection_product_eight m

/-- Evaluation of the two literal Weyl words in the full model. -/
def weyl (m : ℕ) : Weyl →* Model m :=
  WeylPresentation.lift (fun s => weylLift m (side s)) (fun s => weylLift_sq m (side s))
    (weyl_mixed m)

@[simp] theorem weyl_simple (m : ℕ) (s : Bool) : weyl m (simple s) = weylLift m (side s) :=
  lift_simple _ _ _ s

theorem weyl_range (m : ℕ) : (weyl m).range = weylSubgroup m := by
  rw [weyl, lift_range]
  congr 1
  ext x
  constructor
  · rintro ⟨s,rfl⟩; exact ⟨side s,rfl⟩
  · rintro ⟨s,rfl⟩
    cases s
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩

/-- The native sixteen Weyl matrices prove the literal evaluation faithful. -/
theorem weyl_injective (m : ℕ) : Function.Injective (weyl m) := by
  have hc : Nat.card (weyl m).range = Nat.card Weyl := by
    rw [weyl_range, ← Nat.card_congr (CellCardinalities.weylEquiv m), DihedralGroup.nat_card]
    norm_num
  have hb := (weyl m).rangeRestrict_surjective.bijective_of_nat_card_le (le_of_eq hc.symm)
  intro x y he
  exact hb.injective (Subtype.ext he)

theorem weyl_normalizes (m : ℕ) (w : Weyl) :
    weyl m w ∈ normalizer (fixedTorus m : Set (Model m)) := by
  have h : (weyl m).range ≤ normalizer (fixedTorus m : Set (Model m)) := by
    rw [weyl_range]
    apply (closure_le _).mpr
    rintro _ ⟨s,rfl⟩
    exact SmallCompletion.reflection_mem_normalizer_fixedTorus m s
  exact h ⟨w,rfl⟩

/-- Conjugation on the entire native two-dimensional fixed torus. -/
def action (m : ℕ) : Weyl →* MulAut (fixedTorus m) :=
  (fixedTorus m).normalizerMonoidHom.comp ((weyl m).codRestrict _ (weyl_normalizes m))

@[simp] theorem action_apply (m : ℕ) (w : Weyl) (t : fixedTorus m) :
    (action m w t : Model m) = weyl m w * t * (weyl m w)⁻¹ := rfl

@[simp] theorem action_simple (m : ℕ) (s : Bool) :
    action m (simple s) = SmallCompletion.torusReflection m (side s) := by
  apply MulEquiv.ext
  intro t
  apply Subtype.ext
  change weyl m (simple s) * t * (weyl m (simple s))⁻¹ = _
  rw [weyl_simple]
  rfl

/-- The torus–Weyl presentation, with its actual native action. -/
abbrev Presentation (m : ℕ) := (fixedTorus m) ⋊[action m] Weyl

variable {G : Type*} [Group G]

/-- The torus laws, two involutions, literal mixed relation, and the two torus
conjugation equations construct the unique homomorphism from the normalizer. -/
def realize (m : ℕ) (h : fixedTorus m →* G) (n : Bool → G)
    (hsq : ∀ s, n s ^ 2 = 1) (hmix : (n false * n true)^8 = 1)
    (ha : ∀ s t, h (action m (simple s) t) = n s * h t * (n s)⁻¹) :
    Presentation m →* G :=
  SemidirectProduct.lift h (WeylPresentation.lift n hsq hmix)
    (action_compatible (action m) h (WeylPresentation.lift n hsq hmix)
      (by simpa only [lift_simple] using ha))

@[simp] theorem realize_torus (m : ℕ) (h : fixedTorus m →* G) (n : Bool → G)
    (hsq : ∀ s, n s ^ 2 = 1) (hmix : (n false * n true)^8 = 1)
    (ha : ∀ s t, h (action m (simple s) t) = n s * h t * (n s)⁻¹) (t : fixedTorus m) :
    realize m h n hsq hmix ha (SemidirectProduct.inl t) = h t :=
  SemidirectProduct.lift_inl ..

@[simp] theorem realize_simple (m : ℕ) (h : fixedTorus m →* G) (n : Bool → G)
    (hsq : ∀ s, n s ^ 2 = 1) (hmix : (n false * n true)^8 = 1)
    (ha : ∀ s t, h (action m (simple s) t) = n s * h t * (n s)⁻¹) (s : Bool) :
    realize m h n hsq hmix ha (SemidirectProduct.inr (simple s)) = n s := by
  rw [realize, SemidirectProduct.lift_inr, lift_simple]

/-- The displayed torus and two reflection generators determine every map. -/
theorem hom_ext {m : ℕ} {f g : Presentation m →* G}
    (ht : ∀ t, f (SemidirectProduct.inl t) = g (SemidirectProduct.inl t))
    (hn : ∀ s, f (SemidirectProduct.inr (simple s)) = g (SemidirectProduct.inr (simple s))) :
    f = g := by
  apply SemidirectProduct.hom_ext
  · exact MonoidHom.ext ht
  · exact WeylPresentation.hom_ext hn

def nativeEval (m : ℕ) : Presentation m →* Model m :=
  SemidirectProduct.lift (fixedTorus m).subtype (weyl m) (fun _ => rfl)

@[simp] theorem nativeEval_apply (m : ℕ) (a : Presentation m) :
    nativeEval m a = (a.left : Model m) * weyl m a.right := rfl

@[simp] theorem nativeEval_torus (m : ℕ) (t : fixedTorus m) :
    nativeEval m (SemidirectProduct.inl t) = t := SemidirectProduct.lift_inl ..

@[simp] theorem nativeEval_weyl (m : ℕ) (w : Weyl) :
    nativeEval m (SemidirectProduct.inr w) = weyl m w := SemidirectProduct.lift_inr ..

theorem weyl_le_normalizerWords (m : ℕ) : weylSubgroup m ≤ normalizerWords m := by
  apply (closure_le _).mpr
  rintro _ ⟨s,rfl⟩
  exact weylLift_mem_normalizerWords m s

/-- The constructed evaluation reaches exactly the full native normalizer. -/
theorem nativeEval_range (m : ℕ) : (nativeEval m).range = normalizerWords m := by
  apply le_antisymm
  · rintro x ⟨a,rfl⟩
    exact mul_mem (fixedTorus_le_normalizerWords m a.left.property)
      (weyl_le_normalizerWords m (by rw [← weyl_range]; exact ⟨a.right,rfl⟩))
  · intro x hx
    obtain ⟨t,ht,w,hw,rfl⟩ := exists_torus_weyl m hx
    rw [← weyl_range] at hw
    obtain ⟨v,rfl⟩ := hw
    exact ⟨⟨⟨t,ht⟩,v⟩,rfl⟩

/-- No central-kernel argument is needed: native torus/Weyl separation kills
both factors of a word evaluating to one, uniformly including m = 0. -/
theorem nativeEval_injective (m : ℕ) : Function.Injective (nativeEval m) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hw : weyl m a.right ∈ weylSubgroup m := by
    rw [← weyl_range]; exact ⟨a.right,rfl⟩
  have ht : (a.left : Model m) = 1 :=
    (fixedTorus_disjoint_weylSubgroup m).le_bot ⟨a.left.property, by
      rw [show (a.left : Model m) = (weyl m a.right)⁻¹ from eq_inv_of_mul_eq_one_left ha]
      exact (weylSubgroup m).inv_mem hw⟩
  have hw1 : weyl m a.right = 1 := by
    change (a.left : Model m) * weyl m a.right = 1 at ha
    simpa only [ht,one_mul] using ha
  exact SemidirectProduct.ext (Subtype.ext ht)
    (weyl_injective m (hw1.trans (map_one _).symm))

def nativeEquiv (m : ℕ) : Presentation m ≃* normalizerWords m :=
  (MonoidHom.ofInjective (nativeEval_injective m)).trans (MulEquiv.subgroupCongr (nativeEval_range m))

@[simp] theorem nativeEquiv_apply (m : ℕ) (a : Presentation m) :
    (nativeEquiv m a : Model m) = (a.left : Model m) * weyl m a.right := rfl

end ReeF4.RootPresentationRecognition.NormalizerPresentation
