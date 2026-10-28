module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.RankOne
public import Mathlib.GroupTheory.PresentedGroup

/-!
# A rank-one presentation from root, full torus and Gauss equations

The abstract alphabet has a root-group parameter, a torus parameter and one
reflection. The local multiplication, conjugation and Gauss equations give
two-cell collection by closure induction. Evaluation is constructed from
these equations. Its kernel is trivial whenever the two local parameter maps
are faithful with disjoint ranges and a subgroup contains these ranges but
misses the reflection. These are local geometric conditions, not an assumed
presentation kernel or global model homomorphism.

This is the rank-one part of the twisted Bruhat reduction in Steinberg §11,
Lemmas 62--64, `refs/KGroup/GLS3/Chapter2St1.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.LocalPresentation
open Subgroup
variable {A T : Type*} [Group A] [Group T]

/-- Finite local coefficients; the Gauss relation is used only away from one. -/
structure Table (A T : Type*) where
  action : T → A → A
  torusReflection : T → T
  gaussLeft : A → A
  gaussTorus : A → T
  gaussRight : A → A

variable (d : Table A T)

/-- The explicit local relations in a realization. -/
structure Equations {G : Type*} [Group G] (x : A →* G) (h : T →* G) (n : G) : Prop where
  involution : n*n = 1
  torus_root : ∀ t a, h t*x a*(h t)⁻¹ = x (d.action t a)
  weyl_torus : ∀ t, n*h t*n = h (d.torusReflection t)
  gauss : ∀ a, a ≠ 1 → n*x a*n = x (d.gaussLeft a)*h (d.gaussTorus a)*n*x (d.gaussRight a)

inductive Letter (A T : Type*)
  | root (a : A)
  | torus (t : T)
  | reflection

def freeRoot (a : A) : FreeGroup (Letter A T) := FreeGroup.of (.root a)
def freeTorus (t : T) : FreeGroup (Letter A T) := FreeGroup.of (.torus t)
def freeReflection : FreeGroup (Letter A T) := FreeGroup.of .reflection

/-- Only root, torus, reflection and local Gauss relations are imposed. -/
inductive Relator : FreeGroup (Letter A T) → Prop
  | root_one : Relator (freeRoot (1 : A))
  | root_mul (a b : A) : Relator (freeRoot a*freeRoot b*(freeRoot (a*b) : FreeGroup (Letter A T))⁻¹)
  | torus_one : Relator (freeTorus (1 : T))
  | torus_mul (a b : T) : Relator (freeTorus a*freeTorus b*(freeTorus (a*b) : FreeGroup (Letter A T))⁻¹)
  | involution : Relator (freeReflection*freeReflection)
  | torus_root (t : T) (a : A) :
      Relator (freeTorus t*freeRoot a*(freeTorus t)⁻¹*(freeRoot (d.action t a))⁻¹)
  | weyl_torus (t : T) : Relator (freeReflection*freeTorus t*freeReflection*(freeTorus (d.torusReflection t))⁻¹)
  | gauss (a : A) (ha : a ≠ 1) :
      Relator (freeReflection*freeRoot a*freeReflection*(freeRoot (d.gaussLeft a)*freeTorus (d.gaussTorus a)*freeReflection*freeRoot (d.gaussRight a))⁻¹)

abbrev Presentation := PresentedGroup {w | Relator d w}

def root (a : A) : Presentation d := PresentedGroup.of (.root a)
def torus (t : T) : Presentation d := PresentedGroup.of (.torus t)
def reflection : Presentation d := PresentedGroup.of .reflection

@[simp] theorem root_one : root d 1 = 1 := PresentedGroup.one_of_mem (Relator.root_one)
@[simp] theorem torus_one : torus d 1 = 1 := PresentedGroup.one_of_mem (Relator.torus_one)

theorem root_mul (a b : A) : root d a*root d b = root d (a*b) := by
  apply mul_inv_eq_one.mp
  exact PresentedGroup.one_of_mem (Relator.root_mul a b)

theorem torus_mul (a b : T) : torus d a*torus d b = torus d (a*b) := by
  apply mul_inv_eq_one.mp
  exact PresentedGroup.one_of_mem (Relator.torus_mul a b)

def rootHom : A →* Presentation d where
  toFun := root d
  map_one' := root_one d
  map_mul' a b := (root_mul d a b).symm

def torusHom : T →* Presentation d where
  toFun := torus d
  map_one' := torus_one d
  map_mul' a b := (torus_mul d a b).symm

theorem generator_equations : Equations d (rootHom d) (torusHom d) (reflection d) where
  involution := PresentedGroup.one_of_mem (Relator.involution)
  torus_root t a := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.torus_root t a))
  weyl_torus t := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.weyl_torus t))
  gauss a ha := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.gauss a ha))

variable {G : Type*} [Group G] {x : A →* G} {h : T →* G} {n : G}

def assignment (x : A →* G) (h : T →* G) (n : G) : Letter A T → G
  | .root a => x a
  | .torus t => h t
  | .reflection => n

theorem relator_eval (E : Equations d x h n) {w : FreeGroup (Letter A T)}
    (hw : Relator d w) : FreeGroup.lift (assignment x h n) w = 1 := by
  cases hw with
  | root_one => simp [freeRoot, assignment]
  | root_mul a b => simp [freeRoot, assignment]
  | torus_one => simp [freeTorus, assignment]
  | torus_mul a b => simp [freeTorus, assignment]
  | involution => simpa only [freeReflection, map_mul, FreeGroup.lift_apply_of, assignment] using E.involution
  | torus_root t a =>
      simpa only [freeRoot, freeTorus, map_mul, map_inv, FreeGroup.lift_apply_of, assignment,
        mul_inv_eq_one] using E.torus_root t a
  | weyl_torus t =>
      simpa only [freeReflection, freeTorus, map_mul, map_inv, FreeGroup.lift_apply_of, assignment,
        mul_inv_eq_one] using E.weyl_torus t
  | gauss a ha =>
      simpa only [freeReflection, freeRoot, freeTorus, map_mul, map_inv, FreeGroup.lift_apply_of, assignment,
        mul_inv_eq_one] using E.gauss a ha

/-- Evaluation is constructed from the finite local equations. -/
def eval (E : Equations d x h n) : Presentation d →* G :=
  PresentedGroup.toGroup (fun _ hw => relator_eval d E hw)

@[simp] theorem eval_root (E : Equations d x h n) (a : A) : eval d E (root d a) = x a :=
  PresentedGroup.toGroup.of _
@[simp] theorem eval_torus (E : Equations d x h n) (t : T) : eval d E (torus d t) = h t :=
  PresentedGroup.toGroup.of _
@[simp] theorem eval_reflection (E : Equations d x h n) : eval d E (reflection d) = n :=
  PresentedGroup.toGroup.of _

theorem Equations.torus_normalizes (E : Equations d x h n) : h.range ≤ normalizer x.range := by
  rw [le_normalizer_iff]
  rintro _ ⟨t,rfl⟩ _ ⟨a,rfl⟩
  exact ⟨d.action t a,E.torus_root t a |>.symm⟩

theorem Equations.reflection_normalizes (E : Equations d x h n) : n ∈ normalizer h.range := by
  have hi : n⁻¹ = n := inv_eq_of_mul_eq_one_right E.involution
  have hforward {t : G} (ht : t ∈ h.range) : n*t*n ∈ h.range := by
    obtain ⟨a,rfl⟩ := ht
    exact ⟨d.torusReflection a,(E.weyl_torus a).symm⟩
  rw [mem_normalizer_iff]
  intro t
  rw [hi]
  refine ⟨hforward, fun ht => ?_⟩
  have hh := hforward ht
  simpa only [mul_assoc, ← mul_assoc n n, E.involution, one_mul, mul_one] using hh

/-- Abstract local words reduce to two cells directly from the defining relators. -/
theorem normalForm (g : Presentation d) :
    (∃ a t, g = root d a*torus d t) ∨
      ∃ a t b, g = root d a*torus d t*reflection d*root d b := by
  let E := generator_equations d
  have hg : g ∈ (rootHom d).range ⊔ (torusHom d).range ⊔ zpowers (reflection d) := by
    apply PresentedGroup.generated_by _ _ ?_ g
    intro l
    cases l with
    | root a => exact mem_sup_left (mem_sup_left (show root d a ∈ (rootHom d).range from ⟨a,rfl⟩))
    | torus t => exact mem_sup_left (mem_sup_right (show torus d t ∈ (torusHom d).range from ⟨t,rfl⟩))
    | reflection => exact mem_sup_right (mem_zpowers _)
  have hn := RankOne.normalForm_of_mem (rootHom d).range (torusHom d).range
    (reflection d) (E.torus_normalizes d) (E.reflection_normalizes d) E.involution
    (fun u hu hu1 => by
      obtain ⟨a,rfl⟩ := hu
      have ha : a ≠ 1 := by intro ha; exact hu1 (by rw [ha,map_one])
      exact ⟨root d (d.gaussLeft a),⟨_,rfl⟩,torus d (d.gaussTorus a),⟨_,rfl⟩,
        root d (d.gaussRight a),⟨_,rfl⟩,E.gauss a ha⟩) hg
  rcases hn with ⟨u,⟨a,rfl⟩,v,⟨t,rfl⟩,he⟩ | ⟨u,⟨a,rfl⟩,v,⟨t,rfl⟩,w,⟨b,rfl⟩,he⟩
  · exact Or.inl ⟨a,t,he⟩
  · exact Or.inr ⟨a,t,b,he⟩

/-- Local injectivity and separation prove the constructed evaluation kernel trivial. -/
theorem eval_injective (E : Equations d x h n)
    (hx : Function.Injective x) (hh : Function.Injective h)
    (hd : Disjoint x.range h.range) (B : Subgroup G)
    (hxB : x.range ≤ B) (hhB : h.range ≤ B) (hnB : n ∉ B) :
    Function.Injective (eval d E) := by
  apply (eval d E).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro g hg
  have he : eval d E g = 1 := hg
  change g = 1
  rcases normalForm d g with ⟨a,t,rfl⟩ | ⟨a,t,b,rfl⟩
  · rw [map_mul,eval_root,eval_torus] at he
    have hx1 : x a = 1 := Subgroup.disjoint_def.mp hd
      (show x a ∈ x.range from ⟨a,rfl⟩)
      (show x a ∈ h.range from (eq_inv_of_mul_eq_one_left he) ▸ inv_mem (show h t ∈ h.range from ⟨t,rfl⟩))
    have ht1 : h t = 1 := by simpa only [hx1,one_mul] using he
    have ha : a = 1 := hx (hx1.trans x.map_one.symm)
    have ht : t = 1 := hh (ht1.trans h.map_one.symm)
    rw [ha,ht,root_one,torus_one,mul_one]
  · rw [map_mul,map_mul,map_mul,eval_root,eval_torus,eval_reflection,eval_root] at he
    have hn : n = (x a*h t)⁻¹*(x b)⁻¹ := by
      have he' := congrArg (fun z => (x a*h t)⁻¹*z*(x b)⁻¹) he
      simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one] using he'
    exact (hnB (hn ▸ B.mul_mem (B.inv_mem (B.mul_mem (hxB ⟨a,rfl⟩) (hhB ⟨t,rfl⟩)))
      (B.inv_mem (hxB ⟨b,rfl⟩)))).elim

/-- The constructed evaluation covers exactly the subgroup generated by the
root, the whole specified torus and the literal reflection. -/
theorem eval_range (E : Equations d x h n) :
    (eval d E).range = x.range ⊔ h.range ⊔ zpowers n := by
  apply le_antisymm
  · rintro y ⟨g,rfl⟩
    apply PresentedGroup.generated_by _
      ((x.range ⊔ h.range ⊔ zpowers n).comap (eval d E)) ?_ g
    intro l
    cases l with
    | root a =>
        change eval d E (root d a) ∈ x.range ⊔ h.range ⊔ zpowers n
        rw [eval_root]
        exact mem_sup_left (mem_sup_left (show x a ∈ x.range from ⟨a,rfl⟩))
    | torus t =>
        change eval d E (torus d t) ∈ x.range ⊔ h.range ⊔ zpowers n
        rw [eval_torus]
        exact mem_sup_left (mem_sup_right (show h t ∈ h.range from ⟨t,rfl⟩))
    | reflection =>
        change eval d E (reflection d) ∈ x.range ⊔ h.range ⊔ zpowers n
        rw [eval_reflection]
        exact mem_sup_right (mem_zpowers _)
  · refine sup_le (sup_le ?_ ?_) (zpowers_le.mpr ?_)
    · rintro y ⟨a,rfl⟩
      exact ⟨root d a,eval_root d E a⟩
    · rintro y ⟨t,rfl⟩
      exact ⟨torus d t,eval_torus d E t⟩
    · exact ⟨reflection d,eval_reflection d E⟩

/-- Local realization as an actual subgroup; both surjectivity and the kernel
are proved from the local equations and local geometric separation. -/
def realization (E : Equations d x h n)
    (hx : Function.Injective x) (hh : Function.Injective h)
    (hd : Disjoint x.range h.range) (B : Subgroup G)
    (hxB : x.range ≤ B) (hhB : h.range ≤ B) (hnB : n ∉ B) :
    Presentation d ≃* (x.range ⊔ h.range ⊔ zpowers n : Subgroup G) :=
  (MulEquiv.ofBijective (eval d E).rangeRestrict ⟨
    fun _ _ he => eval_injective d E hx hh hd B hxB hhB hnB (congrArg Subtype.val he),
    (eval d E).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (eval_range d E))

@[simp] theorem realization_apply (E : Equations d x h n)
    (hx : Function.Injective x) (hh : Function.Injective h)
    (hd : Disjoint x.range h.range) (B : Subgroup G)
    (hxB : x.range ≤ B) (hhB : h.range ≤ B) (hnB : n ∉ B) (g : Presentation d) :
    (realization d E hx hh hd B hxB hhB hnB g : G) = eval d E g := rfl

end ReeF4.RootPresentationRecognition.LocalPresentation
