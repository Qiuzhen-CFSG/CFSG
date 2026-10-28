module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
public import Mathlib.GroupTheory.PushoutI
/-!
# The actual pushout of a marked rank-two amalgam

Mathlib's group pushout gives a single common completion of every faithful
completion of the same amalgam. Its vertex maps are injective because their
compositions into any given faithful completion are injective. Generation of
the endpoint images gives surjectivity of each canonical lift. The range and
injectivity lemmas retain the original maps needed for coset coverings.

Source: Aschbacher--Smith, F.2.1--2 and F.3.3--4, printed pp.264--265 and 270.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam
universe u v
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R)

def Endpoint : Bool → Type u | false => L | true => R
instance endpointGroup (i : Bool) : Group (Endpoint (L := L) (R := R) i) := by
  cases i
  · exact inferInstanceAs (Group L)
  · exact inferInstanceAs (Group R)

def structureMap : (i : Bool) → B →* Endpoint (L := L) (R := R) i
  | false => α.left
  | true => α.right

abbrev Universal := Monoid.PushoutI α.structureMap
namespace Universal

def left : L →* α.Universal := Monoid.PushoutI.of (φ := α.structureMap) false
def right : R →* α.Universal := Monoid.PushoutI.of (φ := α.structureMap) true

theorem compatible : (left α).comp α.left = (right α).comp α.right := by
  exact (Monoid.PushoutI.of_comp_eq_base (φ := α.structureMap) false).trans
    (Monoid.PushoutI.of_comp_eq_base (φ := α.structureMap) true).symm

theorem generated : (left α).range ⊔ (right α).range = ⊤ := by
  have hh : ∀ x : α.Universal, x ∈ (left α).range ⊔ (right α).range := by
    intro x
    induction x using Monoid.PushoutI.induction_on with
    | of i y =>
      cases i
      · exact (show (left α).range ≤ (left α).range ⊔ (right α).range from le_sup_left) ⟨y, rfl⟩
      · exact (show (right α).range ≤ (left α).range ⊔ (right α).range from le_sup_right) ⟨y, rfl⟩
    | base b =>
      rw [← Monoid.PushoutI.of_apply_eq_base α.structureMap false b]
      exact (show (left α).range ≤ (left α).range ⊔ (right α).range from le_sup_left) ⟨α.left b, rfl⟩
    | mul x y hx hy => exact Subgroup.mul_mem _ hx hy
  exact top_unique (fun x _ => hh x)

variable {G : Type v} [Group G] (c : FaithfulCompletion α (G := G))
def endpointMap : (i : Bool) → Endpoint (L := L) (R := R) i →* G
  | false => c.left
  | true => c.right

def lift : α.Universal →* G :=
  Monoid.PushoutI.lift (endpointMap α c) c.middle (by
    intro i
    cases i
    · rfl
    · exact c.compatible.symm)

@[simp] theorem lift_left (x : L) : lift α c (left α x) = c.left x :=
  Monoid.PushoutI.lift_of (endpointMap α c) c.middle _ (i := false) x
@[simp] theorem lift_right (x : R) : lift α c (right α x) = c.right x :=
  Monoid.PushoutI.lift_of (endpointMap α c) c.middle _ (i := true) x

@[simp] theorem lift_comp_left : (lift α c).comp (left α) = c.left := by
  ext x
  exact lift_left α c x
@[simp] theorem lift_comp_right : (lift α c).comp (right α) = c.right := by
  ext x
  exact lift_right α c x

theorem lift_surjective : Function.Surjective (lift α c) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← c.generated]
  apply sup_le
  · rintro x ⟨a, rfl⟩
    exact ⟨left α a, lift_left α c a⟩
  · rintro x ⟨a, rfl⟩
    exact ⟨right α a, lift_right α c a⟩

def completion : FaithfulCompletion α (G := α.Universal) where
  left := left α
  right := right α
  compatible := compatible α
  left_injective := by
    intro x y h
    apply c.left_injective
    simpa only [lift_left] using congrArg (lift α c) h
  right_injective := by
    intro x y h
    apply c.right_injective
    simpa only [lift_right] using congrArg (lift α c) h
  middle_injective := by
    intro x y h
    apply c.middle_injective
    simpa only [MonoidHom.comp_apply, lift_left] using congrArg (lift α c) h
  generated := generated α

@[simp] theorem map_left_range : (left α).range.map (lift α c) = c.left.range := by
  rw [← MonoidHom.range_comp, lift_comp_left]
@[simp] theorem map_right_range : (right α).range.map (lift α c) = c.right.range := by
  rw [← MonoidHom.range_comp, lift_comp_right]
@[simp] theorem map_middle_range :
    ((left α).comp α.left).range.map (lift α c) = c.middle.range := by
  rw [← MonoidHom.range_comp, ← MonoidHom.comp_assoc, lift_comp_left]

theorem injective_on_left : Function.Injective (fun x : (left α).range => lift α c x) := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ h
  have he : x = y := c.left_injective (by simpa only [lift_left] using h)
  subst y
  rfl

theorem injective_on_right : Function.Injective (fun x : (right α).range => lift α c x) := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ h
  have he : x = y := c.right_injective (by simpa only [lift_right] using h)
  subst y
  rfl
end Universal
end Theory.GroupTheory.RankTwoAmalgam
