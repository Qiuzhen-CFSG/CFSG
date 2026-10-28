module
public import Theory.GroupTheory.Amalgam.AutomorphismTransport
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Split extensions of marked rank-two amalgams

An action by compatible automorphisms gives three semidirect products whose
inclusion maps still commute. A marked isomorphism transports the whole action,
including its restriction to the middle. For normalized disjoint subgroups,
multiplication identifies these semidirect products with the actual joins.

The application is the cubic extension in Aschbacher--Smith 14.2.18, printed
p.987. This construction retains both squares; it does not assert that the
action extends to any prescribed ambient completion (Definition F.4.3).
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B R A : Type*} [Group L] [Group B] [Group R] [Group A]
variable {α : RankTwoAmalgam L B R}

def leftAction (a : A →* Iso α α) : A →* MulAut L where
  toFun x := (a x).left
  map_one' := by rw [map_one, Iso.one_left]
  map_mul' x y := by rw [map_mul, Iso.mul_left]

def middleAction (a : A →* Iso α α) : A →* MulAut B where
  toFun x := (a x).middle
  map_one' := by rw [map_one, Iso.one_middle]
  map_mul' x y := by rw [map_mul, Iso.mul_middle]

def rightAction (a : A →* Iso α α) : A →* MulAut R where
  toFun x := (a x).right
  map_one' := by rw [map_one, Iso.one_right]
  map_mul' x y := by rw [map_mul, Iso.mul_right]

def semidirect (a : A →* Iso α α) :
    RankTwoAmalgam (L ⋊[leftAction a] A) (B ⋊[middleAction a] A)
      (R ⋊[rightAction a] A) where
  left := SemidirectProduct.map α.left (MonoidHom.id A)
    (fun x => by ext b; exact (a x).left_commutes b |>.symm)
  right := SemidirectProduct.map α.right (MonoidHom.id A)
    (fun x => by ext b; exact (a x).right_commutes b |>.symm)

variable {L' B' R' : Type*} [Group L'] [Group B'] [Group R']
variable {β : RankTwoAmalgam L' B' R'}

def semidirectIso (e : Iso α β) (a : A →* Iso α α) :
    Iso (semidirect a) (semidirect ((automorphismConjEquiv e).toMonoidHom.comp a)) where
  left := SemidirectProduct.congr e.left (MulEquiv.refl A)
    (fun x => by ext l; exact (congrArg (fun z => e.left ((a x).left z))
      (e.left.symm_apply_apply l)).symm)
  middle := SemidirectProduct.congr e.middle (MulEquiv.refl A)
    (fun x => by ext b; exact (congrArg (fun z => e.middle ((a x).middle z))
      (e.middle.symm_apply_apply b)).symm)
  right := SemidirectProduct.congr e.right (MulEquiv.refl A)
    (fun x => by ext r; exact (congrArg (fun z => e.right ((a x).right z))
      (e.right.symm_apply_apply r)).symm)
  left_commutes b := by
    apply SemidirectProduct.ext
    · exact e.left_commutes b.left
    · rfl
  right_commutes b := by
    apply SemidirectProduct.ext
    · exact e.right_commutes b.left
    · rfl

variable {G : Type*} [Group G]

def conjugationAction (H P A : Subgroup G)
    (hH : A ≤ normalizer (H : Set G)) (hP : A ≤ normalizer (P : Set G)) :
    A →* Iso (ofSubgroups H (H ⊓ P) P inf_le_left inf_le_right)
      (ofSubgroups H (H ⊓ P) P inf_le_left inf_le_right) where
  toFun x :=
    { left := H.normalizerMonoidHom (inclusion hH x)
      middle := (H ⊓ P).normalizerMonoidHom
        (inclusion ((le_inf hH hP).trans inf_normalizer_le_normalizer_inf) x)
      right := P.normalizerMonoidHom (inclusion hP x)
      left_commutes _ := rfl
      right_commutes _ := rfl }
  map_one' := by
    apply Iso.ext <;> apply MulEquiv.ext <;> intro x <;> apply Subtype.ext
    all_goals change (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G); simp
  map_mul' x y := by
    apply Iso.ext <;> apply MulEquiv.ext <;> intro z <;> apply Subtype.ext
    all_goals
      change ((x : G) * y) * (z : G) * ((x : G) * y)⁻¹ =
        (x : G) * ((y : G) * z * (y : G)⁻¹) * (x : G)⁻¹
      simp only [mul_inv_rev, mul_assoc]

def subgroupProductEquiv (H A : Subgroup G)
    (hn : A ≤ normalizer (H : Set G)) (hd : Disjoint H A) :
    H ⋊[H.normalizerMonoidHom.comp (inclusion hn)] A ≃* (H ⊔ A : Subgroup G) :=
  MulEquiv.ofBijective
    ((SemidirectProduct.monoidHomSubgroup hn).codRestrict (H ⊔ A)
      (fun x => mul_mem_sup x.left.property x.right.property)) (by
    constructor
    · intro x y hxy
      have h := mul_injective_of_disjoint hd
        (a₁ := (x.left,x.right)) (a₂ := (y.left,y.right)) (congrArg Subtype.val hxy)
      exact SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
    · intro x
      have hx : (x : G) ∈ (H : Set G) * (A : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left H A hn]
        exact x.property
      obtain ⟨h, hh, a, ha, he⟩ := hx
      exact ⟨⟨⟨h,hh⟩,⟨a,ha⟩⟩,Subtype.ext he⟩)

def splitIso (H P A : Subgroup G)
    (hH : A ≤ normalizer (H : Set G)) (hP : A ≤ normalizer (P : Set G))
    (hdH : Disjoint H A) (hdP : Disjoint P A) :
    Iso (semidirect (conjugationAction H P A hH hP))
      (ofSubgroups (H ⊔ A) ((H ⊓ P) ⊔ A) (P ⊔ A)
        (sup_le_sup_right inf_le_left A) (sup_le_sup_right inf_le_right A)) where
  left := subgroupProductEquiv H A hH hdH
  middle := subgroupProductEquiv (H ⊓ P) A
    ((le_inf hH hP).trans inf_normalizer_le_normalizer_inf) (hdH.mono_left inf_le_left)
  right := subgroupProductEquiv P A hP hdP
  left_commutes _ := rfl
  right_commutes _ := rfl

end Theory.GroupTheory.RankTwoAmalgam
