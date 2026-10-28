module

public import Theory.SpecificGroups.ReeTwo.SylowPackedArithmetic

/-!
# The short full-Ree Sylow involution

A shear adds coordinates b0 and b1 to b7 and b8, with the forced central
correction b1 + b0*b1. It commutes with the cyclic-four action. Twisting that
cyclic generator by the last central root gives the involution with generator
codes [3584,129,770,4,8,16,32,64,128,256,512]. Multiplicativity is proved on the
core polynomials and the ten presentation generators; no enumeration of all
pairs of Sylow elements is needed.

This constructs the proposed overlap automorphism, without asserting extension
to either endpoint. Source coordinates: Shinoda (1975), pp.81–83; the marked
restriction problem is Parrott (1972), p.683 and Aschbacher–Smith F.1.11–12,
printed pp.262–263. Discovery: ../source/README.md.
-/

@[expose] public section
open ReeTwo
namespace Tits.AmalgamRigidity.FullRee.SecondSeparator

def coreFunction (x : Core) : Core :=
  ⟨x.b0, x.b1, x.b2, x.b3, x.b4, x.b5, x.b6, x.b7 + x.b0,
    x.b8 + x.b1, x.b9 + x.b1 + x.b0 * x.b1⟩

theorem coreFunction_involutive : Function.Involutive coreFunction := by
  intro x
  apply Core.ext <;> simp only [coreFunction]
  all_goals ring_nf; reduce_mod_char

def coreMap : MulAut Core where
  toFun := coreFunction
  invFun := coreFunction
  left_inv := coreFunction_involutive
  right_inv := coreFunction_involutive
  map_mul' x y := by
    change coreFunction (Core.mul x y) = Core.mul (coreFunction x) (coreFunction y)
    apply Core.ext <;> simp only [coreFunction, Core.mul]
    all_goals ring

def coreHom : Core →* SylowModel :=
  SemidirectProduct.inl.comp coreMap.toMonoidHom

def actor : SylowModel :=
  SylowModel.root 9 * SemidirectProduct.inr (FiveFour.generator 4)

set_option maxRecDepth 8192 in
theorem actor_four : actor ^ 4 = 1 := by decide +kernel

def cyclicHom : FiveFour.Cyclic 4 →* SylowModel :=
  FiveFour.cyclicHom actor actor_four

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem compatibility (t : FiveFour.Cyclic 4) :
    coreHom.comp (Core.complementAction (SemidirectProduct.inr t)).toMonoidHom =
      (MulAut.conj (cyclicHom t)).toMonoidHom.comp coreHom := by
  apply Core.hom_ext
  exact (by decide +kernel : ∀ (t : FiveFour.Cyclic 4) (i : CoreRoot),
    coreHom (Core.complementAction (SemidirectProduct.inr t) (Core.root i)) =
      MulAut.conj (cyclicHom t) (coreHom (Core.root i))) t

def sylowHom : SylowModel →* SylowModel :=
  SemidirectProduct.lift coreHom cyclicHom compatibility

theorem sylowHom_inl (x : Core) :
    sylowHom (SemidirectProduct.inl x) = SemidirectProduct.inl (coreMap x) :=
  SemidirectProduct.lift_inl ..

theorem sylowHom_inr (t : FiveFour.Cyclic 4) :
    sylowHom (SemidirectProduct.inr t) = cyclicHom t :=
  SemidirectProduct.lift_inr ..

theorem sylowHom_involutive : Function.Involutive sylowHom := by
  have hh : sylowHom.comp sylowHom = MonoidHom.id _ := by
    apply SemidirectProduct.hom_ext
    · apply Core.hom_ext
      intro i
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, sylowHom_inl]
      exact (by decide +kernel : ∀ i : CoreRoot,
        (SemidirectProduct.inl (coreMap (coreMap (Core.root i))) : SylowModel) =
          SemidirectProduct.inl (Core.root i)) i
    · apply FiveFour.cyclicHom_ext
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, sylowHom_inr,
        cyclicHom, FiveFour.cyclicHom_generator]
      change sylowHom (SylowModel.root 9 * SemidirectProduct.inr (FiveFour.generator 4)) = _
      rw [map_mul]
      change sylowHom (SemidirectProduct.inl (Core.root 9)) *
        sylowHom (SemidirectProduct.inr (FiveFour.generator 4)) = _
      rw [sylowHom_inl, sylowHom_inr]
      decide +kernel
  exact fun x => DFunLike.congr_fun hh x

def separator : MulAut SylowModel :=
  { sylowHom with
    invFun := sylowHom
    left_inv := sylowHom_involutive
    right_inv := sylowHom_involutive }

@[simp] theorem separator_root (i : CoreRoot) :
    separator (SylowModel.root i) = SemidirectProduct.inl (coreMap (Core.root i)) :=
  sylowHom_inl _

@[simp] theorem separator_rootOne :
    separator SylowModel.rootOne = SylowModel.rootOne * SylowModel.root 9 := by
  change sylowHom (SemidirectProduct.inr (FiveFour.generator 4)⁻¹) = _
  rw [sylowHom_inr, map_inv]
  change actor⁻¹ = _
  decide +kernel

theorem separator_images :
    SylowModel.Collected.code (separator SylowModel.rootOne) = 3584 ∧
    (∀ i : CoreRoot, SylowModel.Collected.code (separator (SylowModel.root i)) =
      ![129, 770, 4, 8, 16, 32, 64, 128, 256, 512] i) := by
  rw [separator_rootOne]
  constructor
  · decide +kernel
  · intro i
    rw [separator_root]
    exact (by decide +kernel : ∀ i : CoreRoot,
      SylowModel.Collected.code (SemidirectProduct.inl (coreMap (Core.root i))) =
        ![129, 770, 4, 8, 16, 32, 64, 128, 256, 512] i) i

theorem separator_involutive : Function.Involutive separator := sylowHom_involutive

theorem separator_ne_one : separator ≠ 1 := by
  intro he
  have hh := congrArg (fun r : MulAut SylowModel =>
    SylowModel.Collected.code (r (SylowModel.root 0))) he
  rw [separator_images.2] at hh
  exact (by decide : (129 : Nat) ≠ 1) hh

/-- The first two roots carry the only nontrivial core changes. -/
theorem separator_root_zero :
    separator (SylowModel.root 0) = SylowModel.root 0 * SylowModel.root 7 := by
  rw [separator_root]
  decide +kernel

theorem separator_root_one : separator (SylowModel.root 1) =
    SylowModel.root 1 * SylowModel.root 8 * SylowModel.root 9 := by
  rw [separator_root]
  decide +kernel

/-- All later core roots are fixed. -/
theorem separator_root_fixed (i : CoreRoot) (hi : 2 ≤ i.val) :
    separator (SylowModel.root i) = SylowModel.root i := by
  rw [separator_root]
  exact (by decide +kernel : ∀ i : CoreRoot, 2 ≤ i.val →
    (SemidirectProduct.inl (coreMap (Core.root i)) : SylowModel) =
      SylowModel.root i) i hi

end Tits.AmalgamRigidity.FullRee.SecondSeparator
