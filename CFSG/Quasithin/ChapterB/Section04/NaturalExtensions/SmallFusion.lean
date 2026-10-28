module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.Setup

/-!
# B.4.8 fixed-space calculations on the original Section 12.4 module

The existing marked extension identifies the action with conjugation on the
original elementary abelian subgroup V and the actor with L/O₂(L). Its
nonzero fixed kernel and the cohomology bound force dimension four. Applying
B.4.8's proved involution geometry gives rank two and cardinality four for
the literal involution centralizer in V; the Sylow fixed space is the
original fixed line. No fusion or centralizer witness is assumed.

These are the module calculations used in Aschbacher–Smith 12.4.5–6 and 9,
printed pp.813–815, from B.4.8(2), printed p.91 (1 March 2004 manuscript).
The remaining source-local subgroup arguments belong to Section 12.4.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeExtension
open Section02
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (E : SLThreeExtension D)

include E in
/-- The actual nontrivial fixed-line alternative has dimension four. -/
theorem b48_dimension_four (hne : fixedSubgroup L V ≠ ⊥) : letI := D.elementary
    Module.finrank (ZMod 2) (Additive V) = 4 := by
  let _ := D.elementary
  have hn : E.projection.toLinearMap.ker ≠ ⊥ := by
    intro hk
    apply hne
    apply _root_.eq_bot_iff.mpr
    intro x hx
    let v : Additive V := Additive.ofMul ⟨x,hx.1⟩
    have hv : v ∈ E.projection.toLinearMap.ker := by
      rw [E.kernel]
      exact (E.mem_fixed_iff v).mpr hx.2
    have hv0 : v = 0 := by simpa only [hk, Submodule.mem_bot] using hv
    exact congrArg (fun w : Additive V => (w.toMul : G)) hv0
  have hb := SLThreeCentralExtension.finrank_kernel_le_one E.projection E.surjective
    E.kernel.le E.indecomposable
  have hp : 0 < Module.finrank (ZMod 2) E.projection.toLinearMap.ker := by
    let : Nontrivial E.projection.toLinearMap.ker := Submodule.nontrivial_iff_ne_bot.mpr hn
    exact Module.finrank_pos
  have hd := E.projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr E.surjective, finrank_top, Module.finrank_fin_fun] at hd
  omega

/-- The exact B.4.8(2) involution geometry on the original chosen V. -/
theorem b48_involution_geometry (hne : fixedSubgroup L V ≠ ⊥)
    (a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (ha : orderOf a = 2) :
    letI := D.elementary
    subspaceCommutator E.action ⊤ (zpowers a) = fixedSpace E.action (zpowers a) ∧
      Module.finrank (ZMod 2) (fixedSpace E.action (zpowers a)) = 2 := by
  let _ := D.elementary
  exact ChapterB.NaturalExtensions.central_quotient_involutions E.action E.projection
    E.surjective E.kernel.le E.indecomposable (E.b48_dimension_four hne) a ha

/-- The Sylow-fixed space is the original L-fixed line. -/
theorem b48_sylow_fixed (hne : fixedSubgroup L V ≠ ⊥)
    (S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    letI := D.elementary
    fixedSpace E.action (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) =
      fixed E.action := by
  let _ := D.elementary
  exact ChapterB.NaturalExtensions.central_quotient_sylow E.action E.projection
    E.surjective E.kernel.le E.indecomposable (E.b48_dimension_four hne) S

/-- For an involutory image in L/O₂(L), the literal centralizer in V has four elements.
The calculation uses the original conjugation action, without replacing V by a quotient. -/
theorem b48_involution_centralizer_card (hne : fixedSubgroup L V ≠ ⊥) (l : L)
    (ha : orderOf (E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) = 2) :
    Nat.card (V ⊓ centralizer ({(l : G)} : Set G) : Subgroup G) = 4 := by
  let _ := D.elementary
  let a := E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)
  have he (v : Additive V) : v ∈ fixedSpace E.action (zpowers a) ↔
      (v.toMul : G) ∈ centralizer ({(l : G)} : Set G) := by
    rw [mem_fixedSpace_zpowers_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have h := E.conjugation l v
      rw [hv] at h
      exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
    · intro hv
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [E.conjugation]
      exact mul_inv_eq_iff_eq_mul.mpr hv.symm
  let e : (V ⊓ centralizer ({(l : G)} : Set G) : Subgroup G) ≃ fixedSpace E.action (zpowers a) := {
    toFun := fun v => ⟨Additive.ofMul ⟨v,v.property.1⟩, (he _).mpr v.property.2⟩
    invFun := fun v => ⟨v.val.toMul, v.val.toMul.property, (he _).mp v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    (E.b48_involution_geometry hne a ha).2]
  norm_num
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeExtension
