module
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreInRestriction
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Normal binary-three actions and the centre of an overgroup core

Let a normal subgroup act, through its original two-core quotient, as the
natural-plus-dual module for SL₃(2). Commutators with the overgroup's two-core
lie in the acting subgroup's two-core. Consequently the induced operators
commute with the marked action; its trivial invertible commutant makes those
operators trivial. A normal elementary module therefore embeds in the centre
of the full overgroup core.

The mapped version retains the injective residual and module homomorphisms,
the original quotient projection and the actual linear marking. No Sylow
placement or containment of the overgroup core in the residual is assumed.
Source: the local-module inspection in Aschbacher–Smith 4.4.3, printed
pp.622–623 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace BinaryLinearThree.NaturalDual
variable {G U : Type*} [_root_.Group G] [_root_.Group U] [IsElementaryAbelian 2 U]

/-- A marked normal action annihilates the full ambient two-core. -/
theorem core_acts_trivially (R : Subgroup G) [R.Normal]
    (φ : G →* MulAut U) (π : R →* BinaryLinearThree.Group)
    (hπ : Function.Surjective π) (hcore : pCore 2 R ≤ π.ker)
    (E : Additive U ≃ₗ[ZMod 2] Space)
    (ha : ∀ (r : R) (v : Additive U),
      E (Additive.ofMul (φ r v.toMul)) = action (π r) (E v)) :
    pCore 2 G ≤ φ.ker := by
  have hk (z : R) (hz : z ∈ pCore 2 R) : φ z = 1 := by
    ext u
    change φ z u = u
    apply Additive.ofMul.injective
    apply E.injective
    have hh := ha z (Additive.ofMul u)
    have hzero : π z = 1 := hcore hz
    simpa only [hzero, map_one, Module.End.one_apply, toMul_ofMul] using hh
  intro x hx
  have hc (r : R) : Commute (φ x) (φ r) := by
    have hm := commutator_mem_commutator hx r.property
    have hr : ⁅x, (r : G)⁆ ∈ R := (commutator_le_right (pCore 2 G) R) hm
    have hp : ⁅x, (r : G)⁆ ∈ pCore 2 G := (commutator_le_left (pCore 2 G) R) hm
    have hz : (⟨⁅x, (r : G)⁆,hr⟩ : R) ∈ pCore 2 R := by
      rw [pCore_eq_comap_of_normal]
      exact hp
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact hk _ hz
  let a := (φ x).toAdditive
  let f : Additive U ≃ₗ[ZMod 2] Additive U :=
    a.toLinearEquiv (fun c v => ZMod.map_smul a.toAddMonoidHom c v)
  let F : Space ≃ₗ[ZMod 2] Space := E.symm.trans (f.trans E)
  have hF : F = LinearEquiv.refl _ _ := centralizer_eq_one F (by
    intro g v
    obtain ⟨r,rfl⟩ := hπ g
    have hmark : E.symm (action (π r) v) =
        Additive.ofMul (φ r (E.symm v).toMul) := by
      apply E.injective
      rw [E.apply_symm_apply,ha,E.apply_symm_apply]
    change E (f (E.symm (action (π r) v))) = action (π r) (E (f (E.symm v)))
    rw [hmark,←ha]
    apply congrArg E
    apply Additive.toMul.injective
    exact congrArg (fun b : MulAut U => b (E.symm v).toMul) (hc r).eq)
  change φ x = 1
  ext u
  have hh := congrArg (fun e : Space ≃ₗ[ZMod 2] Space => e (E (Additive.ofMul u))) hF
  change E (f (E.symm (E (Additive.ofMul u)))) = E (Additive.ofMul u) at hh
  rw [E.symm_apply_apply] at hh
  exact Additive.ofMul.injective (E.injective hh)
end BinaryLinearThree.NaturalDual

namespace BinaryLinearThree.NaturalDual
open Subgroup
open scoped IsMulCommutative
variable {Q S U : Type*} [_root_.Group Q] [_root_.Group S] [_root_.Group U]
  [IsElementaryAbelian 2 U]

/-- Literal injective residual and module maps give centralization in their ambient carrier. -/
theorem mapped_core_centralizes (M : Subgroup Q) (r : S →* Q) (w : U →* Q)
    (hr : Function.Injective r) (hw : Function.Injective w)
    (hrM : r.range ≤ M) (hnr : M ≤ normalizer (r.range : Set Q))
    (hnw : M ≤ normalizer (w.range : Set Q))
    (e : (S ⧸ pCore 2 S) ≃* BinaryLinearThree.Group)
    (E : Additive U ≃ₗ[ZMod 2] Space)
    (ha : ∀ s v, r s * w (E.symm v).toMul * (r s)⁻¹ =
      w (E.symm (action (e (QuotientGroup.mk' _ s)) v)).toMul) :
    M.pCoreIn 2 ≤ centralizer (w.range : Set Q) := by
  let b : U ≃* w.range := MonoidHom.ofInjective hw
  let φ : M →* MulAut U := (MulAut.congr b.symm).toMonoidHom.comp
    (w.range.normalizerMonoidHom.comp (inclusion hnw))
  have hφ (x : M) (u : U) : w (φ x u) = (x : Q) * w u * (x : Q)⁻¹ := by
    change ((b (b.symm (w.range.normalizerMonoidHom (inclusion hnw x) (b u)))) : Q) = _
    rw [b.apply_symm_apply]
    rfl
  let R := r.range.subgroupOf M
  let : R.Normal := (normal_subgroupOf_iff_le_normalizer hrM).mpr hnr
  let a : R ≃* S := (subgroupOfEquivOfLe hrM).trans (MonoidHom.ofInjective hr).symm
  have hra (x : R) : r (a x) = ((x : M) : Q) := by
    have hh := (MonoidHom.ofInjective hr).apply_symm_apply
      ((subgroupOfEquivOfLe hrM) x)
    exact congrArg Subtype.val hh
  let π : R →* BinaryLinearThree.Group :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 S))).comp a.toMonoidHom
  have hπ : Function.Surjective π :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp a.surjective)
  have hcore : pCore 2 R ≤ π.ker := by
    intro x hx
    have hh : a x ∈ pCore 2 S := by
      rw [←pCore_map_iso 2 a]
      exact mem_map_of_mem _ hx
    change e (QuotientGroup.mk' _ (a x)) = 1
    have hhq : QuotientGroup.mk' (pCore 2 S) (a x) = 1 :=
      (QuotientGroup.eq_one_iff (a x)).mpr hh
    rw [hhq,map_one]
  have hmark (x : R) (v : Additive U) :
      E (Additive.ofMul (φ x v.toMul)) = action (π x) (E v) := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    apply Additive.toMul.injective
    apply hw
    rw [toMul_ofMul,hφ]
    have hh := ha (a x) (E v)
    rw [hra,E.symm_apply_apply] at hh
    exact hh
  have hc := core_acts_trivially R φ π hπ hcore E hmark
  rintro _ ⟨x,hx,rfl⟩ _ ⟨u,rfl⟩
  have hh := hφ x u
  have he : φ x = 1 := hc hx
  rw [he] at hh
  change w u = (x : Q) * w u * (x : Q)⁻¹ at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
end BinaryLinearThree.NaturalDual

namespace BinaryLinearThree.NaturalDual
open Subgroup
open scoped IsMulCommutative
variable {Q S U : Type*} [_root_.Group Q] [_root_.Group S] [_root_.Group U]
  [IsElementaryAbelian 2 U]

/-- A normal elementary module lies in the embedded full core centre, with its order bound. -/
theorem mapped_module_in_core_center [Finite Q]
    (M : Subgroup Q) (r : S →* Q) (w : U →* Q)
    (hr : Function.Injective r) (hw : Function.Injective w)
    (hrM : r.range ≤ M) (hwM : w.range ≤ M)
    (hnr : M ≤ normalizer (r.range : Set Q))
    (hnw : M ≤ normalizer (w.range : Set Q))
    (e : (S ⧸ pCore 2 S) ≃* BinaryLinearThree.Group)
    (E : Additive U ≃ₗ[ZMod 2] Space)
    (ha : ∀ s v, r s * w (E.symm v).toMul * (r s)⁻¹ =
      w (E.symm (action (e (QuotientGroup.mk' _ s)) v)).toMul) :
    w.range ≤ (center (M.pCoreIn 2)).map (M.pCoreIn 2).subtype ∧
      Nat.card w.range ≤ Nat.card (center (pCore 2 M)) := by
  have hc := mapped_core_centralizes M r w hr hw hrM hnr hnw e E ha
  have hp : IsPGroup 2 w.range :=
    (IsElementaryAbelian.isPGroup 2 U).of_surjective w.rangeRestrict w.rangeRestrict_surjective
  have hWP := le_pCoreIn_of_normalizes hp hwM hnw
  have hZ : w.range ≤ (center (M.pCoreIn 2)).map (M.pCoreIn 2).subtype := by
    intro x hx
    refine ⟨⟨x,hWP hx⟩,mem_center_iff.mpr (fun p => ?_),rfl⟩
    exact Subtype.ext (hc p.property x hx).symm
  refine ⟨hZ,?_⟩
  have hh := card_le_of_le hZ
  rw [card_map_of_injective (M.pCoreIn 2).subtype_injective] at hh
  let a : pCore 2 M ≃* M.pCoreIn 2 :=
    (pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
  exact hh.trans_eq (Nat.card_congr (centerCongr a).toEquiv).symm
end BinaryLinearThree.NaturalDual

namespace BinaryLinearThree.NaturalDual
open Subgroup
variable {Q : Type*} [_root_.Group Q]

/-- Relative normality gives the exact intersection with the full overgroup core. -/
theorem normal_core_intersection (R M : Subgroup Q) (hRM : R ≤ M)
    (hn : M ≤ normalizer (R : Set Q)) : R ⊓ M.pCoreIn 2 = R.pCoreIn 2 :=
  le_antisymm (inf_pCoreIn_le_of_le 2 hRM)
    (le_inf (pCoreIn_le 2 R) (pCoreIn_mono_of_normalizes hRM hn))

/-- Commutators with the full overgroup core lie in the residual core. -/
theorem normal_core_commutator (R M : Subgroup Q) (hRM : R ≤ M)
    (hn : M ≤ normalizer (R : Set Q)) : ⁅M.pCoreIn 2,R⁆ ≤ R.pCoreIn 2 := by
  rw [←normal_core_intersection R M hRM hn]
  have hP : M ≤ normalizer (M.pCoreIn 2 : Set Q) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 M).le_normalizer_map M.subtype
  exact le_inf
    (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 M).trans hn))
    (le_normalizer_iff_commutator_le_left.mp (hRM.trans hP))
end BinaryLinearThree.NaturalDual

namespace BinaryLinearThree.NaturalDual
/-- Transport the full intrinsic core centre through an actual group equivalence. -/
theorem core_center_card_congr {A B : Type*} [_root_.Group A] [_root_.Group B]
    (e : A ≃* B) : Nat.card (Subgroup.center (pCore 2 A)) =
      Nat.card (Subgroup.center (pCore 2 B)) := by
  let eP : pCore 2 A ≃* pCore 2 B :=
    (e.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  exact Nat.card_congr (Subgroup.centerCongr eP).toEquiv
end BinaryLinearThree.NaturalDual
