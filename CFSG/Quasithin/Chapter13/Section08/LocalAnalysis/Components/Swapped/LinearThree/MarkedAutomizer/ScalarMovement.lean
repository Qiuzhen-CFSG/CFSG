module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.Diagonal

/-!
# Commutator generation forces motion on the scalar line

If [R,T]=R, a nontrivial quotient of R cannot be fixed by T. Apply this to
the first coordinate of the marked cubic plane: invariance of the second
line and pointwise fixation of the first would make the first coordinate
of every commutator trivial. Surjectivity gives a contradiction.

Together with the separately checked diagonal-action calculation, this
removes a putative extra premise asserting that T moves the scalar line.
The geometric identification of the two lines and the inner inverter still
have to be proved for the actual marked residual.

Source use: Aschbacher–Smith 13.8.16(1), printed p.952 (PDF p.969).
The occurrence of L₁=[L₁,T] on p.937 is in the simple-A₆ case. It does
not establish this premise in the triple-cover case. A source application
must separately prove generation or construct actual scalar motion; the
existence of an odd automorphism in a larger model group is insufficient.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

variable {G : Type*} [Group G]

noncomputable def coordinateAction (R M : Subgroup G)
    (e : (R ⧸ pCore 2 R) ≃* Model.CubicPlane) :
    (M ⊓ normalizer (R : Set G) : Subgroup G) →* MulAut Model.CubicPlane :=
  (MulAut.congr e).toMonoidHom.comp (automizerAction R M)

/-- The source identity [R,T]=R forces movement of the scalar direction
once the two actual directions are invariant. -/
theorem scalar_moves_of_commutator (R T M : Subgroup G)
    (hn : T ≤ normalizer (R : Set G)) (hTM : T ≤ M)
    (hgen : ⁅R, T⁆ = R) (e : (R ⧸ pCore 2 R) ≃* Model.CubicPlane)
    (hd : ∀ m, Model.derivedAxis.map (coordinateAction R M e m).toMonoidHom =
      Model.derivedAxis) :
    ∃ m, ∃ c : Model.C3, coordinateAction R M e m (c, 1) ≠ (c, 1) := by
  classical
  by_contra! hfix
  let f : R →* Model.C3 := (MonoidHom.fst _ _).comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R)))
  have hfst (m : (M ⊓ normalizer (R : Set G) : Subgroup G)) (v : Model.CubicPlane) :
      (coordinateAction R M e m v).1 = v.1 := by
    have hzero : (coordinateAction R M e m (1, v.2)).1 = 1 := by
      have hmem : coordinateAction R M e m (1, v.2) ∈ Model.derivedAxis :=
        hd m ▸ mem_map_of_mem _ (show (1, v.2) ∈ Model.derivedAxis from ⟨rfl, mem_top _⟩)
      exact hmem.1
    have he := congrArg Prod.fst ((coordinateAction R M e m).map_mul (v.1, 1) (1, v.2))
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, hfix m v.1, Prod.fst_mul,
      hzero] using he
  have hinv (t : T) (r : R) :
      f (R.normalizerMonoidHom (inclusion hn t) r) = f r := by
    let m : (M ⊓ normalizer (R : Set G) : Subgroup G) := inclusion (le_inf hTM hn) t
    have he := hfst m (e (QuotientGroup.mk' (pCore 2 R) r))
    change (e (automizerAction R M m
      (e.symm (e (QuotientGroup.mk' (pCore 2 R) r))))).1 = _ at he
    rw [MulEquiv.symm_apply_apply] at he
    change (e (quotientAction R _ inf_le_right m (QuotientGroup.mk' (pCore 2 R) r))).1 = _ at he
    rw [quotientAction_mk] at he
    exact he
  have hcomm : ⁅T, R⁆ ≤ f.ker.map R.subtype := by
    apply commutator_le.mpr
    intro t ht r hr
    let tr : R := R.normalizerMonoidHom (inclusion hn ⟨t, ht⟩) ⟨r, hr⟩
    refine ⟨tr * (⟨r, hr⟩ : R)⁻¹, ?_, rfl⟩
    change f (tr * (⟨r, hr⟩ : R)⁻¹) = 1
    rw [map_mul, map_inv, hinv, mul_inv_cancel]
  rw [commutator_comm T R, hgen] at hcomm
  have hall (r : R) : f r = 1 := by
    obtain ⟨s, hs, he⟩ := hcomm r.property
    have he' : s = r := Subtype.ext he
    subst s
    exact hs
  let c : Model.C3 := Multiplicative.ofAdd (1 : ZMod 3)
  obtain ⟨r, hr⟩ := (QuotientGroup.mk'_surjective (pCore 2 R)) (e.symm (c, 1))
  have hc : f r = c := by
    change (e (QuotientGroup.mk' (pCore 2 R) r)).1 = c
    rw [hr, MulEquiv.apply_symm_apply]
  have : c = 1 := hc.symm.trans (hall r)
  exact (by decide : c ≠ 1) this

/-- Conditional assembly of the actual automizer image after the two marked
lines and the inner inverter have been identified. This does not establish
those geometric inputs for the source subgroup. -/
noncomputable def automizerEquivE4_of_marked_action (R T M : Subgroup G)
    (hn : T ≤ normalizer (R : Set G)) (hTM : T ≤ M)
    (hgen : ⁅R, T⁆ = R) (e : (R ⧸ pCore 2 R) ≃* Model.CubicPlane)
    (hs : ∀ m, Model.scalarAxis.map (coordinateAction R M e m).toMonoidHom =
      Model.scalarAxis)
    (hd : ∀ m, Model.derivedAxis.map (coordinateAction R M e m).toMonoidHom =
      Model.derivedAxis)
    (hinvert : Diagonal.diagonalAction Diagonal.derivedFlip ∈
      (coordinateAction R M e).range) :
    (automizerAction R M).range ≃* E4 := by
  let c := MulAut.congr e
  have hr : (automizerAction R M).range.map c.toMonoidHom =
      (coordinateAction R M e).range := (MonoidHom.range_comp _ _).symm
  exact ((c.subgroupMap (automizerAction R M).range).trans (MulEquiv.subgroupCongr hr)).trans
    (Diagonal.imageEquivE4 (coordinateAction R M e) hs hd hinvert
      (scalar_moves_of_commutator R T M hn hTM hgen e hd))

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

end
