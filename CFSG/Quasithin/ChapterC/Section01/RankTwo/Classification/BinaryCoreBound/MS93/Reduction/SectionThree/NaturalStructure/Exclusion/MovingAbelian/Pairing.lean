module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Quotient

/-!
# Residual-invariant commutator forms on the moving radius

The commutator pairing on P/Z(P), for P the actual moving radius, takes values
in the elementary derived subgroup P'. Composing with all binary functionals
on P' gives alternating forms with zero common radical. The local residual
fixes P' by the supplied derived-radius containment, so it preserves every
one of these forms. Individual forms may be degenerate, and no self-duality
of the whole quotient or pointwise fixation of its whole center is assumed.

The private pairing construction adapts
Theory/GroupTheory/CentralQuotientCommutatorForms.lean, weakening its center
fixation premise to fixation of the derived subgroup. The source-specific
specialization uses the literal conjugation action and ambient commutators.
Source: Meierfrankenfeld--Stellmacher (1993), (3.8), printed p.878.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
variable {M : Type*} [Group M] {L R : Subgroup M}

private def derivedBracketHom {P : Type*} [Group P]
    (hd : _root_.commutator P ≤ center P) (x : P) : P →* _root_.commutator P where
  toFun y := ⟨⁅x,y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' y z := by
    apply Subtype.ext
    change ⁅x,y*z⁆ = ⁅x,y⁆ * ⁅x,z⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅x,y⁆ y ⁅x,z⁆,
      mem_center_iff.mp (hd (commutator_mem_commutator (mem_top x) (mem_top z))) y]
    simp only [← mul_assoc, mul_inv_cancel_right]

private theorem exists_derived_pairing {P : Type*} [Group P]
    [IsMulCommutative (_root_.commutator P)]
    (hd : _root_.commutator P ≤ center P) :
    ∃ B : (P ⧸ center P) →* ((P ⧸ center P) →* _root_.commutator P),
      ∀ x y : P, (B (QuotientGroup.mk' (center P) x)
        (QuotientGroup.mk' (center P) y) : P) = ⁅x,y⁆ := by
  have hk (x : P) : center P ≤ (derivedBracketHom hd x).ker := by
    intro z hz
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz x)
  let B : P →* ((P ⧸ center P) →* _root_.commutator P) := {
    toFun x := QuotientGroup.lift (center P) (derivedBracketHom hd x) (hk x)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
      apply Subtype.ext
      change ⁅(1 : P), y⁆ = 1
      simp
    map_mul' x y := by
      apply MonoidHom.ext
      intro q
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
      apply Subtype.ext
      change ⁅x*y,z⁆ = ⁅x,z⁆ * ⁅y,z⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (hd (commutator_mem_commutator (mem_top y) (mem_top z))) x]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp (hd (commutator_mem_commutator (mem_top y) (mem_top z))) ⁅x,z⁆).symm }
  refine ⟨QuotientGroup.lift (center P) B ?_, fun x y => rfl⟩
  intro x hx
  apply MonoidHom.ext
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
  apply Subtype.ext
  change ⁅x,y⁆ = 1
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm


private theorem exists_derived_fixed_forms
    {P : Type*} [Group P] [IsElementaryAbelian 2 (P ⧸ center P)] :
    ∃ forms : Set (LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P))),
      (∀ B ∈ forms, B.IsAlt) ∧
      (∀ v, (∀ B ∈ forms, ∀ w, B v w = 0) → v = 0) ∧
      ∀ (a : MulAut P), (∀ z : _root_.commutator P, a z = z) →
        ∀ B ∈ forms, ∀ v w,
          B (Additive.ofMul (quotientAut (center P) a v.toMul))
            (Additive.ofMul (quotientAut (center P) a w.toMul)) = B v w := by
  let hq : IsElementaryAbelian 2 (P ⧸ center P) := inferInstance
  let := hq.derived_of_central_quotient
  obtain ⟨pairing, heval⟩ := exists_derived_pairing hq.commutator_le_center_of_central_quotient
  let scalar (f : Module.Dual (ZMod 2) (Additive (_root_.commutator P))) :
      LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P)) :=
    AddMonoidHom.toZModLinearMap 2 {
      toFun := fun x => AddMonoidHom.toZModLinearMap 2 {
        toFun := fun y => f (Additive.ofMul (pairing x.toMul y.toMul))
        map_zero' := by simp
        map_add' := by intros; simp }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  refine ⟨Set.range scalar, ?_, ?_, ?_⟩
  · rintro _ ⟨f, rfl⟩ v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    have hB : pairing v.toMul v.toMul = 1 := by
      apply Subtype.ext
      rw [← hx, heval, commutatorElement_self]
      rfl
    change f (Additive.ofMul (pairing v.toMul v.toMul)) = 0
    rw [hB]
    exact map_zero f
  · intro v hv
    have hB (w : P ⧸ center P) : pairing v.toMul w = 1 := by
      by_contra hn
      have hn' : Additive.ofMul (pairing v.toMul w) ≠ 0 := hn
      obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hn'
      exact hf (hv (scalar f) ⟨f, rfl⟩ (Additive.ofMul w))
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    have hcenter : x ∈ center P := by
      apply mem_center_iff.mpr
      intro y
      have he := congrArg Subtype.val (hB (QuotientGroup.mk' (center P) y))
      rw [← hx, heval] at he
      exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
    exact congrArg Additive.ofMul (hx.symm.trans ((QuotientGroup.eq_one_iff x).mpr hcenter))
  · intro a ha B hB v w
    obtain ⟨f, rfl⟩ := hB
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center P) w.toMul
    change f (Additive.ofMul (pairing (quotientAut (center P) a v.toMul)
      (quotientAut (center P) a w.toMul))) = f (Additive.ofMul (pairing v.toMul w.toMul))
    congr 2
    apply Subtype.ext
    rw [← hx, ← hy, quotientAut_apply_mk, quotientAut_apply_mk, heval, heval,
      ← map_commutatorElement]
    exact ha ⟨⁅x,y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩


/-- Scalar commutator forms separate the actual moving central quotient and
are invariant under its two-residual action. Only the derived subgroup, not
the whole center, needs to be fixed. -/
theorem movingQuotient_separating_forms (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a) :
    letI := moving_central_quotient_elementary geometry hb a ha hfixed
    ∃ forms : Set (LinearMap.BilinForm (ZMod 2)
        (Additive ((Vcirc R a) ⧸ center (Vcirc R a)))),
      (∀ B ∈ forms, B.IsAlt) ∧
      (∀ v, (∀ B ∈ forms, ∀ w, B v w = 0) → v = 0) ∧
      ∀ (g : stabilizer R a), g ∈ pResidual 2 (stabilizer R a) →
        ∀ B ∈ forms, ∀ v w,
          B (Additive.ofMul (movingQuotientAction a g v.toMul))
            (Additive.ofMul (movingQuotientAction a g w.toMul)) = B v w := by
  let := moving_central_quotient_elementary geometry hb a ha hfixed
  obtain ⟨forms, halt, hsep, hinv⟩ :=
    exists_derived_fixed_forms (P := Vcirc R a)
  refine ⟨forms, halt, hsep, ?_⟩
  intro g hg B hB v w
  apply hinv (movingAction a g) ?_ B hB v w
  intro d
  apply Subtype.ext
  rw [movingAction_apply]
  have hm : Vcirc R a ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hd : ((d : Vcirc R a) : FreeAmalgam R) ∈ ⁅Vcirc R a, Vcirc R a⁆ := by
    rw [← map_subtype_commutator]
    exact mem_map_of_mem (Vcirc R a).subtype d.property
  have hdf := hfixed (commutator_mono hm hm hd)
  have hgl : (g : FreeAmalgam R) ∈ Ltilde R a :=
    mem_map_of_mem (stabilizer R a).subtype hg
  rw [hdf.2 g hgl, mul_inv_cancel_right]


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
