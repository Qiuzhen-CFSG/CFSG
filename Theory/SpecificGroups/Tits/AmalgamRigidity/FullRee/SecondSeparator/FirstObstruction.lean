module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.Candidate
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.Setup
public import Theory.SpecificGroups.ReeTwo.CoreActionPacking

/-!
# The short Sylow involution does not extend to the full first endpoint

The order-five complement conjugates core root 1 to root 3. The candidate
fixes root 3 and sends root 1 to root 1*root 8*root 9. These images are not
conjugate in the full first endpoint: inspection of the twenty complement
images reduces any proposed conjugator to a core conjugacy from root 1.
Coordinates b7 and b8 would then force its b4 coordinate to be both zero
and one. Thus no preservation assumption about a marked Tits subgroup is used.

The only finite orbit certificate has twenty entries. All arbitrary core
conjugators are excluded symbolically using the verified multiplication.
Source: Shinoda (1975), pp.81–83; Parrott (1972), p.683; Aschbacher–Smith
F.1.11–12, printed pp.262–263.
-/

@[expose] public section
open ReeTwo
namespace Tits.AmalgamRigidity.FullRee.SecondSeparator

open Core.CensusPacked in
private def orbitCodes (i : Fin 5) (j : Fin 4) : Nat :=
  if j.val % 2 = 0 then ![8, 786, 181, 73, 2] i else ![24, 47, 78, 862, 3] i

open Core.CensusPacked in
private theorem complement_root_three_code (i : Fin 5) (j : Fin 4) :
    code ((Core.c ^ i.val * Core.a ^ j.val) (Core.root 3)) = orbitCodes i j := by
  change code ((Core.c ^ i.val) ((Core.a ^ j.val) (Core.root 3))) = _
  rw [← cAct_iterate_code]
  have ha : ∀ j : Fin 4, code ((Core.a ^ j.val) (Core.root 3)) =
      if j.val % 2 = 0 then 8 else 24 := by decide +kernel
  rw [ha]
  exact (by decide +kernel : ∀ (i : Fin 5) (j : Fin 4),
    (cAct^[i.val]) (if j.val % 2 = 0 then 8 else 24) = orbitCodes i j) i j

/-- Only the actual first-root image in the complement orbit of root 3 has
its first five coordinates. -/
theorem complement_root_three_head (g : Core.complement)
    (h0 : ((g : MulAut Core) (Core.root 3)).b0 = 0)
    (h1 : ((g : MulAut Core) (Core.root 3)).b1 = 1)
    (h2 : ((g : MulAut Core) (Core.root 3)).b2 = 0)
    (h3 : ((g : MulAut Core) (Core.root 3)).b3 = 0)
    (h4 : ((g : MulAut Core) (Core.root 3)).b4 = 0) :
    (g : MulAut Core) (Core.root 3) = Core.root 1 := by
  obtain ⟨i, j, rfl⟩ := Core.complement_normal_form g
  have he : (((Core.complementA ^ 2 * Core.complementR) ^ i.val *
      Core.complementA ^ j.val : Core.complement) : MulAut Core) =
      Core.c ^ i.val * Core.a ^ j.val := rfl
  simp only [he] at *
  have hc : (Core.c ^ i.val * Core.a ^ j.val) (Core.root 3) =
      Core.CensusPacked.decode (orbitCodes i j) := by
    rw [← complement_root_three_code, Core.CensusPacked.decode_code]
  rw [hc] at h0 h1 h2 h3 h4 ⊢
  exact (by decide +kernel : ∀ (i : Fin 5) (j : Fin 4),
    let x := Core.CensusPacked.decode (orbitCodes i j)
    x.b0 = 0 → x.b1 = 1 → x.b2 = 0 → x.b3 = 0 → x.b4 = 0 →
      x = Core.root 1) i j h0 h1 h2 h3 h4

/-- The shear image of root 1 is not conjugate to root 3 even in the full
first endpoint. -/
theorem not_isConj_core_images :
    ¬ IsConj (Centralizer.root 3)
      (SemidirectProduct.inl (coreMap (Core.root 1)) : Centralizer) := by
  intro hh
  obtain ⟨g, hg⟩ := isConj_iff.mp hh
  have he : g * Centralizer.root 3 = SemidirectProduct.inl (coreMap (Core.root 1)) * g :=
    mul_inv_eq_iff_eq_mul.mp hg
  have hl := congrArg SemidirectProduct.left he
  change Core.mul g.left ((g.right : MulAut Core) (Core.root 3)) =
    Core.mul (coreFunction (Core.root 1)) ((Core.complement.subtype 1) g.left) at hl
  rw [map_one, MulAut.one_apply] at hl
  have head : (g.right : MulAut Core) (Core.root 3) = Core.root 1 := by
    apply complement_root_three_head
    all_goals first
      | have h := congrArg Core.b0 hl
        simpa [Core.mul, coreFunction, Core.root, Core.ofCoords] using h
      | have h := congrArg Core.b1 hl
        simpa [Core.mul, coreFunction, Core.root, Core.ofCoords, add_comm (1 : ZMod 2)] using h
      | have h := congrArg Core.b2 hl
        simpa [Core.mul, coreFunction, Core.root, Core.ofCoords] using h
      | have h := congrArg Core.b3 hl
        simpa [Core.mul, coreFunction, Core.root, Core.ofCoords] using h
      | have h := congrArg Core.b4 hl
        simpa [Core.mul, coreFunction, Core.root, Core.ofCoords] using h
  rw [head] at hl
  have h7 := congrArg Core.b7 hl
  have h8 := congrArg Core.b8 hl
  have hzero : g.left.b4 = 0 := by
    simpa [Core.mul, coreFunction, Core.root, Core.ofCoords] using h7
  have hone : g.left.b4 = 1 := by
    simpa [Core.mul, coreFunction, Core.root, Core.ofCoords, add_comm (1 : ZMod 2)] using h8
  exact zero_ne_one (hzero.symm.trans hone)

/-- The five-element complement fuses these two actual core roots. -/
theorem root_one_isConj_root_three :
    IsConj (Centralizer.root 1) (Centralizer.root 3) := by
  apply isConj_iff.mpr
  refine ⟨SemidirectProduct.inr (Core.complementA ^ 2 * Core.complementR), ?_⟩
  change SemidirectProduct.inr _ * SemidirectProduct.inl _ *
    (SemidirectProduct.inr _)⁻¹ = SemidirectProduct.inl _
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  apply congrArg SemidirectProduct.inl
  change Core.c (Core.root 1) = Core.root 3
  decide +kernel

/-- The actual coordinate first inclusion cannot carry an extension of the
short involution. -/
theorem separator_not_mem_firstRestrictions : separator ∉ firstRestrictions := by
  rintro ⟨a, ha⟩
  have hc := a.toMonoidHom.map_isConj root_one_isConj_root_three
  change IsConj (a (Centralizer.root 1)) (a (Centralizer.root 3)) at hc
  rw [← SylowModel.embedding_root, ← SylowModel.embedding_root, ha, ha,
    separator_root_fixed 3 (by decide), SylowModel.embedding_root] at hc
  rw [separator_root] at hc
  have he : SylowModel.embedding
      (SemidirectProduct.inl (coreMap (Core.root 1))) =
        (SemidirectProduct.inl (coreMap (Core.root 1)) : Centralizer) := by
    apply SemidirectProduct.ext
    · rfl
    · exact map_one SylowModel.complementEmbedding
  rw [he] at hc
  exact not_isConj_core_images hc.symm

end Tits.AmalgamRigidity.FullRee.SecondSeparator
