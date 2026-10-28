module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A binary natural plane is moved by its own stabilizer

A transvection with direction in a marked plane and nonzero displacement
on that plane belongs to its stabilizer. Its determinant is one, so it is
an actual special-linear actor. The statement is transported through the
original group and module equivalence, retaining the same marked plane.
This is the finite natural-action obstruction for the quintic section.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl

private theorem plane_transvection
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (P : Submodule (ZMod 2) W) (hd : Module.finrank (ZMod 2) P = 2) :
    ∃ t : W ≃ₗ[ZMod 2] W, t.det = 1 ∧
      (∀ w, t w ∈ P ↔ w ∈ P) ∧ ∃ w ∈ P, t w ≠ w := by
  have hP : P ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hnot : ¬P ≤ Submodule.span (ZMod 2) {v} := by
    intro hh
    have hdim := Submodule.finrank_mono hh
    rw [hd,finrank_span_singleton hvn] at hdim
    omega
  obtain ⟨w,hw,hwn⟩ := Set.not_subset.mp hnot
  obtain ⟨f,hfw,hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwn inferInstance
  have hfv : f v = 0 := by
    have hm : f v ∈ (Submodule.span (ZMod 2) {v}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
    rw [hf] at hm
    exact hm
  let t := LinearEquiv.transvection hfv
  refine ⟨t,LinearEquiv.transvection.det_eq_one hfv,?_,w,hw,?_⟩
  · intro z
    change z + f z • v ∈ P ↔ z ∈ P
    constructor
    · intro hz
      simpa using P.sub_mem hz (P.smul_mem (f z) hv)
    · intro hz
      exact P.add_mem hz (P.smul_mem (f z) hv)
  · intro he
    change w + f w • v = w at he
    have hz : f w • v = 0 := by
      exact add_left_cancel (show w + f w • v = w + 0 by simpa only [add_zero] using he)
    exact (smul_eq_zero.mp hz).elim hfw hvn

/-- The actual stabilizer of a binary natural plane contains an actor moving it. -/
theorem binary_natural_plane_stabilizer_moves (n : ℕ)
    (P : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hd : Module.finrank (ZMod 2) P = 2) :
    ¬ P ≤ fixedSpace (specialLinearNatural (k := ZMod 2) n)
      (subspaceStabilizer (specialLinearNatural (k := ZMod 2) n) P) := by
  obtain ⟨t,ht,hs,w,hw,hm⟩ := plane_transvection P hd
  let g := (Matrix.SpecialLinearGroup.toLin'_equiv).symm
    (⟨t,ht⟩ : _root_.SpecialLinearGroup (ZMod 2) (Fin n → ZMod 2))
  have hg (v : Fin n → ZMod 2) : specialLinearNatural n g v = t v := by
    have hh := congrArg (fun a : _root_.SpecialLinearGroup (ZMod 2) (Fin n → ZMod 2) => a v)
      (Matrix.SpecialLinearGroup.toLin'_equiv.apply_symm_apply
        (⟨t,ht⟩ : _root_.SpecialLinearGroup (ZMod 2) (Fin n → ZMod 2)))
    exact hh
  intro hfix
  have hgs : g ∈ subspaceStabilizer (specialLinearNatural (k := ZMod 2) n) P := by
    intro v
    rw [hg]
    exact hs v
  exact hm ((hg w).symm.trans (hfix hw ⟨g,hgs⟩))

/-- A marked binary natural component cannot have its plane stabilizer
fix the plane pointwise. The group and module coordinates remain the given ones. -/
theorem marked_binary_natural_plane_stabilizer_moves
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D) (n : ℕ)
    (e : ChapterB.QuasisimpleSource.ActionEquiv (ρ.comp L.subtype)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two n))
    (P : Submodule (ZMod 2) W) (hd : Module.finrank (ZMod 2) P = 2) :
    ¬P ≤ fixedSpace ρ (L ⊓ subspaceStabilizer ρ P) := by
  let P' := P.map e.linearEquiv.toLinearMap
  have hd' : Module.finrank (ZMod 2) P' = 2 :=
    (e.linearEquiv.finrank_map_eq P).trans hd
  intro hfix
  apply binary_natural_plane_stabilizer_moves n P' hd'
  intro w hw g
  obtain ⟨v,hv,rfl⟩ := hw
  let l : L := e.groupEquiv.symm g.val
  have hl : l.val ∈ subspaceStabilizer ρ P := by
    intro x
    have hm (y : W) : e.linearEquiv y ∈ P' ↔ y ∈ P := by
      constructor
      · rintro ⟨z,hz,he⟩
        exact e.linearEquiv.injective he ▸ hz
      · intro hy
        exact ⟨y,hy,rfl⟩
    rw [←hm (ρ l x),←hm x]
    have he := e.intertwines l x
    rw [show e.groupEquiv l = g.val from e.groupEquiv.apply_symm_apply g.val] at he
    change e.linearEquiv (ρ l x) = specialLinearNatural n g.val (e.linearEquiv x) at he
    rw [he]
    exact g.property (e.linearEquiv x)
  have hf := hfix hv ⟨l.val,l.property,hl⟩
  have he := e.intertwines l v
  rw [show e.groupEquiv l = g.val from e.groupEquiv.apply_symm_apply g.val] at he
  change e.linearEquiv (ρ l v) = specialLinearNatural n g.val (e.linearEquiv v) at he
  exact he.symm.trans (congrArg e.linearEquiv hf)

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
