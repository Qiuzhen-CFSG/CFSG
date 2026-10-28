module
public import CFSG.Quasithin.ChapterG.Section10.Components
public import Mathlib.GroupTheory.Index

/-!
# The constituent normalizer in G.10.12

For a constituent avoiding the marked point, its stabilizer in X is the
stabilizer of any nonzero vector in its intersection with W. Full centered
transvections give that vector precisely two images. Thus the original
normalizer has index two, without invoking the subsequent component
classification or the separate invariant-submodule theorem G.10.10.

Source: Aschbacher--Smith G.10.12(2), printed p.360.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

omit [FiniteDimensional (ZMod 2) V] in
/-- Full centered transvections make the stabilizer of every vector of W
outside the marked point a subgroup of index two in X. -/
theorem point_centralizer_relIndex_two {a : V} (ha : a ∈ W)
    (hav : a ∉ Submodule.span (ZMod 2) {v}) :
    (pointCentralizer ρ a).relIndex X = 2 := by
  classical
  have binary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have two_values (x : X) : ρ x a = a ∨ ρ x a = a + v := by
    obtain ⟨f,_,hf⟩ := h.transvections x
    have he := hf ⟨a,ha⟩
    rcases binary (f ⟨a,ha⟩) with hz | ho
    · exact Or.inl (by simpa only [hz,zero_smul,add_zero] using he)
    · exact Or.inr (by simpa only [ho,one_smul] using he)
  obtain ⟨f,hfa,hfk⟩ := (Submodule.span (ZMod 2) {v}).exists_le_ker_of_notMem hav
  have hfv : f v = 0 := hfk (Submodule.mem_span_singleton_self v)
  obtain ⟨x,hx⟩ := h.full_transvections (f.comp W.subtype) hfv
  have hxa : ρ x a = a + v := by
    have he := hx ⟨a,ha⟩
    change ρ x a = a + f a • v at he
    simpa only [(binary (f a)).resolve_left hfa,one_smul] using he
  apply Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨x,x.property,?_,?_⟩
  · change ¬ ρ x a = a
    rw [hxa]
    intro he
    exact h.point_ne_zero (add_left_cancel (he.trans (add_zero a).symm))
  · intro b hb
    rcases two_values ⟨b,hb⟩ with he | he
    · exact Or.inr he
    · left
      change ρ (b * x) a = a
      rw [map_mul,Module.End.mul_apply,hxa,map_add,he,h.fixes_point hb]
      have hvv : v + v = 0 := by
        calc
          v + v = (1 : ZMod 2) • v + (1 : ZMod 2) • v := by simp
          _ = ((1 : ZMod 2) + 1) • v := (add_smul _ _ _).symm
          _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide,zero_smul]
      rw [add_assoc,hvv,add_zero]

/-- A constituent avoiding the marked point is stabilized exactly by the
actors fixing a nonzero vector in its intersection with W. -/
theorem constituent_stabilizer_eq_point_centralizer (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ H I) (hv : v ∉ I)
    {a : V} (haI : a ∈ I) (haW : a ∈ W) (ha0 : a ≠ 0) :
    (subspaceStabilizer ρ I).subgroupOf X = (pointCentralizer ρ a).subgroupOf X := by
  ext x
  change (x : G) ∈ subspaceStabilizer ρ I ↔ ρ x a = a
  constructor
  · intro hs
    obtain ⟨f,_,hf⟩ := h.transvections x
    have hxaI : ρ x a ∈ I := (hs a).2 haI
    have he := hf ⟨a,haW⟩
    have hdiff := I.sub_mem hxaI haI
    rw [he,add_sub_cancel_left] at hdiff
    have hf0 : f ⟨a,haW⟩ = 0 := by
      by_contra hn
      exact hv ((I.smul_mem_iff hn).mp hdiff)
    simpa only [hf0,zero_smul,add_zero] using he
  · intro hxa
    apply (subspace_map_eq_iff ρ I x).mp
    rcases hI.eq_or_disjoint_conjugate_of_normal_restriction ρ hi H x with he | hd
    · exact he
    · exact (ha0 (Submodule.disjoint_def.mp hd a ⟨a,haI,hxa⟩ haI)).elim

/-- G.10.12(2), with the literal normalizer inside the original actor X. -/
theorem constituent_stabilizer_relIndex_two (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ H I) (hv : v ∉ I) (hne : I ⊓ W ≠ ⊥) :
    (subspaceStabilizer ρ I).relIndex X = 2 := by
  obtain ⟨a,ha,ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hav : a ∉ Submodule.span (ZMod 2) {v} := by
    intro hs
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hs
    by_cases hr0 : r = 0
    · exact ha0 (by simpa only [hr0,zero_smul] using hr.symm)
    · exact hv ((I.smul_mem_iff hr0).mp (hr.symm ▸ ha.1))
  rw [Subgroup.relIndex,h.constituent_stabilizer_eq_point_centralizer hi H hI hv ha.1 ha.2 ha0]
  exact h.point_centralizer_relIndex_two ha.2 hav

end CFSG.Quasithin.ChapterG.Section10.Hypothesis

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- G.10.12(2) for the literal original terminal action and actor. -/
theorem terminal_constituent_stabilizer_relIndex_two (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (h : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    (H : Subgroup F.TerminalHdot) [H.Normal]
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation H I) (hv : v ∉ I)
    (hne : I ⊓ hatSpace F (F.E g) ≠ ⊥) :
    (subspaceStabilizer F.terminalRepresentation I).relIndex (F.terminalDot (F.X g)) = 2 :=
  h.constituent_stabilizer_relIndex_two (h.irreducible_of_not_solvable hn) H hI hv hne

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
