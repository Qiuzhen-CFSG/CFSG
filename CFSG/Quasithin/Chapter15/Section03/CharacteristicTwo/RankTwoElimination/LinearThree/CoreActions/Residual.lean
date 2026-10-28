module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Core
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.SylowKernelCore

/-!
# Residual action on the actual L₃(2) commutator core

Perfectness of L improves the displacement of the genuine section kernel
Y_C from O₂(L) to Q = [O₂(L),L], by the relative three-subgroups lemma.
If Y_C fixes Q, its inverse displacement at each element of L is a
homomorphism into the two-group Q. Two-perfectness of Y_C kills these
homomorphisms, so Y_C centralizes L. In particular this argument does not
use the incorrect full-order-three assertion about Y_C.

We also put [Q,Y_L] in O₂(Y_L) using its actual relative normality. If
[Q,Y_L] = Q, residual exchange therefore places Qᵗ in C_G(L). The full
displacement and fixed-core statements remain inputs to be constructed
from the three-layer action in C.1.34(3).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.3.23, printed p.1129 (PDF p.1146).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
variable {G : Type*} [Group G]

private theorem perfect_component (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : Group.IsPerfect c.L := by
  let _ := c.component.perfect
  have hp := Group.IsPerfect.map (Stellmacher.elementaryAbelianMaxJ I).subtype
    (H := c.L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I))
  rwa [map_subgroupOf_eq_of_le c.le_thompson] at hp

/-- The genuine residual acts trivially on the two-core quotient of L. -/
theorem YC_section_action (d : LocalData G) (L : Subgroup G) :
    YC d L ≤ normalizer (L : Set G) ∧ ⁅YC d L, L⁆ ≤ L.pCoreIn 2 := by
  exact (Chapter4.le_sectionCentralizer_iff _ L).mp
    ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)

/-- Perfectness improves the section-kernel displacement to the commutator core. -/
theorem YC_commutator_le (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : ⁅YC d c.L, c.L⁆ ≤ commutatorCore c.L := by
  let _ := perfect_component d c
  have hC := YC_section_action d c.L
  have hLQ : c.L ≤ normalizer (commutatorCore c.L : Set G) :=
    normalizer_commutator_ge_right _ _
  have hCQ := hC.1.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hdouble : ⁅⁅YC d c.L, c.L⁆, c.L⁆ ≤ commutatorCore c.L :=
    commutator_mono hC.2 le_rfl
  have h := commutator_commutator_le_of_rotate_of_le_normalizer hLQ hLQ hCQ
    (by rwa [commutator_comm c.L (YC d c.L)]) hdouble
  rwa [commutator_eq_self, commutator_comm] at h

/-- Fixing Q suffices for the two-residual Y_C to fix L. The actor is not
assumed to have odd order: its two-perfectness kills the displacement maps. -/
theorem YC_centralizes_of_core_fixed [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hfix : YC d c.L ≤ centralizer (commutatorCore c.L : Set G)) :
    YC d c.L ≤ centralizer (c.L : Set G) := by
  have hcomm := YC_commutator_le d c
  have hQ : IsPGroup 2 (commutatorCore c.L) :=
    (c.L.isPGroup_pCoreIn 2).to_le (commutatorCore_le c.L)
  have hp := ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L
  intro y hy l hl
  let f : YC d c.L →* commutatorCore c.L :=
    { toFun x := ⟨⁅(x : G), l⁆⁻¹,
        (commutatorCore c.L).inv_mem (hcomm (commutator_mem_commutator x.property hl))⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' x z := by
        apply Subtype.ext
        change ⁅(x : G) * (z : G), l⁆⁻¹ = ⁅(x : G), l⁆⁻¹ * ⁅(z : G), l⁆⁻¹
        have hc := hfix x.property _ (hcomm (commutator_mem_commutator z.property hl))
        rw [commutatorElement_mul_left_eq_conj_mul, ← hc, mul_inv_cancel_right, mul_inv_rev] }
  have hf := hp.hom_eq_one_of_isPGroup hQ f
  have he := congrArg (fun k : YC d c.L →* commutatorCore c.L => (k ⟨y, hy⟩ : G)) hf
  change ⁅y, l⁆⁻¹ = 1 at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp (inv_eq_one.mp he)).symm

/-- The S-action on Y_L follows from the S-actions on Y and L. -/
theorem S_normalizes_YL [Finite G] (d : LocalData G) (L : Subgroup G)
    (hSY : d.S ≤ normalizer (d.Yplus : Set G))
    (hSL : d.S ≤ normalizer (L : Set G)) :
    d.S ≤ normalizer (YL d L : Set G) := by
  have hn : d.S ≤ normalizer ((d.Yplus ⊓ L : Subgroup G) : Set G) := by
    intro s hs x
    exact ⟨fun h => ⟨(hSY hs x).mp h.1, (hSL hs x).mp h.2⟩,
      fun h => ⟨(hSY hs x).mpr h.1, (hSL hs x).mpr h.2⟩⟩
  change d.S ≤ normalizer (Stellmacher.twoResidualAmbient (d.Yplus ⊓ L) : Set G)
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ _)

/-- Moving Q by Y_L lands in the intrinsic two-core of Y_L. -/
theorem core_YL_commutator_le [Finite G] (d : LocalData G) (L : Subgroup G)
    (hSQ : commutatorCore L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d L : Set G)) :
    ⁅commutatorCore L, YL d L⁆ ≤ (YL d L).pCoreIn 2 := by
  have hYL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hYQ : YL d L ≤ normalizer (commutatorCore L : Set G) :=
    hYL.trans (normalizer_commutator_ge_right _ _)
  exact le_pCoreIn_of_normalizes
    (((L.isPGroup_pCoreIn 2).to_le (commutatorCore_le L)).to_le
      (le_normalizer_iff_commutator_le_left.mp hYQ))
    (le_normalizer_iff_commutator_le_right.mp (hSQ.trans hSYL))
    (normalizer_commutator_ge_right _ _)

/-- Full Y_L displacement gives Q ≤ O₂(Y_L), rather than assuming that bound. -/
theorem core_le_YL_core [Finite G] (d : LocalData G) (L : Subgroup G)
    (hSQ : commutatorCore L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hfull : ⁅commutatorCore L, YL d L⁆ = commutatorCore L) :
    commutatorCore L ≤ (YL d L).pCoreIn 2 := by
  rw [← hfull]
  exact core_YL_commutator_le d L hSQ hSYL

/-- Exchange carries the core of Y_L onto the core of Y_C. -/
theorem conjugate_YL_core (d : LocalData G) (L : Subgroup G) (t : G)
    (hexchange : (YL d L).conjBy t = YC d L) :
    ((YL d L).pCoreIn 2).conjBy t = (YC d L).pCoreIn 2 := by
  change ((YL d L).pCoreIn 2).map (MulAut.conj t).toMonoidHom = _
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj t).injective]
  exact congrArg (fun H : Subgroup G => H.pCoreIn 2) hexchange

/-- The three-layer branch's group-theoretic conclusion, after its two
actual action calculations. -/
theorem conjugate_core_centralizes_of_full_action [Finite G] (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    (hSQ : commutatorCore c.L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hfull : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (hfix : YC d c.L ≤ centralizer (commutatorCore c.L : Set G))
    (t : G) (hexchange : (YL d c.L).conjBy t = YC d c.L) :
    (commutatorCore c.L).conjBy t ≤ centralizer (c.L : Set G) := by
  have h := map_mono (f := (MulAut.conj t).toMonoidHom)
    (core_le_YL_core d c.L hSQ hSYL hfull)
  change (commutatorCore c.L).conjBy t ≤ ((YL d c.L).pCoreIn 2).conjBy t at h
  rw [conjugate_YL_core d c.L t hexchange] at h
  exact h.trans (((YC d c.L).pCoreIn_le 2).trans (YC_centralizes_of_core_fixed d c hfix))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions

end
