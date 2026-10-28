module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

/-!
# The two-core of the four-plus-three partition stabilizer

The action is the actual block action of `S₄ × S₃` on seven points.
Surjective projection sends its two-core into the two-cores of the factors:
the second is trivial and the first is the even Klein four group. Therefore
its ambient image contains no transpositions. Normality and two-cores here
are intrinsic to the partition stabilizer, not to the whole symmetric group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
abbrev S7 := Perm (Fin 7)
abbrev FourThree := Perm (Fin 4) × Perm (Fin 3)

-- The genuine action on two blocks of lengths four and three.
def fourThreeHom : FourThree →* S7 :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7)).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom _ _)

def fourThreeStabilizer : Subgroup S7 := fourThreeHom.range

theorem fourThreeHom_injective : Function.Injective fourThreeHom :=
  (Equiv.permCongrHom _).injective.comp Equiv.Perm.sumCongrHom_injective

noncomputable def fourThreeEquiv : FourThree ≃* fourThreeStabilizer :=
  MulEquiv.ofBijective fourThreeHom.rangeRestrict
    ⟨fun _ _ h => fourThreeHom_injective (congrArg Subtype.val h),
      fourThreeHom.rangeRestrict_surjective⟩

private theorem pCore_map_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) : (pCore 2 G).map f ≤ pCore 2 H :=
  le_sSup ⟨(inferInstance : (pCore 2 G).Normal).map f hf, pCore_isPGroup.map f⟩

private theorem three_twoCore : pCore 2 (Perm (Fin 3)) = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three
    (MonoidHom.id (Perm (Fin 3))) Function.surjective_id
    (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
  simpa only [MonoidHom.ker_id] using h.symm

private theorem product_core_even (x : FourThree) (hx : x ∈ pCore 2 FourThree) :
    x.1.sign = 1 ∧ x.2 = 1 := by
  have hf := pCore_map_le (MonoidHom.fst (Perm (Fin 4)) (Perm (Fin 3)))
    (fun y => ⟨(y, 1), rfl⟩) (mem_map_of_mem _ hx)
  have hs := pCore_map_le (MonoidHom.snd (Perm (Fin 4)) (Perm (Fin 3)))
    (fun y => ⟨(1, y), rfl⟩) (mem_map_of_mem _ hx)
  rw [three_twoCore] at hs
  refine ⟨?_, hs⟩
  rw [← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq] at hf
  exact (Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff x.1).mp hf |>.1

-- The intrinsic core is mapped to its correct ambient seven-point action.
theorem fourThreeCore_even (g : fourThreeStabilizer)
    (hg : g ∈ pCore 2 fourThreeStabilizer) : g.val.sign = 1 := by
  rw [← pCore_map_iso 2 fourThreeEquiv] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨hf, hs⟩ := product_core_even x hx
  change (finSumFinEquiv.permCongr (Equiv.sumCongr x.1 x.2)).sign = 1
  rw [Perm.sign_permCongr, Perm.sign_sumCongr, hf, hs, map_one, mul_one]

theorem fourThreeCore_no_swap (g : fourThreeStabilizer)
    (hg : g ∈ pCore 2 fourThreeStabilizer) : ¬ g.val.IsSwap := by
  intro ht
  have h := (fourThreeCore_even g hg).symm.trans ht.sign_eq
  norm_num at h
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
