module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.MovedCoordinates

/-!
# The rank-two natural module for the actual cubic image

Restriction to the last three coordinates identifies the moved plane with the
binary augmentation core on three letters. The displayed cubic restricts to
the standard three-cycle, giving an explicit isomorphism of actors with A₃
and an equivariant vector isomorphism. Its transitive action on the three
nonzero vectors proves irreducibility; those same vectors detect its kernel.
All computations are on the three-element actor and four-element module.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926,
and the odd-degree binary natural-module convention of §B.3, printed p.83.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.ResidualCoordinates
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _
local instance : DecidablePred (· ∈ core (Fin 3)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 3)) := Subtype.fintype _

private theorem tail_mem (x : Space) (hx : Multiplicative.ofAdd x ∈ moved) :
    (fun i : Fin 3 => x.val ⟨i.val + 2, by omega⟩) ∈ core (Fin 3) := by
  have hh : ∀ x : Space, x.val 0 = 0 → x.val 1 = 0 →
      (∑ i : Fin 3, x.val ⟨i.val + 2, by omega⟩) = 0 := by decide +kernel
  exact hh x hx.1 hx.2

private theorem head_mem (x : core (Fin 3)) :
    ![0, 0, x.val 0, x.val 1, x.val 2] ∈ core (Fin 5) := by
  have hh : ∀ x : core (Fin 3), (∑ i : Fin 5, ![0, 0, x.val 0, x.val 1, x.val 2] i) = 0 := by decide +kernel
  exact hh x

/-- Restriction to the last three coordinates, with inverse obtained by
adjoining two zero coordinates. -/
def movedCoreEquiv : moved ≃* Multiplicative (core (Fin 3)) where
  toFun x := Multiplicative.ofAdd ⟨fun i => x.val.toAdd.val ⟨i.val + 2, by omega⟩,
    by exact tail_mem x.val.toAdd x.property⟩
  invFun x := ⟨Multiplicative.ofAdd ⟨![0, 0, x.toAdd.val 0, x.toAdd.val 1, x.toAdd.val 2],
    by exact head_mem x.toAdd⟩, rfl, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    fin_cases i
    · exact x.property.1.symm
    · exact x.property.2.symm
    · rfl
    · rfl
    · rfl
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl

def threeCycle : alternatingGroup (Fin 3) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

def cubicToThree (g : cubicGroup) : alternatingGroup (Fin 3) :=
  if g.val = 1 then 1 else if g.val = cubic then threeCycle else threeCycle ^ 2

private theorem cubicToThree_injective : Function.Injective cubicToThree := by
  intro g h he
  apply Subtype.ext
  rcases cubic_cases g.val g.property with hg | hg | hg <;>
    rcases cubic_cases h.val h.property with hh | hh | hh
  all_goals
    have e : cubicToThree g = cubicToThree h := he
    simp only [cubicToThree, hg, hh] at e
    first | exact hg.trans hh.symm | exfalso; revert e; decide +kernel

/-- Restriction of the displayed cubic to the last three letters. -/
def cubicThreeHom : cubicGroup →* alternatingGroup (Fin 3) where
  toFun := cubicToThree
  map_one' := by simp [cubicToThree]
  map_mul' g h := by
    rcases cubic_cases g.val g.property with hg | hg | hg <;>
      rcases cubic_cases h.val h.property with hh | hh | hh
    all_goals
      change (if g.val * h.val = 1 then 1 else if g.val * h.val = cubic then threeCycle else threeCycle ^ 2) = _
      simp only [cubicToThree, hg, hh]
      decide +kernel

/-- The actual cubic permutation subgroup identified with A₃. -/
noncomputable def cubicThreeEquiv : cubicGroup ≃* alternatingGroup (Fin 3) :=
  MulEquiv.ofBijective cubicThreeHom
    ⟨by exact cubicToThree_injective, by
      intro g
      have hh : ∀ g : alternatingGroup (Fin 3), g = 1 ∨ g = threeCycle ∨ g = threeCycle ^ 2 := by decide +kernel
      rcases hh g with rfl | rfl | rfl
      · exact ⟨1, by decide +kernel⟩
      · exact ⟨⟨cubic, cubic_mem⟩, by decide +kernel⟩
      · exact ⟨⟨cubic ^ 2, cubicGroup.pow_mem cubic_mem 2⟩, by decide +kernel⟩⟩

theorem act_mem_moved (g : cubicGroup) (x : moved) :
    Multiplicative.ofAdd (act g.val x.val.toAdd) ∈ moved := by
  have hd := moved.mul_mem (difference_mem g x.val.toAdd) x.property
  change Multiplicative.ofAdd (act g.val x.val.toAdd - x.val.toAdd + x.val.toAdd) ∈ moved at hd
  simpa only [sub_add_cancel] using hd

def movedAction (g : cubicGroup) (x : moved) : moved :=
  ⟨Multiplicative.ofAdd (act g.val x.val.toAdd), act_mem_moved g x⟩

theorem movedCoreEquiv_equivariant (g : cubicGroup) (x : moved) :
    movedCoreEquiv (movedAction g x) = Multiplicative.ofAdd
      (coreRepresentation (Fin 3) (cubicThreeEquiv g).val (movedCoreEquiv x).toAdd) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext i
  rcases cubic_cases g.val g.property with hg | hg | hg
  all_goals
    change x.val.toAdd.val (g.val.val.symm ⟨i.val + 2, by omega⟩) =
      x.val.toAdd.val ⟨((cubicToThree g).val.symm i).val + 2, by omega⟩
    simp only [cubicToThree, hg]
    fin_cases i <;> rfl

/-- The binary core action, in the multiplicative notation used by the ambient subgroup. -/
noncomputable def threeAction : alternatingGroup (Fin 3) →* MulAut (Multiplicative (core (Fin 3))) where
  toFun g := (LinearEquiv.ofBijective (coreRepresentation (Fin 3) g.val)
    ((coreRepresentation (Fin 3)).apply_bijective g.val)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro x
    change Multiplicative.ofAdd (coreRepresentation (Fin 3) 1 x.toAdd) = x
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    change Multiplicative.ofAdd (coreRepresentation (Fin 3) (g.val * h.val) x.toAdd) =
      Multiplicative.ofAdd (coreRepresentation (Fin 3) g.val
        (coreRepresentation (Fin 3) h.val x.toAdd))
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem threeAction_apply (g : alternatingGroup (Fin 3))
    (x : Multiplicative (core (Fin 3))) :
    threeAction g x = Multiplicative.ofAdd (coreRepresentation (Fin 3) g.val x.toAdd) := rfl

/-- Faithfulness tested on the actual four vectors. -/
theorem three_faithful (g : alternatingGroup (Fin 3))
    (hg : ∀ x : core (Fin 3), coreRepresentation (Fin 3) g.val x = x) : g = 1 := by
  have hh : ∀ g : alternatingGroup (Fin 3),
      (∀ x : core (Fin 3), coreRepresentation (Fin 3) g.val x = x) → g = 1 := by decide +kernel
  exact hh g hg

theorem threeAction_injective : Function.Injective threeAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply three_faithful g
  intro x
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hg (Multiplicative.ofAdd x))

/-- A₃ is transitive on the three nonzero vectors of its binary core. -/
theorem three_nonzero_transitive (x y : core (Fin 3)) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : alternatingGroup (Fin 3), coreRepresentation (Fin 3) g.val x = y := by
  have hh : ∀ x y : core (Fin 3), x ≠ 0 → y ≠ 0 →
      ∃ g : alternatingGroup (Fin 3), coreRepresentation (Fin 3) g.val x = y := by decide +kernel
  exact hh x y hx hy

/-- Irreducibility stated for additive subgroups, hence also for binary submodules. -/
theorem three_irreducible (H : Subgroup (Multiplicative (core (Fin 3))))
    (hH : ∀ g : alternatingGroup (Fin 3), ∀ x ∈ H,
      Multiplicative.ofAdd (coreRepresentation (Fin 3) g.val x.toAdd) ∈ H) : H = ⊥ ∨ H = ⊤ := by
  by_cases hb : H = ⊥
  · exact Or.inl hb
  right
  obtain ⟨x, hxne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
  apply top_unique
  intro y _
  by_cases hy : y = 1
  · exact hy ▸ H.one_mem
  have hx0 : x.val.toAdd ≠ 0 := fun h => hxne (Subtype.ext h)
  have hy0 : y.toAdd ≠ 0 := hy
  obtain ⟨g, hg⟩ := three_nonzero_transitive x.val.toAdd y.toAdd hx0 hy0
  change Multiplicative.ofAdd y.toAdd ∈ H
  rw [← hg]
  exact hH g x x.property

theorem three_rank : Module.finrank (ZMod 2) (core (Fin 3)) = 2 := by
  rw [finrank_core]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.ResidualCoordinates
