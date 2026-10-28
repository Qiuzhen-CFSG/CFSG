module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Three independent axes give the full binary three-space action

The full axis group in each coordinate direction contains its two elementary
transvections. These six root groups generate SL₃(2), which is the full
automorphism group of the elementary abelian group of order eight. The
result retains the literal ambient normalizer map. An explicit cubic in the
last two coordinates fixes the first axis pointwise.

Source: Aschbacher–Smith, proof of 14.7.70, printed pp.1073–1074.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
open Representation.OneCohomology.SLHigherNatural
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes.Linear

abbrev Model := Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.Model
abbrev standard (i : Fin 3) : Model := Multiplicative.ofAdd (Pi.single i 1)
def axis (i : Fin 3) : Subgroup Model := zpowers (standard i)

private theorem single_mem_axis (i : Fin 3) (a : ZMod 2) :
    Multiplicative.ofAdd (Pi.single i a) ∈ axis i := by
  have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases ha with rfl | rfl
  · rw [Pi.single_zero]
    exact (axis i).one_mem
  · exact mem_zpowers _

private theorem transvection_displacement (i j : Fin 3) (hij : i ≠ j) (a : ZMod 2)
    (v : Model) :
    slAut (SpecialLinearGroup.transvection hij a) v * v⁻¹ ∈ axis i := by
  have he : slAut (SpecialLinearGroup.transvection hij a) v * v⁻¹ =
      Multiplicative.ofAdd (Pi.single i (a * v.toAdd j)) := by
    apply Multiplicative.toAdd.injective
    change (slAut (SpecialLinearGroup.transvection hij a) v).toAdd + -v.toAdd = _
    rw [slAut_apply]
    change Representation.specialLinearNatural 3 (SpecialLinearGroup.transvection hij a) v.toAdd + -v.toAdd = _
    rw [action_transvection]
    rw [← sub_eq_add_neg, add_sub_cancel_left]
    rfl
  rw [he]
  exact single_mem_axis i _

private theorem fixes_axis_of_standard (f : MulAut Model) (i : Fin 3)
    (hf : f (standard i) = standard i) (v : Model) (hv : v ∈ axis i) : f v = v := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hv
  rw [map_zpow, hf]

private theorem transvection_fixes_axis (i j : Fin 3) (hij : i ≠ j) (a : ZMod 2)
    (v : Model) (hv : v ∈ axis i) :
    slAut (SpecialLinearGroup.transvection hij a) v = v := by
  apply fixes_axis_of_standard _ i ?_ v hv
  apply Multiplicative.toAdd.injective
  rw [slAut_apply]
  exact SpecialLinearGroup.transvection_smul_single_fst hij a

universe u
variable {G : Type u} [Group G] (A : Subgroup G) (e : Model ≃* A)
  (C : Subgroup G) (hn : C ≤ normalizer (A : Set G))
  (P : Fin 3 → Subgroup G)
  (hP : ∀ i, ((axis i).map e.toMonoidHom).map A.subtype = P i)

include hP in
private theorem realized_mem_range (i : Fin 3) (f : MulAut Model)
    (hd : ∀ x, f x * x⁻¹ ∈ axis i)
    (hf : ∀ x ∈ axis i, f x = x)
    (haxes : RealizesAxis A (P i) C) :
    MulAut.congr e f ∈ (A.normalizerMonoidHom.comp (inclusion hn)).range := by
  have hd' (x : A) : ((MulAut.congr e f) x : G) * (x : G)⁻¹ ∈ P i := by
    rw [← hP i]
    refine ⟨e (f (e.symm x) * (e.symm x)⁻¹), ?_, ?_⟩
    · exact ⟨_, hd _, rfl⟩
    · simp only [map_mul, map_inv, e.apply_symm_apply]
      rfl
  have hf' (x : A) (hx : (x : G) ∈ P i) : (MulAut.congr e f) x = x := by
    rw [← hP i] at hx
    obtain ⟨y, ⟨v, hv, he⟩, hy⟩ := hx
    have hy' : y = x := Subtype.ext hy
    have hx' : e v = x := he.trans hy'
    rw [← hx']
    change e (f (e.symm (e v))) = e v
    rw [e.symm_apply_apply, hf v hv]
  obtain ⟨q, hqC, hqA, hq⟩ := haxes (MulAut.congr e f) hd' hf'
  refine ⟨⟨q, hqC⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact hq x

include hP in
/-- Realization of all three independent axis groups gives every automorphism
of the literal original elementary abelian subgroup. -/
theorem full_action
    (haxes : ∀ i, RealizesAxis A (P i) C) :
    Function.Surjective (A.normalizerMonoidHom.comp (inclusion hn)) := by
  let H := (A.normalizerMonoidHom.comp (inclusion hn)).range
  have hall (g : Matrix.PSL3Two.SL) : MulAut.congr e (slAut g) ∈ H := by
    apply transvection_induction (fun g => MulAut.congr e (slAut g) ∈ H) ?_ ?_ g
    · intro i j hij a
      exact realized_mem_range A e C hn P hP i _
        (transvection_displacement i j hij a) (transvection_fixes_axis i j hij a) (haxes i)
    · intro g h hg hh
      simpa only [map_mul] using H.mul_mem hg hh
  intro f
  obtain ⟨g, rfl⟩ := (MulAut.congr e).surjective f
  obtain ⟨g, rfl⟩ := slAut.surjective g
  exact hall g

private def cubic : Matrix.PSL3Two.SL :=
  SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) 1 *
    SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1

private theorem cubic_order : orderOf cubic = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have he := congrArg (fun g : Matrix.PSL3Two.SL => g.val 1 1) h
    exact (by decide : (0 : ZMod 2) ≠ 1) he

private theorem cubic_fixes_axis (v : Model) (hv : v ∈ axis 0) : slAut cubic v = v := by
  apply fixes_axis_of_standard _ 0 ?_ v hv
  apply Multiplicative.toAdd.injective
  rw [slAut_apply]
  decide +kernel

include hP in
/-- A genuine cubic automorphism fixing the first marked axis pointwise. -/
theorem exists_cubic_fixing_first :
    ∃ f : MulAut A, orderOf f = 3 ∧ ∀ x : A, (x : G) ∈ P 0 → f x = x := by
  refine ⟨MulAut.congr e (slAut cubic), ?_, ?_⟩
  · exact (orderOf_injective (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective (slAut cubic)).trans
      ((orderOf_injective slAut.toMonoidHom slAut.injective cubic).trans cubic_order)
  · intro x hx
    rw [← hP 0] at hx
    obtain ⟨y, ⟨v, hv, he⟩, hy⟩ := hx
    have hx' : e v = x := he.trans (Subtype.ext hy)
    rw [← hx']
    change e (slAut cubic (e.symm (e v))) = e v
    rw [e.symm_apply_apply, cubic_fixes_axis v hv]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes.Linear
