module

public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum

/-!
# The A₄ invariant-plane obstruction in the binary A₅ module

The point stabilizer has one nonzero fixed word in the even-weight core.
Every other nonzero word has at least four translates, which together with
zero cannot lie in a subgroup of order four. Finite tests below are checked
by kernel reduction. They enumerate only the explicit permutation action.

The core is equivariantly isomorphic to the natural section in odd degree.
Sylow conjugacy transports both the actor and the candidate subgroup, giving
the obstruction for every Sylow normalizer without choosing a new action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.12,
printed p.124, and the A₅ exclusion in 15.3.30, printed p.1131.
-/

@[expose] public section

open Subgroup Equiv
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.AlternatingFive.Permutation
local notation "A5" => alternatingGroup (Fin 5)
private abbrev V4 := Multiplicative (ZMod 2 × ZMod 2)
private def r : A5 := ⟨swap 0 1 * swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def s : A5 := ⟨swap 0 2 * swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def t : A5 := ⟨swap 0 1 * swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def fourEmbedding : V4 →* A5 where
  toFun i := r ^ i.toAdd.1.val * s ^ i.toAdd.2.val
  map_one' := rfl
  map_mul' := by decide +kernel
private theorem fourEmbedding_injective : Function.Injective fourEmbedding := by decide +kernel
private def four : Subgroup A5 := fourEmbedding.range
private theorem four_card : Nat.card four = 4 := by
  rw [four, ← Nat.card_congr (MonoidHom.ofInjective fourEmbedding_injective).toEquiv]
  simp [V4]
private def sylow : Sylow 2 A5 := Sylow.ofCard four (by
  rw [four_card, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  decide +kernel)
/-- The subgroup of A₅ fixing the fifth letter, an A₄. -/
def pointStabilizer : Subgroup A5 := MulAction.stabilizer A5 (4 : Fin 5)
private theorem normalizer_test : ∀ g : A5,
    (∀ i : V4, ∃ j : V4, fourEmbedding j = g * fourEmbedding i * g⁻¹) ↔
      (g : Perm (Fin 5)) 4 = 4 := by
  decide +kernel
private theorem normalizer_four : normalizer (four : Set A5) = pointStabilizer := by
  apply le_antisymm
  · intro g hg
    apply (normalizer_test g).mp
    intro i
    exact (hg _).mp ⟨i, rfl⟩
  · apply le_normalizer_iff.mpr
    rintro g hg x ⟨i, rfl⟩
    exact (normalizer_test g).mpr hg i
private def words (i : V4 × Fin 3) : A5 := fourEmbedding i.1 * t ^ i.2.val
private theorem words_mem (i : V4 × Fin 3) : words i ∈ pointStabilizer := by
  change (words i).val 4 = 4
  revert i
  decide +kernel
private def line : BinaryPermutation.Full (Fin 5) := ![1, 1, 1, 1, 0]
private def orbitSet (v : BinaryPermutation.Full (Fin 5)) : Finset (BinaryPermutation.Full (Fin 5)) :=
  Finset.univ.image (fun i : V4 × Fin 3 => BinaryPermutation.representation (Fin 5) (words i) v)
private theorem orbit_card : ∀ v : BinaryPermutation.Full (Fin 5),
    (∑ i, v i) = 0 → v ≠ 0 → v ≠ line → 4 ≤ (orbitSet v).card := by
  decide +kernel
private theorem no_four_core (P : AddSubgroup (BinaryPermutation.core (Fin 5)))
    (hP : Nat.card P = 4)
    (hinv : ∀ a ∈ pointStabilizer, ∀ v ∈ P,
      BinaryPermutation.coreRepresentation (Fin 5) a v ∈ P) : False := by
  classical
  have hsmall (v : BinaryPermutation.core (Fin 5)) (hv : v ∈ P) :
      (v : BinaryPermutation.Full (Fin 5)) = 0 ∨ (v : BinaryPermutation.Full (Fin 5)) = line := by
    by_contra hn
    push Not at hn
    have hc := orbit_card v v.property hn.1 hn.2
    have hzero : (0 : BinaryPermutation.Full (Fin 5)) ∉ orbitSet v := by
      rintro hz
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      apply hn.1
      have he := congrArg (fun w => BinaryPermutation.representation (Fin 5) ((words i)⁻¹) w) hi
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, map_zero] using he
    let f : {x // x ∈ insert 0 (orbitSet v)} → P := fun x =>
      if hx : x.val = 0 then ⟨0, P.zero_mem⟩ else
      ⟨⟨x.val, by
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_insert.mp x.property).resolve_left hx)
          rw [← hi]
          exact BinaryPermutation.core_invariant (Fin 5) _ v.property⟩, by
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((Finset.mem_insert.mp x.property).resolve_left hx)
        have h := hinv (words i) (words_mem i) v hv
        convert h using 1
        exact Subtype.ext hi.symm⟩
    have hf (x : {x // x ∈ insert 0 (orbitSet v)}) :
        ((f x : BinaryPermutation.core (Fin 5)) : BinaryPermutation.Full (Fin 5)) = x.val := by
      dsimp [f]
      split_ifs with h
      · exact h.symm
      · rfl
    have hfi : Function.Injective f := by
      intro x y he
      apply Subtype.ext
      exact (hf x).symm.trans ((congrArg
        (fun z : P => ((z : BinaryPermutation.core (Fin 5)) : BinaryPermutation.Full (Fin 5)))
        he).trans (hf y))
    have hbound := Nat.card_le_card_of_injective f hfi
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_insert_of_notMem hzero, hP] at hbound
    omega
  let f : P → ZMod 2 := fun v => v.val.val 0
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    rcases hsmall x x.property with hx | hx <;>
      rcases hsmall y y.property with hy | hy
    · exact hx.trans hy.symm
    · exfalso
      change x.val.val 0 = y.val.val 0 at hxy
      rw [hx, hy] at hxy
      exact zero_ne_one hxy
    · exfalso
      change x.val.val 0 = y.val.val 0 at hxy
      rw [hx, hy] at hxy
      exact one_ne_zero hxy
    · exact hx.trans hy.symm
  have hc := Nat.card_le_card_of_injective f hf
  rw [hP] at hc
  norm_num at hc

/-- Every Sylow normalizer is an actual conjugate of the degree-five point stabilizer. -/
theorem sylowNormalizer_is_pointStabilizer (Q : Sylow 2 A5) :
    ∃ g : A5, pointStabilizer.map (MulAut.conj g).toMonoidHom =
      normalizer (Q : Set A5) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 sylow Q
  have hQ : four.map (MulAut.conj g).toMonoidHom = (Q : Subgroup A5) :=
    congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_⟩
  rw [← normalizer_four, map_equiv_normalizer_eq, hQ]
  rfl

private theorem no_four_core_normalizer (Q : Sylow 2 A5)
    (P : AddSubgroup (BinaryPermutation.core (Fin 5))) (hP : Nat.card P = 4)
    (hinv : ∀ a ∈ normalizer (Q : Set A5), ∀ v ∈ P,
      BinaryPermutation.coreRepresentation (Fin 5) a.val v ∈ P) : False := by
  obtain ⟨g, hN⟩ := sylowNormalizer_is_pointStabilizer Q
  let pi := BinaryPermutation.coreRepresentation (Fin 5)
  have hi : Function.Injective (pi g⁻¹.val) := by
    intro x y he
    have hh := congrArg (pi g.val) he
    simpa only [Subgroup.coe_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using hh
  let R := P.map (pi g⁻¹.val).toAddMonoidHom
  apply no_four_core R ((AddSubgroup.card_map_of_injective hi).trans hP)
  rintro a ha v ⟨w, hw, rfl⟩
  have hmem : g * a * g⁻¹ ∈ normalizer (Q : Set A5) := by
    rw [← hN]
    exact mem_map_of_mem _ ha
  refine ⟨pi (g * a * g⁻¹).val w, hinv _ hmem w hw, ?_⟩
  change pi g⁻¹.val (pi (g * a * g⁻¹).val w) = pi a.val (pi g⁻¹.val w)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  simp [mul_assoc]

/-- The natural binary A₅-module has no subgroup of order four invariant
under a Sylow two-normalizer. The odd-degree core-to-natural equivalence
retains the coordinate permutation action throughout. -/
theorem no_four_natural_normalizer (Q : Sylow 2 A5)
    (P : Subgroup (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (hP : Nat.card P = 4)
    (hinv : ∀ a ∈ normalizer (Q : Set A5), ∀ v ∈ P,
      Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 5) a.val v.toAdd)
        ∈ P) : False := by
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let R := P.toAddSubgroup'.map e.symm.toAddEquiv.toAddMonoidHom
  apply no_four_core_normalizer Q R
  · exact (AddSubgroup.card_map_of_injective e.symm.injective).trans hP
  · rintro a ha v ⟨w, hw, rfl⟩
    refine ⟨BinaryPermutation.naturalRepresentation (Fin 5) a.val w,
      hinv a ha w hw, ?_⟩
    apply e.injective
    change e (e.symm (BinaryPermutation.naturalRepresentation (Fin 5) a.val w)) =
      e (BinaryPermutation.coreRepresentation (Fin 5) a.val (e.symm w))
    rw [e.apply_symm_apply]
    symm
    have he : e (BinaryPermutation.coreRepresentation (Fin 5) a.val (e.symm w)) =
        BinaryPermutation.naturalRepresentation (Fin 5) a.val (e (e.symm w)) :=
      BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) a.val (e.symm w)
    simpa only [e.apply_symm_apply] using he
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.AlternatingFive.Permutation

end
