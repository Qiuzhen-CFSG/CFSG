module

public import Theory.Representation.AlternatingSevenBinarySmallModels
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

/-!
# Fixed vectors for index-seven subgroups of A₇ in small binary modules

Every equivariant family of seven vectors in a binary module of dimension
at most five is constant: the augmentation core on seven letters is an
irreducible six-space, so its map to the given module must vanish.
For an arbitrary subgroup of order 360, its seven cosets carry the standard
alternating action up to an automorphism of A₇. A fixed vector extends to
this coset family and therefore is fixed by the whole group.

This is the small-orbit input for the normal A₆ upper-component argument
in Aschbacher–Smith 13.3.2. The augmentation module is the original binary
permutation module of B.3.1; no subgroup conjugacy or module classification
is assumed.
-/

public section
open Representation BinaryPermutation Subgroup
namespace Representation.BinaryAlternatingSevenSmallOrbit

private abbrev A7 := alternatingGroup (Fin 7)

private theorem seven_point_action
    {O : Type*} [Finite O] [MulAction A7 O] [MulAction.IsPretransitive A7 O]
    (hO : Nat.card O = 7) :
    ∃ (e : O ≃ Fin 7) (a : A7 ≃* A7),
      ∀ (g : A7) (o : O), e (g • o) = (a g).val (e o) := by
  classical
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  let : Nontrivial O := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  let e : O ≃ Fin 7 := Finite.equivFinOfCardEq hO
  let f : A7 →* Equiv.Perm (Fin 7) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom A7 O)
  have hf_apply (g : A7) (o : O) : f g (e o) = e (g • o) := by
    simp [f, Equiv.permCongrHom]
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact hk
    · obtain ⟨x, y, hxy⟩ := exists_pair_ne O
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 x y
      have hg1 : f g = 1 := hk.ge (mem_top g)
      have he : e y = e x := by
        rw [← hg, ← hf_apply, hg1]
        rfl
      exact (hxy (e.injective he).symm).elim
  have hr : Nat.card f.range = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    change Nat.card (alternatingGroup (Fin 7)) = 2520
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hi : f.range.index = 2 := by
    have h := f.range.index_mul_card
    rw [hr, Nat.card_perm, Nat.card_fin] at h
    norm_num [Nat.factorial] at h
    omega
  let a : A7 ≃* A7 :=
    (MonoidHom.ofInjective hf).trans
      (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))
  refine ⟨e, a, fun g o => ?_⟩
  change e (g • o) = f g (e o)
  exact (hf_apply g o).symm

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

private theorem equivariant_values_equal
    (ρ : Representation (ZMod 2) A7 W) (hdim : Module.finrank (ZMod 2) W ≤ 5)
    (value : Fin 7 → W)
    (hvalue : ∀ (g : A7) (i : Fin 7), value (g.val i) = ρ g (value i)) :
    ∀ i j, value i = value j := by
  classical
  let f : IntertwiningMap (alternatingCoreRepresentation (Fin 7)) ρ := {
    toLinearMap := {
      toFun := fun a => ∑ i : Fin 7, a.val i • value i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ i : Fin 7, a.val (g.val.symm i) • value i) =
        ρ g (∑ i : Fin 7, a.val i • value i)
      rw [map_sum]
      simp only [map_smul, ← hvalue]
      exact (Equiv.sum_comp g.val
        (fun i => a.val (g.val.symm i) • value i)).symm.trans (by simp) }
  let : (alternatingCoreRepresentation (Fin 7)).IsIrreducible :=
    AlternatingSevenBinarySmallModels.core_irreducible
  have hf : f = 0 := by
    rcases IsIrreducible.injective_or_eq_zero f with hi | hz
    · have hd := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hi
      rw [finrank_core] at hd
      simp only [Fintype.card_fin] at hd
      omega
    · exact hz
  intro i j
  let w : core (Fin 7) := ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
  have hz : value i + value j = 0 := by
    have hh := congrArg
      (fun f : IntertwiningMap (alternatingCoreRepresentation (Fin 7)) ρ => f w) hf
    change (∑ k : Fin 7, ((Pi.single i 1 : Fin 7 → ZMod 2) k +
      (Pi.single j 1 : Fin 7 → ZMod 2) k) • value k) = 0 at hh
    simpa [add_smul, Finset.sum_add_distrib] using hh
  have h := congrArg (fun z : W => z + value j) hz
  have hself : value j + value j = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  simpa only [add_assoc, hself, add_zero, zero_add] using h

private theorem fixed_of_coset_coordinates
    (ρ : Representation (ZMod 2) A7 W) (hdim : Module.finrank (ZMod 2) W ≤ 5)
    (B : Subgroup A7) (e : (A7 ⧸ B) ≃ Fin 7) (a : A7 ≃* A7)
    (he : ∀ (g : A7) (o : A7 ⧸ B), e (g • o) = (a g).val (e o))
    (v : W) (hv : ∀ b : B, ρ b.val v = v) : ∀ g, ρ g v = v := by
  classical
  let value : A7 ⧸ B → W := Quotient.lift (fun g : A7 => ρ g v) (by
    intro g h hrel
    have hh := congrArg (ρ g) (hv ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hrel⟩)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using hh.symm)
  have hvalue (g : A7) (x : A7 ⧸ B) : value (g • x) = ρ g (value x) := by
    induction x using QuotientGroup.induction_on with
    | H h => exact LinearMap.congr_fun (ρ.map_mul g h) v
  let σ := ρ.comp a.symm.toMonoidHom
  let label : Fin 7 → W := fun i => value (e.symm i)
  have hlabel (g : A7) (i : Fin 7) : label (g.val i) = σ g (label i) := by
    have hi : e.symm (g.val i) = a.symm g • e.symm i := by
      apply e.injective
      rw [e.apply_symm_apply, he, a.apply_symm_apply, e.apply_symm_apply]
    change value (e.symm (g.val i)) = ρ (a.symm g) (value (e.symm i))
    rw [hi, hvalue]
  have hall := equivariant_values_equal σ hdim label hlabel
  intro g
  have h := hall (e (QuotientGroup.mk g)) (e (QuotientGroup.mk 1))
  change value (e.symm (e (QuotientGroup.mk g))) =
    value (e.symm (e (QuotientGroup.mk 1))) at h
  rw [e.symm_apply_apply, e.symm_apply_apply] at h
  change ρ g v = ρ 1 v at h
  simpa only [map_one, Module.End.one_apply] using h

/-- An arbitrary subgroup of A₇ of order 360 fixes exactly the global fixed
vectors in every binary representation of dimension at most five. -/
theorem fixed_of_card_subgroup
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W)
    (hdim : Module.finrank (ZMod 2) W ≤ 5)
    (B : Subgroup (alternatingGroup (Fin 7))) (hB : Nat.card B = 360)
    (v : W) (hv : ∀ b : B, ρ b.val v = v) : ∀ g, ρ g v = v := by
  have hO : Nat.card (A7 ⧸ B) = 7 := by
    have h := B.index_mul_card
    rw [hB, Subgroup.index_eq_card] at h
    have hA : Nat.card A7 = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hA] at h
    change Nat.card (A7 ⧸ B) * 360 = 2520 at h
    omega
  obtain ⟨e, a, he⟩ := seven_point_action hO
  exact fixed_of_coset_coordinates ρ hdim B e a he v hv

end Representation.BinaryAlternatingSevenSmallOrbit
