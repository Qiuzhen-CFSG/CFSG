module

public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Mathlib.GroupTheory.IsPerfect

/-!
# Existence of irreducible sections for perfect actors

A finite-dimensional nontrivial action of a perfect subgroup has a member of
`Irr⁺`. Choose an invariant noncentral subspace of least dimension. If its
commutator subspace were central, its action image would be both abelian and
perfect, hence trivial. Minimality therefore makes the commutator the whole
subspace, and makes the literal quotient by fixed vectors irreducible.

This supplies the existence step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, B.1.11, printed p. 73, using Definition A.1.40. No
semisimplicity or irreducible-section witness is assumed.
-/

public section

open Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An invariant subspace contains its action commutators. -/
private theorem invariant_commutator_le (L : Subgroup G)
    (W : Submodule (ZMod 2) V) (hW : L ≤ subspaceStabilizer ρ W) :
    subspaceCommutator ρ W L ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, w, hw, rfl⟩
  exact W.sub_mem ((hW hl w).2 hw) hw

/-- Action commutators of an invariant subspace are invariant. -/
private theorem invariant_commutator_stable (L : Subgroup G)
    (W : Submodule (ZMod 2) V) (hW : L ≤ subspaceStabilizer ρ W) :
    L ≤ subspaceStabilizer ρ (subspaceCommutator ρ W L) := by
  apply le_subspaceStabilizer
  intro g hg w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, v, hv, rfl⟩ := hw
    have hmem := Submodule.subset_span (R := ZMod 2)
      (s := {w | ∃ l ∈ L, ∃ v ∈ W, w = ρ l v - v})
      (show ρ (g * l * g⁻¹) (ρ g v) - ρ g v ∈ _ from
        ⟨g * l * g⁻¹, L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg),
          ρ g v, (hW hg v).2 hv, rfl⟩)
    convert hmem using 1
    simp [map_mul, Module.End.mul_apply, subspaceCommutator]
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (subspaceCommutator ρ W L).add_mem ihx ihy
  | smul a x hx ih => simpa using (subspaceCommutator ρ W L).smul_mem a ih

/-- A perfect actor cannot act nontrivially with central action commutators. -/
theorem le_fixedSpace_of_commutator_le_fixedSpace (L : Subgroup G)
    [Group.IsPerfect L] (W : Submodule (ZMod 2) V)
    (hW : L ≤ subspaceStabilizer ρ W)
    (hC : subspaceCommutator ρ W L ≤ fixedSpace ρ L) : W ≤ fixedSpace ρ L := by
  let σ := (invariantSubspace ρ L W hW).toRepresentation
  let f := σ.asGroupHom
  have hc (x y : L) (v : W) : ρ x (ρ y v - v) = ρ y v - v :=
    hC (Submodule.subset_span ⟨y, y.property, v, v.property, rfl⟩) x
  let : IsMulCommutative f.range := ⟨⟨by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ x (ρ y v) = ρ y (ρ x v)
    have hxy := hc x y v
    have hyx := hc y x v
    rw [map_sub] at hxy hyx
    exact add_right_cancel ((sub_eq_sub_iff_add_eq_add.mp hxy).trans
      ((add_comm _ _).trans (sub_eq_sub_iff_add_eq_add.mp hyx).symm))⟩⟩
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have htriv (x : L) : f x = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨f x, x, rfl⟩ : f.range) 1)
  intro v hv x
  have h := congrArg (fun t => (t.val (⟨v, hv⟩ : W) : V)) (htriv x)
  exact h

/-- Every nontrivial finite-dimensional action of a perfect subgroup has an Irr⁺ section. -/
theorem exists_isIrrPlus_of_not_fixed [FiniteDimensional (ZMod 2) V]
    (L : Subgroup G) [Group.IsPerfect L] (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ L) :
    ∃ I, IsIrrPlus ρ L I := by
  classical
  let P : ℕ → Prop := fun n => ∃ W : Submodule (ZMod 2) V,
    (L ≤ subspaceStabilizer ρ W) ∧ ¬ W ≤ fixedSpace ρ L ∧ Module.finrank (ZMod 2) W = n
  have hp : ∃ n, P n := ⟨_, ⊤, le_subspaceStabilizer ρ ⊤ (by simp), hn, rfl⟩
  obtain ⟨I, hI, hnI, hdim⟩ := Nat.find_spec hp
  have hmin (J : Submodule (ZMod 2) V) (hJ : L ≤ subspaceStabilizer ρ J)
      (hJI : J ≤ I) (hnJ : ¬ J ≤ fixedSpace ρ L) : J = I := by
    apply eq_of_le_of_not_lt hJI
    intro hlt
    exact Nat.find_min hp (hdim ▸ Submodule.finrank_lt_finrank_of_lt hlt)
      ⟨J, hJ, hnJ, rfl⟩
  have hcomm : subspaceCommutator ρ I L = I :=
    hmin _ (invariant_commutator_stable ρ L I hI)
      (invariant_commutator_le ρ L I hI)
      (fun hc => hnI (le_fixedSpace_of_commutator_le_fixedSpace ρ L I hI hc))
  refine ⟨I, hI, hcomm, ?_⟩
  have hC : (fixedSpace ρ L).comap I.subtype ≠ ⊤ := by
    intro heq
    apply hnI
    intro v hv
    have hm : (⟨v, hv⟩ : I) ∈ (fixedSpace ρ L).comap I.subtype := by rw [heq]; trivial
    exact hm
  let : Nontrivial (centralQuotient ρ L I) := Submodule.Quotient.nontrivial_iff.mpr hC
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro S
  let q := ((fixedSpace ρ L).comap I.subtype).mkQ
  let J := (S.toSubmodule.comap q).map I.subtype
  have hJI : J ≤ I := Submodule.map_subtype_le _ _
  have hJ : L ≤ subspaceStabilizer ρ J := by
    apply le_subspaceStabilizer
    rintro g hg _ ⟨v, hv, rfl⟩
    refine ⟨⟨ρ g v, (hI hg v).2 v.property⟩, ?_, rfl⟩
    exact S.apply_mem_toSubmodule ⟨g, hg⟩ hv
  by_cases hfix : J ≤ fixedSpace ρ L
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ v
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact hfix ⟨w, hv, rfl⟩
  · right
    have hJIeq := hmin J hJ hJI hfix
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ v
    have hw : (w : V) ∈ J := by rw [hJIeq]; exact w.property
    obtain ⟨u, hu, heq⟩ := hw
    have hueq : u = w := Subtype.ext heq
    have huq : q u ∈ S := hu
    rw [hueq] at huq
    exact huq
/-- A faithful action supplies the nontriviality premise for every nontrivial
perfect subgroup. -/
theorem exists_isIrrPlus_of_faithful [FiniteDimensional (ZMod 2) V]
    (hfaith : Function.Injective ρ) (L : Subgroup G) [Group.IsPerfect L]
    (hL : L ≠ ⊥) : ∃ I, IsIrrPlus ρ L I := by
  apply exists_isIrrPlus_of_not_fixed ρ L
  intro hfix
  apply hL
  apply bot_unique
  intro l hl
  apply hfaith
  ext v
  simpa using hfix (show v ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top) ⟨l, hl⟩

end Representation.BinaryOffender
