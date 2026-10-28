module
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Binary simple degrees of A₆ through dimension six

A simple quotient of the six-letter binary permutation module is trivial:
its invariant subspaces form the chain zero, constants, augmentation core,
and the full module. Any transitive six-point action of A₆ is identified
with the actual alternating group on those six points by its faithful
permutation action and index two in the symmetric group. Thus an equivariant
six-point set containing a nonzero vector also has one-dimensional simple span.

For a simple module of dimension greater than one, the small-index subgroup
bound now makes every nonzero orbit length divisible by five or equal to 36.
Summing the orbit lengths gives `2^d - 1 = 5*a + 36*b`. For `1 < d ≤ 6`,
this leaves only `d = 4`. Faithfulness and semisimplicity of restrictions
are not assumed, and no representation catalogue is used.

This supplies the point-stabilizer degree input for the A₇ six-space in
Aschbacher–Smith K.1.2, printed p.452 (PDF p.463). The permutation-module
structure is the elementary structure theorem of §B.3.
-/

public section
namespace AlternatingSix.BinarySmallDegrees
open Representation
local notation "A6" => alternatingGroup (Fin 6)

private theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private noncomputable def sixActionEquiv {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    [MulAction A6 Ω] [MulAction.IsPretransitive A6 Ω] (hc : Fintype.card Ω = 6) :
    A6 ≃* alternatingGroup Ω := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let f := MulAction.toPermHom A6 Ω
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    rcases (MonoidHom.normal_ker f).eq_bot_or_eq_top with h | h
    · exact h
    have hs : Subsingleton Ω := ⟨by
      intro x y
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A6 x y
      have ht : f g = 1 := show g ∈ f.ker from h ▸ Subgroup.mem_top g
      have he := congrArg (fun p : Equiv.Perm Ω => p x) ht
      exact he.symm.trans hg⟩
    let := hs
    have hb : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega
  have hr : Nat.card f.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans card_A6
  have hi : f.range.index = 2 := by
    have h := f.range.index_mul_card
    rw [hr, Nat.card_perm, Nat.card_eq_fintype_card, hc] at h
    norm_num [Nat.factorial] at h
    omega
  exact (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))

private theorem sixActionEquiv_apply {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    [MulAction A6 Ω] [MulAction.IsPretransitive A6 Ω] (hc : Fintype.card Ω = 6)
    (g : A6) (i : Ω) : (sixActionEquiv hc g).val i = g • i := by
  simp [sixActionEquiv, MonoidHom.ofInjective_apply, MulAction.toPermHom_apply]

/-- An equivariant image of a transitive six-set in a simple binary module
spans a one-dimensional module whenever the image contains a nonzero vector. -/
theorem finrank_eq_one_of_six_set {Ω W : Type*} [Fintype Ω] [DecidableEq Ω]
    [MulAction A6 Ω] [MulAction.IsPretransitive A6 Ω]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hc : Fintype.card Ω = 6) (ρ : Representation (ZMod 2) A6 W) [ρ.IsIrreducible]
    (v : Ω → W) (hv : ∀ (g : A6) (i : Ω), v (g • i) = ρ g (v i))
    (hn : ∃ i, v i ≠ 0) : Module.finrank (ZMod 2) W = 1 := by
  classical
  let : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  let e := sixActionEquiv hc
  let σ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective ρ).mpr inferInstance
  have he (g : alternatingGroup Ω) (i : Ω) : e.symm g • i = g.val i := by
    rw [← sixActionEquiv_apply hc]
    exact congrArg (fun p : alternatingGroup Ω => p.val i) (e.apply_symm_apply g)
  have hv' (g : alternatingGroup Ω) (i : Ω) : v (g.val i) = σ g (v i) := by
    rw [← he]
    exact hv (e.symm g) i
  let f : (BinaryPermutation.alternatingRepresentation Ω).IntertwiningMap σ := {
    toLinearMap := {
      toFun a := ∑ i : Ω, a i • v i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ i : Ω, a (g.val.symm i) • v i) = σ g (∑ i : Ω, a i • v i)
      rw [map_sum]
      simp only [map_smul, ← hv']
      exact (Equiv.sum_comp g.val (fun i => a (g.val.symm i) • v i)).symm.trans (by
        simp only [Equiv.symm_apply_apply]) }
  have hf : f ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hn
    apply hi
    have heq := congrArg (fun t => t (Pi.single i 1)) hz
    change (∑ j : Ω, (Pi.single i (1 : ZMod 2) : Ω → ZMod 2) j • v j) = 0 at heq
    simpa using heq
  have hsur := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hmax := SimpleHeadQuotient.isCoatom_ker_of_surjective f hsur
  have hchain := BinaryPermutation.alternating_chiefSeries_strict
    (show 5 ≤ Fintype.card Ω by omega) (show Even (Fintype.card Ω) by rw [hc]; decide)
  have hk : f.ker = BinaryPermutation.coreSubrepresentation := by
    rcases BinaryPermutation.alternating_subrepresentation_classification
      (show 5 ≤ Fintype.card Ω by omega) f.ker with h | h | h | h
    · have hh := hmax.2 BinaryPermutation.constantsSubrepresentation (h ▸ hchain.1)
      exact ((ne_of_lt (hchain.2.1.trans hchain.2.2)) hh).elim
    · have hh := hmax.2 BinaryPermutation.coreSubrepresentation (h ▸ hchain.2.1)
      exact (hchain.2.2.ne hh).elim
    · exact h
    · exact (hmax.1 h).elim
  have hr := f.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsur, finrank_top, BinaryPermutation.finrank_full, hc] at hr
  have hker := congrArg Subrepresentation.toSubmodule hk
  change LinearMap.ker f.toLinearMap = BinaryPermutation.core Ω at hker
  rw [hker, BinaryPermutation.finrank_core, hc] at hr
  omega
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) W] in
private theorem finrank_eq_one_of_fixed (ρ : Representation (ZMod 2) A6 W)
    [ρ.IsIrreducible] (v : W) (hne : v ≠ 0) (hv : ∀ g, ρ g v = v) :
    Module.finrank (ZMod 2) W = 1 := by
  let S : Subrepresentation ρ := {
    toSubmodule := Submodule.span (ZMod 2) {v}
    apply_mem_toSubmodule := by
      intro g w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hv]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v)) }
  have hn : S ≠ ⊥ := by
    intro he
    have hm : v ∈ S := Submodule.subset_span (Set.mem_singleton v)
    rw [he] at hm
    exact hne hm
  have ht : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hn
  have hd : Module.finrank (ZMod 2) S.toSubmodule = 1 := finrank_span_singleton hne
  rw [congrArg Subrepresentation.toSubmodule ht] at hd
  exact (finrank_top (R := ZMod 2) (M := W)) ▸ hd

private abbrev nonzeroAction (ρ : Representation (ZMod 2) A6 W) :
    MulAction A6 {w : W // w ≠ 0} where
  smul g w := ⟨ρ g w.val, by
    intro hz
    apply w.property
    simpa only [ρ.inv_self_apply, map_zero] using congrArg (ρ g⁻¹) hz⟩
  one_smul w := Subtype.ext (by change ρ 1 w.val = w.val; simp)
  mul_smul g h w := Subtype.ext (by
    change ρ (g * h) w.val = ρ g (ρ h w.val)
    simp [Module.End.mul_apply])

/-- Nontrivial simple modules of dimension at most six have only nonzero
orbits whose lengths are divisible by five or equal to thirty-six. -/
private theorem nonzero_orbits (ρ : Representation (ZMod 2) A6 W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W ≤ 6) (hd1 : Module.finrank (ZMod 2) W ≠ 1) :
    letI := nonzeroAction ρ
    ∀ x : {w : W // w ≠ 0}, 5 ∣ Nat.card (MulAction.orbit A6 x) ∨
      Nat.card (MulAction.orbit A6 x) = 36 := by
  classical
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Fintype W := Fintype.ofFinite W
  let := nonzeroAction ρ
  intro x
  let H := MulAction.stabilizer A6 x
  have hi : H.index = Nat.card (MulAction.orbit A6 x) := MulAction.index_stabilizer A6 x
  have hxcard : Nat.card {w : W // w ≠ 0} = 2 ^ Module.finrank (ZMod 2) W - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_unique (α := {w : W // w = 0}),
      Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hb : H.index ≤ 63 := by
    rw [hi]
    have hc := Nat.card_le_card_of_injective
      (Subtype.val : MulAction.orbit A6 x → {w : W // w ≠ 0}) Subtype.val_injective
    change Nat.card (MulAction.orbit A6 x) ≤ Nat.card {w : W // w ≠ 0} at hc
    rw [hxcard] at hc
    have hpow : 2 ^ Module.finrank (ZMod 2) W ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hd
    omega
  have hproper : H ≠ ⊤ := by
    intro ht
    apply hd1
    apply finrank_eq_one_of_fixed ρ x.val x.property
    intro g
    have hg : g ∈ H := ht ▸ Subgroup.mem_top g
    exact congrArg Subtype.val (show g • x = x from hg)
  rcases AlternatingSix.SmallIndex.index_divisible_by_five_or_six_or_thirtySix H hproper hb
      with h | h | h
  · exact Or.inl (hi ▸ h)
  · exfalso
    apply hd1
    let Ω := MulAction.orbit A6 x
    let : Fintype Ω := Fintype.ofFinite Ω
    apply finrank_eq_one_of_six_set
      (show Fintype.card Ω = 6 by simpa only [← Nat.card_eq_fintype_card] using hi.symm.trans h)
      ρ (fun z : Ω => z.val.val) (fun _ _ => rfl)
    exact ⟨⟨x, MulAction.mem_orbit_self x⟩, x.property⟩
  · exact Or.inr (hi ▸ h)

/-- Every binary simple A₆-module of dimension at most six has dimension
one or four; no faithfulness or ambient cubic hypothesis is required. -/
theorem finrank_eq_one_or_four (ρ : Representation (ZMod 2) A6 W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W ≤ 6) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 4 := by
  classical
  by_cases h1 : Module.finrank (ZMod 2) W = 1
  · exact Or.inl h1
  right
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have hpos : 0 < Module.finrank (ZMod 2) W := Module.finrank_pos
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Fintype W := Fintype.ofFinite W
  let X := {w : W // w ≠ 0}
  let := nonzeroAction ρ
  let Q := MulAction.orbitRel.Quotient A6 X
  let : Fintype Q := Fintype.ofFinite Q
  let : ∀ q : Q, Fintype (MulAction.orbit A6 q.out) := fun _ => Fintype.ofFinite _
  have hs : Nat.card X = ∑ q : Q, Nat.card (MulAction.orbit A6 q.out) := by
    have he := Nat.card_congr (MulAction.selfEquivSigmaOrbits A6 X)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using he
  have hex (q : Q) : ∃ a b : ℕ, Nat.card (MulAction.orbit A6 q.out) = 5 * a + 36 * b := by
    rcases nonzero_orbits ρ hd h1 q.out with ⟨a, ha⟩ | he
    · exact ⟨a, 0, by omega⟩
    · exact ⟨0, 1, by omega⟩
  choose a b hab using hex
  have heq : 2 ^ Module.finrank (ZMod 2) W - 1 =
      5 * (∑ q : Q, a q) + 36 * (∑ q : Q, b q) := by
    calc
      _ = Nat.card X := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_unique (α := {w : W // w = 0}),
          Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      _ = _ := hs
      _ = _ := by simp_rw [hab]; rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  interval_cases hn : Module.finrank (ZMod 2) W <;> norm_num at heq ⊢ <;> omega
end AlternatingSix.BinarySmallDegrees
