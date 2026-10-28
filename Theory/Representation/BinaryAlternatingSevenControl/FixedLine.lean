module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.Representation.BinaryFourOrbit
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
public import Theory.SpecificGroups.AlternatingSevenSylowNormalizer
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
/-!
# The Sylow fixed line in the binary A₇ four-space

The actual image has order divisible by 45, so the existing binary four-space
orbit count proves transitivity on its fifteen nonzero vectors. Sylow
self-normalization then gives a unique nonzero Sylow-fixed vector. Its
stabilizer has index 15 and is maximal by simplicity and the small-index
bound. A normalizer containing a three-cycle generates A₇ with this stabilizer.
All statements retain the arbitrary faithful representation and supplied Sylow.

Source: Aschbacher–Smith C.1.23(2), printed p.130. The proof uses the fixed
line of the full Sylow, rather than the fixed plane of a four-group.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped Pointwise
namespace Representation.BinaryAlternatingSevenControl
abbrev A7 := alternatingGroup (Fin 7)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem fixed_eq_of_self_normalizing
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hn : normalizer (P : Set G) = (P : Subgroup G))
    {x y : X} (hx : ∀ a ∈ (P : Subgroup G), a • x = x)
    (hy : ∀ a ∈ (P : Subgroup G), a • y = y)
    (g : G) (hg : g • x = y) : x = y := by
  have h1 : (P : Subgroup G) ≤ MulAction.stabilizer G y := hy
  have h2 : (↑(g • P : Sylow p G) : Subgroup G) ≤ MulAction.stabilizer G y := by
    rintro _ ⟨z,hz,rfl⟩
    change (g*z*g⁻¹) • y = y
    rw [mul_smul, mul_smul, ← hg, inv_smul_smul, hx z hz]
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (MulAction.stabilizer G y)
    ((g • P).subtype h2) (P.subtype h1)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hc
  have hn' := Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hc)
  rw [hn] at hn'
  have hh := hx ((c : G)*g) hn'
  rw [mul_smul,hg,c.property] at hh
  exact hh.symm

theorem transitive (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) : ∃ g : A7, ρ g v = w := by
  apply BinaryFourOrbit.representation_transitive ρ hd ?_ hv hw
  have hi : Function.Injective ρ.asGroupHom := fun a b hab => hf (congrArg Units.val hab)
  rw [actionImage, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
    nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem sylow_fixed_line (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) :
    ∃ v : V, v ≠ 0 ∧ v ∈ fixedSpace ρ R ∧
      ∀ w ∈ fixedSpace ρ R, w = 0 ∨ w = v := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) V)
  obtain ⟨v,hv,hfix⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
    (ρ.comp (R : Subgroup A7).subtype) R.isPGroup'
  refine ⟨v,hv,hfix,?_⟩
  intro w hw
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  right
  obtain ⟨g,hg⟩ := transitive ρ hf hd hw0 hv
  let : MulAction A7 V := MulAction.compHom V ρ
  exact fixed_eq_of_self_normalizing R (AlternatingSevenSylow.sylow_normalizer_eq_self R)
    (fun a ha => hw ⟨a,ha⟩) (fun a ha => hfix ⟨a,ha⟩) g hg

theorem sylow_fixed_finrank (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) : Module.finrank (ZMod 2) (fixedSpace ρ R) = 1 := by
  obtain ⟨v,hv,hfix,hunique⟩ := sylow_fixed_line ρ hf hd R
  have he : fixedSpace ρ R = Submodule.span (ZMod 2) {v} := by
    apply le_antisymm
    · intro w hw
      rcases hunique w hw with rfl | rfl
      · exact Submodule.zero_mem _
      · exact Submodule.subset_span (by simp)
    · exact Submodule.span_le.mpr (by simpa using hfix)
  rw [he,finrank_span_singleton hv]

theorem sylow_fixedKernel_index (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) : (subspaceKernel ρ (fixedSpace ρ R) ⊤).index = 15 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  let : MulAction A7 V := MulAction.compHom V ρ
  obtain ⟨v,hv,hfix,hunique⟩ := sylow_fixed_line ρ hf hd R
  have he : subspaceKernel ρ (fixedSpace ρ R) ⊤ = MulAction.stabilizer A7 v := by
    ext g
    constructor
    · exact fun h => h.2 v hfix
    · intro hg
      refine ⟨mem_top g, fun w hw => ?_⟩
      rcases hunique w hw with rfl | rfl
      · exact map_zero _
      · exact hg
  have ho : MulAction.orbit A7 v = {w : V | w ≠ 0} := by
    ext w
    constructor
    · rintro ⟨g,rfl⟩
      intro hz
      apply hv
      change ρ g v = 0 at hz
      have hh := congrArg (ρ g⁻¹) hz
      simpa only [ρ.inv_self_apply, map_zero] using hh
    · intro hw
      exact (MulAction.mem_orbit_iff).mpr (transitive ρ hf hd hv hw)
  rw [he,MulAction.index_stabilizer,ho,← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card]
  change Fintype.card {w : V // w ≠ 0} = 15
  rw [Fintype.card_subtype_compl,
    Fintype.card_unique (α := {w : V // w = 0}),
    Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,hd]
  norm_num

theorem sylow_fixedKernel_coatom (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) : IsCoatom (subspaceKernel ρ (fixedSpace ρ R) ⊤) := by
  let C := subspaceKernel ρ (fixedSpace ρ R) ⊤
  have hi : C.index = 15 := sylow_fixedKernel_index ρ hf hd R
  change IsCoatom C
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨?_,fun H hH => ?_⟩
  · intro ht
    simp [ht] at hi
  · have hdiv : H.index ∣ 15 := hi ▸ index_dvd_of_le hH.le
    have hlt : H.index < 15 := hi ▸ Subgroup.index_strictAnti hH
    have hpos : 0 < H.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))
    have hcases : H.index = 1 ∨ H.index = 3 ∨ H.index = 5 :=
      (by decide : ∀ n ∈ Finset.range 15, n ∣ 15 → 0 < n →
        n = 1 ∨ n = 3 ∨ n = 5) H.index (Finset.mem_range.mpr hlt) hdiv hpos
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    change H.index.factorial < Nat.card (alternatingGroup (Fin 7))
    rw [nat_card_alternatingGroup]
    rcases hcases with h | h | h <;> rw [h] <;> norm_num [Nat.factorial]

theorem normalizer_sup_fixedKernel_of_threeCycle
    (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) (A : Subgroup A7)
    (hc : ∃ c ∈ normalizer (A : Set A7), (c : Equiv.Perm (Fin 7)).IsThreeCycle) :
    normalizer (A : Set A7) ⊔ subspaceKernel ρ (fixedSpace ρ R) ⊤ = ⊤ := by
  let C := subspaceKernel ρ (fixedSpace ρ R) ⊤
  apply (sylow_fixedKernel_coatom ρ hf hd R).2
  apply lt_of_le_of_ne le_sup_right
  intro he
  change C = normalizer (A : Set A7) ⊔ C at he
  obtain ⟨c,hc,hthree⟩ := hc
  have hcC : c ∈ C := by
    rw [he]
    exact (show normalizer (A : Set A7) ≤ normalizer (A : Set A7) ⊔ C from le_sup_left) hc
  obtain ⟨v,hv,hfix,_⟩ := sylow_fixed_line ρ hf hd R
  exact hv (binaryAlternatingSeven_threeCycle_fixedPointFree ρ hf hd c hthree v (hcC.2 v hfix))

end Representation.BinaryAlternatingSevenControl
