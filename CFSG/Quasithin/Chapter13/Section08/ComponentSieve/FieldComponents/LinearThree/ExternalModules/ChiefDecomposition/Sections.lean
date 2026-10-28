module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Models
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Literal chief sections for the external linear-three action

A cover in the invariant-subspace lattice gives an irreducible literal quotient.
A nontrivial perfect normal actor has a noncentral chief section: choose a minimal
invariant space above its fixed space and use perfection to exclude a central
quotient. For an order-three actor, the norm operator proves that ambient
commutator generation passes to every section. Finally, the kernel argument for
two simple normal factors proves section faithfulness from an actual joint
centralizer containment.

These are the section steps for Aschbacher–Smith 13.8.21(1), printed pp.956–957,
combined manuscript of 1 March 2004. The irreducible module classifications and
the structural centralizer containment are separate inputs.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- A chief section is irreducible for the original acting group. -/
theorem chief_section_irreducible (L N : Subrepresentation ρ) (hLN : L ⋖ N) :
    IsIrreducible (sectionRepresentation ρ L N) := by
  let q := (sectionLower ρ L N).toSubmodule.mkQ
  have hproper : (sectionLower ρ L N).toSubmodule ≠ ⊤ := by
    intro he
    apply hLN.1.not_ge
    intro v hv
    have hm : (⟨v, hv⟩ : N) ∈ (sectionLower ρ L N).toSubmodule := by rw [he]; trivial
    exact hm
  let : Nontrivial (N ⧸ (sectionLower ρ L N).toSubmodule) :=
    Submodule.Quotient.nontrivial_iff.mpr hproper
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro S
  let P : Subrepresentation ρ :=
    { toSubmodule := (S.toSubmodule.comap q).map N.toSubmodule.subtype
      apply_mem_toSubmodule g := by
        rintro v ⟨w, hw, rfl⟩
        exact ⟨N.toRepresentation g w, S.apply_mem_toSubmodule g hw, rfl⟩ }
  have hLP : L ≤ P := by
    intro v hv
    refine ⟨⟨v, hLN.le hv⟩, ?_, rfl⟩
    change q ⟨v, hLN.le hv⟩ ∈ S
    have hz : q ⟨v, hLN.le hv⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact S.toSubmodule.zero_mem
  have hPN : P ≤ N := Submodule.map_subtype_le _ _
  rcases (covBy_iff_lt_and_eq_or_eq.mp hLN).2 P hLP hPN with he | he
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨w, rfl⟩ := (sectionLower ρ L N).toSubmodule.mkQ_surjective v
    have hw : (w : U) ∈ P := ⟨w, hv, rfl⟩
    rw [he] at hw
    exact (Submodule.Quotient.mk_eq_zero _).mpr hw
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    obtain ⟨w, rfl⟩ := (sectionLower ρ L N).toSubmodule.mkQ_surjective v
    have hw : (w : U) ∈ P := by rw [he]; exact w.property
    obtain ⟨z, hz, hez⟩ := hw
    have hzw : z = w := Subtype.ext hez
    subst z
    exact hz

/-- The fixed space of a normal subgroup is invariant under the ambient action. -/
noncomputable def normalFixedSubrepresentation (K : Subgroup H) [K.Normal] : Subrepresentation ρ where
  toSubmodule := fixedSpace ρ K
  apply_mem_toSubmodule h v hv := by
    intro k
    have hk : h⁻¹ * k * h ∈ K := by
      simpa using (inferInstance : K.Normal).conj_mem (k : H) k.property h⁻¹
    have hh := hv ⟨_, hk⟩
    change ρ k (ρ h v) = ρ h v
    calc
      _ = ρ h (ρ (h⁻¹ * k * h) v) := by
        simp [map_mul, Module.End.mul_apply]
      _ = _ := congrArg (ρ h) hh

/-- A nontrivial perfect normal component acts nontrivially on an actual chief
section. The lower term can be chosen to be the whole component-fixed space. -/
theorem exists_noncentral_chief_section [FiniteDimensional (ZMod 2) U]
    (K : Subgroup H) [K.Normal] [Group.IsPerfect K]
    (hn : ∃ k : K, ∃ v, ρ k v ≠ v) :
    ∃ L N : Subrepresentation ρ, L ⋖ N ∧
      ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v := by
  classical
  let C := normalFixedSubrepresentation ρ K
  have hC : C < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    obtain ⟨k, v, hv⟩ := hn
    have hm : v ∈ C := by rw [he]; trivial
    exact hv (hm k)
  let P : ℕ → Prop := fun n => ∃ N : Subrepresentation ρ,
    C < N ∧ Module.finrank (ZMod 2) N.toSubmodule = n
  have hp : ∃ n, P n := ⟨_, ⊤, hC, rfl⟩
  obtain ⟨N, hCN, hdim⟩ := Nat.find_spec hp
  have hc : C ⋖ N := by
    refine ⟨hCN, ?_⟩
    intro M hCM hMN
    exact Nat.find_min hp (hdim ▸ Submodule.finrank_lt_finrank_of_lt hMN)
      ⟨M, hCM, rfl⟩
  refine ⟨C, N, hc, ?_⟩
  by_contra! hfix
  have hstable : K ≤ subspaceStabilizer ρ N.toSubmodule := by
    apply le_subspaceStabilizer
    exact fun k _ v hv => N.apply_mem_toSubmodule k hv
  have hcomm : subspaceCommutator ρ N.toSubmodule K ≤ fixedSpace ρ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, hv, rfl⟩
    exact (sectionRepresentation_trivial_iff ρ C N k).mp (hfix ⟨k, hk⟩) v hv
  have hle := le_fixedSpace_of_commutator_le_fixedSpace ρ K N.toSubmodule hstable hcomm
  exact hCN.not_ge hle

/-- Faithfulness supplies the noncentrality needed above. -/
theorem exists_noncentral_chief_section_of_faithful [FiniteDimensional (ZMod 2) U]
    (hfaith : Function.Injective ρ) (K : Subgroup H) [K.Normal] [Group.IsPerfect K]
    (hK : K ≠ ⊥) :
    ∃ L N : Subrepresentation ρ, L ⋖ N ∧
      ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v := by
  apply exists_noncentral_chief_section ρ K
  by_contra! h
  apply hK
  apply bot_unique
  intro k hk
  apply hfaith
  ext v
  simpa using h ⟨k, hk⟩ v
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- The unnormalized averaging operator of a finite subgroup. -/
noncomputable def subgroupNorm (X : Subgroup H) [Fintype X] : Module.End (ZMod 2) U :=
  ∑ x : X, ρ x

private theorem subgroupNorm_action (X : Subgroup H) [Fintype X] (x : X) (v : U) :
    subgroupNorm ρ X (ρ x v) = subgroupNorm ρ X v := by
  simpa only [subgroupNorm, LinearMap.sum_apply, Equiv.coe_mulRight, Subgroup.coe_mul, map_mul,
    Module.End.mul_apply] using Equiv.sum_comp (Equiv.mulRight x) (fun y : X => ρ y v)

/-- Commutator generation annihilates the norm operator. -/
theorem subgroupNorm_eq_zero_of_generated (X : Subgroup H) [Fintype X]
    (hgen : subspaceCommutator ρ ⊤ X = ⊤) (v : U) : subgroupNorm ρ X v = 0 := by
  have hle : subspaceCommutator ρ ⊤ X ≤ LinearMap.ker (subgroupNorm ρ X) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, w, _, rfl⟩
    change subgroupNorm ρ X (ρ x w - w) = 0
    rw [map_sub, subgroupNorm_action ρ X ⟨x, hx⟩, sub_self]
  rw [hgen] at hle
  exact hle (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) U))

/-- The same norm identity holds on the literal subquotient. -/
theorem section_subgroupNorm_eq_zero (X : Subgroup H) [Fintype X]
    (hgen : subspaceCommutator ρ ⊤ X = ⊤) (L N : Subrepresentation ρ)
    (v : N ⧸ (sectionLower ρ L N).toSubmodule) :
    subgroupNorm (sectionRepresentation ρ L N) X v = 0 := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  let q := (sectionLower ρ L N).toSubmodule.mkQ
  have hn : (∑ x : X, N.toRepresentation x v) = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, ZeroMemClass.coe_zero]
    change (∑ x : X, ρ x (v : U)) = 0
    simpa only [subgroupNorm, LinearMap.sum_apply] using
      subgroupNorm_eq_zero_of_generated ρ X hgen (v : U)
  change (∑ x : X, (sectionRepresentation ρ L N) x) (q v) = 0
  rw [LinearMap.sum_apply]
  change (∑ x : X, q (N.toRepresentation x v)) = 0
  rw [← map_sum, hn, map_zero]

private theorem card_three_nsmul (X : Subgroup H) [Fintype X] (hX : Nat.card X = 3)
    (v : U) : Fintype.card X • v = v := by
  calc
    _ = (3 : ZMod 2) • v := by
      rw [← Nat.card_eq_fintype_card, hX]
      exact (Nat.cast_smul_eq_nsmul (ZMod 2) 3 v).symm
    _ = v := by rw [show (3 : ZMod 2) = 1 from rfl, one_smul]

/-- Every section has zero X-fixed space when the ambient module is generated
by commutators with a subgroup of order three. No semisimplicity of H is used. -/
theorem section_fixedSpace_eq_bot_of_card_three (X : Subgroup H) [Finite X]
    (hX : Nat.card X = 3) (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (L N : Subrepresentation ρ) :
    fixedSpace (sectionRepresentation ρ L N) X = ⊥ := by
  classical
  let : Fintype X := Fintype.ofFinite X
  apply le_antisymm _ bot_le
  intro v hv
  have hn := section_subgroupNorm_eq_zero ρ X hgen L N v
  have he : subgroupNorm (sectionRepresentation ρ L N) X v = v := by
    have hf (x : X) : sectionRepresentation ρ L N x v = v := hv x
    simp only [subgroupNorm, LinearMap.sum_apply, hf, Finset.sum_const,
      Finset.card_univ, card_three_nsmul X hX]
  exact he.symm.trans hn

/-- The source identity U=[U,X] passes to every literal section, including
sections whose upper term is a proper submodule. -/
theorem section_generated_of_card_three (X : Subgroup H) [Finite X]
    (hX : Nat.card X = 3) (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (L N : Subrepresentation ρ) :
    subspaceCommutator (sectionRepresentation ρ L N) ⊤ X = ⊤ := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let σ := sectionRepresentation ρ L N
  apply top_unique
  intro v _
  have hn : (∑ x : X, σ x v) = 0 := by
    simpa only [subgroupNorm, LinearMap.sum_apply] using
      section_subgroupNorm_eq_zero ρ X hgen L N v
  have he : (∑ x : X, (v - σ x v)) = v := by
    rw [Finset.sum_sub_distrib, hn, sub_zero, Finset.sum_const, Finset.card_univ,
      card_three_nsmul X hX]
  rw [← he]
  apply Submodule.sum_mem
  intro x _
  have hm : σ x v - v ∈ subspaceCommutator σ ⊤ X :=
    Submodule.subset_span ⟨x, x.property, v, Submodule.mem_top, rfl⟩
  simpa only [neg_sub] using (subspaceCommutator σ ⊤ X).neg_mem hm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- Nontrivial action of a simple subgroup has trivial restricted kernel. -/
theorem faithful_restriction_of_simple (K : Subgroup H) [IsSimpleGroup K]
    (hn : ∃ k : K, ∃ v, ρ k v ≠ v) : Function.Injective (ρ.comp K.subtype) := by
  let σ := ρ.comp K.subtype
  apply σ.ker_eq_bot_iff.mp
  rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · obtain ⟨k, v, hv⟩ := hn
    have hk : k ∈ σ.ker := by rw [ht]; trivial
    exact False.elim (hv (LinearMap.congr_fun hk v))

/-- A normal kernel disjoint from both simple factors centralizes both. The
stated centralizer containment then places it in X, where it is trivial. -/
theorem faithful_of_simple_normal_factors (K X : Subgroup H)
    [K.Normal] [X.Normal] [IsSimpleGroup K] [IsSimpleGroup X]
    (hcent : Subgroup.centralizer (K : Set H) ⊓ Subgroup.centralizer (X : Set H) ≤ X)
    (hK : ∃ k : K, ∃ v, ρ k v ≠ v) (hX : ∃ x : X, ∃ v, ρ x v ≠ v) :
    Function.Injective ρ := by
  have hdis (A : Subgroup H) (hf : Function.Injective (ρ.comp A.subtype)) :
      Disjoint ρ.ker A := by
    apply disjoint_iff_inf_le.mpr
    intro a ha
    have he : (⟨a, ha.2⟩ : A) = 1 := hf (show (ρ.comp A.subtype) ⟨a, ha.2⟩ =
      (ρ.comp A.subtype) 1 by simpa using ha.1)
    exact congrArg Subtype.val he
  have hdK := hdis K (faithful_restriction_of_simple ρ K hK)
  have hdX := hdis X (faithful_restriction_of_simple ρ X hX)
  have hcK : ρ.ker ≤ Subgroup.centralizer (K : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_eq_bot_of_disjoint hdK)
  have hcX : ρ.ker ≤ Subgroup.centralizer (X : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_eq_bot_of_disjoint hdX)
  apply ρ.ker_eq_bot_iff.mp
  exact le_bot_iff.mp (fun g hg =>
    (disjoint_iff_inf_le.mp hdX) ⟨hg, hcent ⟨hcK hg, hcX hg⟩⟩)
/-- Each chief section is noncentral for the marked order-three subgroup. -/
theorem chief_section_noncentral_on_three (X : Subgroup H) [Finite X]
    (hX : Nat.card X = 3) (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (L N : Subrepresentation ρ) (hLN : L ⋖ N) :
    ∃ x : X, ∃ v, sectionRepresentation ρ L N x v ≠ v := by
  let σ := sectionRepresentation ρ L N
  let : IsIrreducible σ := chief_section_irreducible ρ L N hLN
  let : Nontrivial (N.toSubmodule ⧸ (sectionLower ρ L N).toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial σ
  by_contra! hfix
  obtain ⟨v, hv⟩ := exists_ne (0 : N.toSubmodule ⧸ (sectionLower ρ L N).toSubmodule)
  have hm : v ∈ fixedSpace σ X := fun x => hfix x v
  rw [section_fixedSpace_eq_bot_of_card_three ρ X hX hgen L N] at hm
  exact hv hm

/-- Chief-section faithfulness from simple normal factors and their actual
joint centralizer. Faithfulness of the ambient action is not used as a
substitute for faithfulness of this section. -/
theorem chief_section_faithful (K X : Subgroup H)
    [K.Normal] [X.Normal] [IsSimpleGroup K] [Finite X]
    (hcent : Subgroup.centralizer (K : Set H) ⊓ Subgroup.centralizer (X : Set H) ≤ X)
    (hX : Nat.card X = 3) (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (L N : Subrepresentation ρ) (hLN : L ⋖ N)
    (hK : ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v) :
    Function.Injective (sectionRepresentation ρ L N) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsSimpleGroup X := isSimpleGroup_of_prime_card hX
  exact faithful_of_simple_normal_factors (sectionRepresentation ρ L N) K X hcent hK
    (chief_section_noncentral_on_three ρ X hX hgen L N hLN)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules