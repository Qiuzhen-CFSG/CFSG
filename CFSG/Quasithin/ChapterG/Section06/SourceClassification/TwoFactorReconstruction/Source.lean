module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorReconstruction.FactorSpaces
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneRows.FactorModels
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.InitialReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneFactorSelection
public import Theory.GroupTheory.NormalClosureProductExchange

/-!
# Reconstruction of the two-factor G.6.4 source branch

The original rank-one involution belongs to one of the actual source factors.
Normal-closure generation supplies an ambient exchanger and hence a conjugate
rank-one involution in the second factor. Apply the genuine source row
selection to each, recover the original moved spaces by their dimension
bounds, and prove their full sum and cross centralizations. Finally include
the same factors into G, retaining the original action and marked involution.

Source: Aschbacher–Smith, G.6.4 case II, printed pp.345–346.
The ambient involutory extension is the separate final normalizer step.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource ChapterB.SourceInduction TwoFactorReconstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

private theorem reconstruct_marked_first
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (d : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype))
    (ha : (⟨a, subset_normalClosure (Set.mem_singleton a)⟩ : normalClosure ({a} : Set G)) ∈ d.first) :
    Nonempty (TwoFactorModules ρ a) := by
  let := h.finite_group
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  let σ : Representation (ZMod 2) K V := ρ.comp K.subtype
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  let A := d.first.map K.subtype
  let B := d.second.map K.subtype
  have htne : t ≠ 1 := fun he => h.nonidentity (congrArg Subtype.val he)
  have ht : t ^ 2 = 1 := Subtype.ext h.involution
  have hjoin : A ⊔ B = K := by
    change d.first.map K.subtype ⊔ d.second.map K.subtype = K
    rw [← Subgroup.map_sup, d.product.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  have hcomm : ⁅A, B⁆ = ⊥ := by
    change ⁅d.first.map K.subtype, d.second.map K.subtype⁆ = ⊥
    rw [← Subgroup.map_commutator, d.product.commutator_eq_bot, Subgroup.map_bot]
  have hdis : Disjoint A B := Subgroup.disjoint_map K.subtype_injective d.product.disjoint
  have hB : B ≠ ⊥ := by
    intro he
    have hb : d.second = ⊥ := Subgroup.map_injective (f := K.subtype) K.subtype_injective
      (by simpa only [Subgroup.map_bot] using he)
    exact (Subgroup.nontrivial_iff_ne_bot d.second).mp d.secondCase.nontrivial hb
  have hmap (g : G) (X : Subgroup K) :
      (X.map (MulAut.conjNormal g).toMonoidHom).map K.subtype =
        (X.map K.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hperm (g : G) :
      (A.map (MulAut.conj g).toMonoidHom = A ∧ B.map (MulAut.conj g).toMonoidHom = B) ∨
      (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A) := by
    have hh := d.automorphism_permutation (h.normalClosure_ffHypothesis hr).twoCore
      (MulAut.conjNormal g)
    rcases hh with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨(hmap g d.first).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₁),
        (hmap g d.second).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₂)⟩
    · exact Or.inr ⟨(hmap g d.first).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₁),
        (hmap g d.second).symm.trans (congrArg (fun X : Subgroup K => X.map K.subtype) h₂)⟩
  have haA : a ∈ A := mem_map_of_mem K.subtype ha
  obtain ⟨g, hg, _⟩ := exists_exchange_of_normalClosure_product A B a haA hjoin hdis hB hperm
  have hgs : d.first.map (MulAut.conjNormal g).toMonoidHom = d.second := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [hmap]
    exact hg
  let b : K := MulAut.conjNormal g t
  have hb : b ∈ d.second := hgs ▸ mem_map_of_mem (MulAut.conjNormal g).toMonoidHom ha
  have hbne : b ≠ 1 := fun he => htne ((MulAut.conjNormal g).injective
    (he.trans (map_one _).symm))
  have hbt : b ^ 2 = 1 := by
    change (MulAut.conjNormal g t) ^ 2 = 1
    rw [← map_pow, ht, map_one]
  have hbr : Module.finrank (ZMod 2) (LinearMap.range (σ b - LinearMap.id)) ≤ 1 := by
    change Module.finrank (ZMod 2) (LinearMap.range (ρ (g * a * g⁻¹) - LinearMap.id)) ≤ 1
    rw [← fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_conj,
      fixedCodim_zpowers_eq_displacement_rank, hr]
  obtain ⟨hm₁, hn₁⟩ := sourceFactor_small_quotient_of_rank_one d.firstCase t ha ht htne hr.le
  obtain ⟨hm₂, hn₂⟩ := sourceFactor_small_quotient_of_rank_one d.secondCase b hb hbt hbne hbr
  obtain ⟨hf₁, hmA⟩ := small_model_on_moved hm₁ hn₁ ⟨t, ha⟩
    (fun he => htne (congrArg Subtype.val he))
    (by apply Subtype.ext; change t * t = 1; simpa only [pow_two] using ht) hr.le
  obtain ⟨_, hmB⟩ := small_model_on_moved hm₂ hn₂ ⟨b, hb⟩
    (fun he => hbne (congrArg Subtype.val he))
    (by apply Subtype.ext; change b * b = 1; simpa only [pow_two] using hbt) hbr
  have hsum := original_spaces_sum d hm₁ hm₂ h.normalClosure_moved_eq_top
  obtain ⟨hc₁, hc₂⟩ := original_cross_commutator d hm₁ hm₂ hf₁
  have hs₁ : d.firstSpace.toSubmodule = subspaceCommutator ρ ⊤ A :=
    hm₁.trans (commutator_subtype_map ρ K d.first ⊤)
  have hs₂ : d.secondSpace.toSubmodule = subspaceCommutator ρ ⊤ B :=
    hm₂.trans (commutator_subtype_map ρ K d.second ⊤)
  refine ⟨{
    first := A
    second := B
    join_eq := hjoin
    disjoint := hdis.eq_bot
    commute := hcomm
    marked := haA
    second_nontrivial := hB
    first_model := ?_
    second_model := ?_
    space_sum := ?_
    cross_first := ?_
    cross_second := ?_
    permutation := hperm }⟩
  · have hh := smallFactorModel_subtype K d.first (moved σ d.first) hmA
    rwa [show moved σ d.first = subspaceCommutator ρ ⊤ A from commutator_subtype_map ρ K d.first ⊤] at hh
  · have hh := smallFactorModel_subtype K d.second (moved σ d.second) hmB
    rwa [show moved σ d.second = subspaceCommutator ρ ⊤ B from commutator_subtype_map ρ K d.second ⊤] at hh
  · rwa [hs₁, hs₂] at hsum
  · rwa [commutator_subtype_map, hs₂] at hc₁
  · rwa [commutator_subtype_map, hs₁] at hc₂

/-- The complete original module output of G.6.4's two-factor source branch. -/
theorem Hypotheses.twoFactorModules_of_source
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (d : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype)) :
    Nonempty (TwoFactorModules ρ a) := by
  let := h.finite_module
  let t : normalClosure ({a} : Set G) := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  rcases d.rank_one_mem_factor t hr.le with ht | ht
  · exact reconstruct_marked_first h hr d ht
  · let d' : SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype) :=
      { first := d.second
        second := d.first
        product := d.product.swap
        firstSpace := d.secondSpace
        secondSpace := d.firstSpace
        decomposition := d.decomposition.symm
        firstCase := d.secondCase
        secondCase := d.firstCase }
    exact reconstruct_marked_first h hr d' ht

end CFSG.Quasithin.ChapterG.Section06
