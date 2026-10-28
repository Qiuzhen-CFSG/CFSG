module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Covered
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import CFSG.Quasithin.Chapter6.SourceDefs.ReducedImage


/-!
# Recovering the original Irr⁺ choice from the natural A₆ setup

The given V embeds in the literal reduced module of LT. The genuine A₆
coordinate action is transitive on its nonidentity vectors, so this
embedded subspace has no proper nonzero L-invariant subspace. It has
nontrivial action and is therefore a full commutator space with irreducible
central quotient. Its T-invariance makes the homogeneous orbit condition
automatic. This constructs the original ChosenModule, not an additional
choice premise, and retains all source subgroups and coordinates.

Source: Aschbacher–Smith, A.1.40 and Hypothesis 13.7.1,
printed pp.31–32,935, applied to the standing 13.8 setup.
-/

public section

open Subgroup Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)

include d in
theorem local_nonzero_transitive {x y : G} (hx : x ∈ V) (hy : y ∈ V)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ l ∈ L, l*x*l⁻¹=y := by
  have hnx : (d.coordinate ⟨x,hx⟩).toAdd ≠ 0 := by
    intro h
    have he : (⟨x,hx⟩:V)=1 := d.coordinate.injective (h.trans (map_one d.coordinate).symm)
    exact hx1 (congrArg Subtype.val he)
  have hny : (d.coordinate ⟨y,hy⟩).toAdd ≠ 0 := by
    intro h
    have he : (⟨y,hy⟩:V)=1 := d.coordinate.injective (h.trans (map_one d.coordinate).symm)
    exact hy1 (congrArg Subtype.val he)
  obtain ⟨a,ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero _ _ hnx hny
  obtain ⟨q,hq⟩ := d.local_quotient.surjective a
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨l,l.property,?_⟩
  have hc := d.conjugation l ⟨x,hx⟩
  rw [hl,hq] at hc
  have he : V.normalizerMonoidHom
      ⟨l.val,d.normalizes_V (mem_sup_left l.property)⟩ ⟨x,hx⟩ = ⟨y,hy⟩ :=
    d.coordinate.injective (hc.trans ha)
  exact congrArg Subtype.val he


private abbrev Local := L ⊔ (T:Subgroup G)
private abbrev Red := ReducedModule (Local (L:=L) (T:=T))
private def redVal (v : Additive (Red (L:=L) (T:=T))) : G := v.toMul.val.val
omit [Finite G] in
private theorem redVal_injective : Function.Injective (redVal (L:=L) (T:=T)) := by
  intro x y h
  apply Additive.toMul.injective
  exact Subtype.ext (Subtype.ext h)

private noncomputable def localChosenSpace : Submodule (ZMod 2) (Additive (Red (L:=L) (T:=T))) :=
  AddSubgroup.toZModSubmodule 2
    ((V.comap (Local (L:=L) (T:=T)).subtype).comap (Red (L:=L) (T:=T)).subtype).toAddSubgroup

omit [Finite G] in
private theorem chosen_mem (v : Additive (Red (L:=L) (T:=T))) :
    v∈localChosenSpace (L:=L) (T:=T) (V:=V) ↔ redVal v ∈ V := Iff.rfl

omit [Finite G] in
private theorem action_val (g : Local (L:=L) (T:=T)) (v : Additive (Red (L:=L) (T:=T))) :
    redVal (reducedRepresentation (Local (L:=L) (T:=T)) g v) =
      (g:G)*redVal v*(g:G)⁻¹ := rfl

include d in
private theorem chosen_stable : (⊤:Subgroup (Local (L:=L) (T:=T))) ≤
    subspaceStabilizer (reducedRepresentation (Local (L:=L) (T:=T))) (localChosenSpace (V:=V)) := by
  apply le_subspaceStabilizer
  intro g _ v hv
  rw [chosen_mem,action_val]
  exact (mem_normalizer_iff.mp (d.normalizes_V g.property) (redVal v)).mp hv

include d in
private theorem chosen_minimal (J : Submodule (ZMod 2) (Additive (Red (L:=L) (T:=T))))
    (hJ : L.subgroupOf (Local (L:=L) (T:=T)) ≤
      subspaceStabilizer (reducedRepresentation (Local (L:=L) (T:=T))) J)
    (hle : J ≤ localChosenSpace (V:=V)) : J=⊥ ∨ J=localChosenSpace (V:=V) := by
  by_cases hz : J=⊥
  · exact Or.inl hz
  right
  apply le_antisymm hle
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  intro y hy
  by_cases hy0 : y=0
  · exact hy0 ▸ J.zero_mem
  have hx1 : redVal x ≠ 1 := by
    intro he
    exact hx0 (redVal_injective he)
  have hy1 : redVal y ≠ 1 := by
    intro he
    exact hy0 (redVal_injective he)
  obtain ⟨l,hl,he⟩ := local_nonzero_transitive d (hle hx) hy hx1 hy1
  let a : Local (L:=L) (T:=T) := ⟨l,mem_sup_left hl⟩
  have hm := (hJ (show a∈L.subgroupOf (Local (L:=L) (T:=T)) from hl) x).mpr hx
  have hh : reducedRepresentation (Local (L:=L) (T:=T)) a x = y :=
    redVal_injective ((action_val a x).trans he)
  rwa [hh] at hm

include d in
private theorem chosen_noncentral : ¬ localChosenSpace (L:=L) (T:=T) (V:=V) ≤
    fixedSpace (reducedRepresentation (Local (L:=L) (T:=T))) (L.subgroupOf (Local (L:=L) (T:=T))) := by
  intro h
  have hv1 : ∀ v:V, v=1 := by
    intro v
    have hvR := d.module_in_reduced v.property
    rw [Chapter6.Source.reducedSubgroup_eq_map] at hvR
    obtain ⟨r,hr,he⟩ := hvR
    let x : Additive (Red (L:=L) (T:=T)) := Additive.ofMul ⟨r,hr⟩
    have hx : redVal x = (v:G) := he
    have hc : (v:G) ∈ centralizer (L:Set G) := by
      apply mem_centralizer_iff.mpr
      intro l hl
      let a : L.subgroupOf (Local (L:=L) (T:=T)) := ⟨⟨l,mem_sup_left hl⟩,hl⟩
      have hxI : x∈localChosenSpace (V:=V) := by
        change redVal x ∈ V
        rw [hx]
        exact v.property
      have hf := h hxI a
      have hf' := congrArg redVal hf
      change redVal (reducedRepresentation (Local (L:=L) (T:=T)) a.val x)=redVal x at hf'
      rw [action_val,hx] at hf'
      exact mul_inv_eq_iff_eq_mul.mp hf'
    have hb : v ∈ (⊥:Subgroup V) := (local_centralizer_bot d) ▸ hc
    exact mem_bot.mp hb
  have hV : V=⊥ := by
    apply bot_unique
    intro v hv
    exact congrArg Subtype.val (hv1 ⟨v,hv⟩)
  have hline : V₁=⊥ := bot_unique (hV ▸ d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
  have hc := d.line_card
  rw [hline,Subgroup.card_bot] at hc
  norm_num at hc

noncomputable def localChosenModule : ChosenModule T L V := by
  let I := localChosenSpace (L:=L) (T:=T) (V:=V)
  let ρ := reducedRepresentation (Local (L:=L) (T:=T))
  let K := L.subgroupOf (Local (L:=L) (T:=T))
  let S := (T:Subgroup G).subgroupOf (Local (L:=L) (T:=T))
  have hK : K ≤ subspaceStabilizer ρ I := le_top.trans (chosen_stable d)
  have hS : S ≤ subspaceStabilizer ρ I := le_top.trans (chosen_stable d)
  have hc : subspaceCommutator ρ I K=I := by
    rcases chosen_minimal d _ (subspaceCommutator_invariant ρ I K)
      (subspaceCommutator_le_of_invariant ρ hK) with hz|he
    · exact False.elim (chosen_noncentral d ((subspaceCommutator_eq_bot_iff ρ I K).mp hz))
    · exact he
  have hi : IsIrrPlus ρ K I := by
    apply isIrrPlus_of_minimal ρ hK hc (chosen_noncentral d)
    intro J hJ hle
    rcases chosen_minimal d J hJ hle with he|he
    · right
      rw [he]
      exact bot_le
    · exact Or.inl he
  have hnormal : (L.subgroupOf (Local (L:=L) (T:=T))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  refine ⟨I,⟨?_,hK,hi,?_⟩,?_⟩
  · exact le_normalizer_of_normal
  · apply le_antisymm _ (quotientImage_le_homogeneousPart ρ hK)
    rw [orbitSpan_eq_self ρ hS]
    apply iSup_le
    intro J
    apply iSup_le
    intro hJ
    exact hJ.1
  · ext v
    constructor
    · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩
      exact hy
    · intro hv
      have hvR := d.module_in_reduced hv
      rw [Chapter6.Source.reducedSubgroup_eq_map] at hvR
      obtain ⟨r,hr,he⟩ := hvR
      refine ⟨r,⟨⟨r,hr⟩,?_,rfl⟩,he⟩
      change r.val ∈ V
      rw [show r.val=v from he]
      exact hv

/-- The earlier natural source configuration reconstructed from LocalSetup. -/
@[expose] noncomputable def localNaturalSetup : NaturalSetup T L V V₁ V₂ V₃ M G₁ where
  counterexample := d.counterexample
  normalizes_L := d.normalizes_L
  normalizes_V := d.normalizes_V
  local_quotient := d.local_quotient
  module_in_reduced := d.module_in_reduced
  coordinate := d.coordinate
  conjugation := d.conjugation
  line_le_plane := d.line_le_plane
  plane_le_seed := d.plane_le_seed
  seed_le := d.seed_le
  line_card := d.line_card
  plane_card := d.plane_card
  seed_card := d.seed_card
  line_stable := d.line_stable
  plane_stable := d.plane_stable
  seed_stable := d.seed_stable
  first_normalizer := d.first_normalizer
  local_normalizer := d.local_normalizer
  chosen := localChosenModule d

/-- Restoring the given abelian span returns the identical original setup. -/
theorem localNaturalSetup_toLocalSetup :
    (localNaturalSetup d).toLocalSetup d.abelian_span = d := rfl

include d in
/-- An actual ChosenModule consumer on the unchanged original LT and V. -/
theorem local_core_centralizes :
    (L ⊔ (T:Subgroup G)).pCoreIn 2 ≤ centralizer (V:Set G) :=
  (localChosenModule d).core_centralizes

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
