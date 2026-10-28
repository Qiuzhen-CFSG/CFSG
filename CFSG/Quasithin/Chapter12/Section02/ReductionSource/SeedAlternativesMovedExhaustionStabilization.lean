module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionIsotypic
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionStabilization

/-!
# Stabilizing the chosen seed under strict normalizer-orbit enlargement

For the literal normalizer orbit `U = componentOrbit V (normalizer L)`,
a Sylow element preserving the full isotypic component of `V` preserves `V`.
This uses homogeneous selection only in the original Sylow orbit. If `U`
is strictly larger than that orbit, the full component contains a second
copy of the seed. The repeated-constituent argument then forces every
starred cubic actor in the original Sylow image to preserve the component
and the seed. The full preimage under the original conjugation action map
therefore normalizes `V`.

The final theorem constructs such an actor using the source cubic bound
under `hmany`, with no extra actor or stabilization premise. These are the
D.3.12 conclusions needed by the remaining D.3.13--19 centralizer argument;
normalizer-orbit exhaustion and source 3.2.5 remain with `qt-baumann-fsu`.
The literal component action retains the special linear central covers
and the separate alternating-seven constituent.

Source: Aschbacher--Smith, D.3.10--12, printed pp.201--202.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A Sylow element preserving the full seed type also preserves the actual
chosen seed. Homogeneous selection is used only in the original Sylow orbit. -/
theorem normalizer_sylow_type_stabilizer_le_seed
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    (internalSylow T M U hn D.sylow_normalizes_component : Subgroup _) ⊓
      subspaceStabilizer ρ I ≤ subspaceStabilizer ρ (internalSection U V) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let N := L.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let c := normalTypeAction (internalAction hn) N
  let S := internalSubrepresentation hn D.normalizes
  let I := (typePart S).toSubmodule
  have hVU : V ≤ U := le_componentOrbit V M
  have hi : IsIrreducible S.toRepresentation :=
    internalSubrepresentation_irreducible hn L.le_normalizer hVU D.normalizes D.ne_bot
      (D.seed_invariant_subgroup_eq hc)
  dsimp only
  intro a ha
  have hmem := ha.1
  change a ∈ ((T : Subgroup G).subgroupOf M).map f at hmem
  obtain ⟨g,hg,rfl⟩ := hmem
  have hmap : (c.conjugate g (typePart S)).toSubmodule = I.map (ρ (f g)) :=
    conjugateSubrepresentationOrderIso_toSubmodule (internalAction hn) N g _
  have he : typePart (c.conjugate g S) = typePart S := by
    rw [←conjugate_typePart]
    apply Subrepresentation.toSubmodule_injective
    exact hmap.trans ((subspace_map_eq_iff ρ I (f g)).mpr ha.2)
  have hs : SameModule S (c.conjugate g S) :=
    sameModule_of_typePart_eq S _ hi (c.conjugate_irreducible S hi g) he.symm
  have hle : V.map (MulAut.conj g.val).toMonoidHom ≤ U :=
    le_iSup (fun z : M => V.map (MulAut.conj z.val).toMonoidHom) g
  have hnorm : g.val ∈ normalizer (V : Set G) := by
    by_contra hng
    apply D.moved_conjugate_not_sameModule hg hng
    let := D.elementary
    let : IsElementaryAbelian 2 (V.map (MulAut.conj g.val).toMonoidHom) :=
      IsElementaryAbelian.of_le hle
    rw [internal_conjugate_subrepresentation hn le_rfl hVU D.normalizes g] at hs
    exact sameConjugationModule_of_internal
      (V' := V.map (MulAut.conj g.val).toMonoidHom) hn L.le_normalizer hVU hle D.normalizes
      (normalizes_conjugate D.normalizes g) hs
  apply (subspace_map_eq_iff ρ S.toSubmodule (f g)).mp
  change (internalSection U V).map (internalAction hn g) = internalSection U V
  have hV : V.map (MulAut.conj g.val).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hnorm
  rw [internalSection_map_action hn hVU g,hV]

/-- D.3.12 for the chosen seed: a minimal cubic actor in the original Sylow
image stabilizes its full isotypic component under strict orbit enlargement. -/
theorem normalizer_starred_stabilizes_isotypic_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      A ≤ subspaceStabilizer ρ I := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let N := L.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let c := normalTypeAction (internalAction hn) N
  let S := internalSubrepresentation hn D.normalizes
  let I := (typePart S).toSubmodule
  dsimp only
  intro A hAS hA
  obtain ⟨t,_,_,hcomp,hstrict,hdim,hperm,_⟩ :=
    D.normalizer_starred_isotypic_pair_of_moved_of_many h hmany hc hm hne
  have hVU : V ≤ U := le_componentOrbit V M
  have hi : IsIrreducible S.toRepresentation :=
    internalSubrepresentation_irreducible hn L.le_normalizer hVU D.normalizes D.ne_bot
      (D.seed_invariant_subgroup_eq hc)
  have hstrict' : S < typePart S := by
    refine lt_of_le_of_ne (le_typePart S) ?_
    intro he
    exact hstrict.ne (congrArg Subrepresentation.toSubmodule he)
  obtain ⟨R,hsame,hRI,hdis⟩ := exists_disjoint_same_in_typePart S hi hstrict'
  have hseed_dim : 1 < Module.finrank (ZMod 2) S.toSubmodule := by
    let := D.elementary
    let a : D.space ≃+ Additive V := D.spaceEquiv.toAdditive
    let e : D.space ≃ₗ[ZMod 2] Additive V := {a with map_smul' := ZMod.map_smul a}
    change 1 < Module.finrank (ZMod 2) (internalSection U V)
    rw [(internalSectionEquiv hVU).finrank_eq,←e.finrank_eq,
      ←D.orbitSeedActionEquiv.linearEquiv.finrank_eq]
    exact lt_trans (by decide) (D.orbitSeed_finrank_gt_two h.toHypothesis1221)
  apply starred_stabilizes_repeated_pair ρ f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective N S R hi hseed_dim
    I (I.map (ρ (f t))) hcomp hdim (le_typePart S) hRI hsame hdis hA
    (fun b _ => hperm b)
  exact (inf_le_inf hAS le_rfl).trans
    (D.normalizer_sylow_type_stabilizer_le_seed h.toHypothesis1221 hc)

/-- The same source cubic actor stabilizes the literal chosen seed. -/
theorem normalizer_starred_stabilizes_seed_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      A ≤ subspaceStabilizer ρ (internalSection U V) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  dsimp only
  intro A hAS hA
  exact (le_inf hAS (D.normalizer_starred_stabilizes_isotypic_of_moved_of_many
    h hmany hc hm hne A hAS hA)).trans
      (D.normalizer_sylow_type_stabilizer_le_seed h.toHypothesis1221 hc)

/-- Stabilization descends through the original conjugation map to actual
normalization of V by the full preimage of the cubic actor. -/
theorem normalizer_starred_preimage_normalizes_seed_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      (A.comap (internalHom M U hn)).map M.subtype ≤ normalizer (V : Set G) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  dsimp only
  intro A hAS hA
  have hs := D.normalizer_starred_stabilizes_seed_of_moved_of_many h hmany hc hm hne A hAS hA
  rintro _ ⟨g,hg,rfl⟩
  apply mem_normalizer_iff.mpr
  intro v
  have hh := hs hg
  have hVU : V ≤ U := le_componentOrbit V M
  constructor
  · intro hv
    exact (hh (Additive.ofMul ⟨v,hVU hv⟩)).2 hv
  · intro hv
    have hU : g.val * v * g.val⁻¹ ∈ U := hVU hv
    have hvU : v ∈ U := (mem_normalizer_iff.mp (hn g.property) v).mpr hU
    exact (hh (Additive.ofMul ⟨v,hvU⟩)).1 hv

/-- A source cubic actor with both stabilization conclusions exists in the
literal Sylow image. No extra actor or local invariance premise remains. -/
theorem exists_normalizer_starred_stabilizes_of_moved_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let I := (typePart (internalSubrepresentation hn D.normalizes)).toSubmodule
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      A ≤ subspaceStabilizer ρ I ∧ A ≤ subspaceStabilizer ρ (internalSection U V) ∧
      (A.comap (internalHom M U hn)).map M.subtype ≤ normalizer (V : Set G) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  obtain ⟨A,hAS,hA,_⟩ := D.exists_normalizer_starred_in_sylow_of_many h hmany
  exact ⟨A,hAS,hA,
    D.normalizer_starred_stabilizes_isotypic_of_moved_of_many h hmany hc hm hne A hAS hA,
    D.normalizer_starred_stabilizes_seed_of_moved_of_many h hmany hc hm hne A hAS hA,
    D.normalizer_starred_preimage_normalizes_seed_of_moved_of_many h hmany hc hm hne A hAS hA⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
