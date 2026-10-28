module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleSource
public import Theory.SpecificGroups.Alternating.TripleTranspositionFixed

/-!
# Excluding the marked seven-point action from the proper completion

The original local component K lies in the canonical containing residual L
and centralizes the marked central involution z. Its inclusion therefore
lands in the fixed subgroup of the actual conjugation action on L.

For both A₇ and its central three-cover, the marked triple-transposition
fixed group is solvable. This contradicts the original local component's
nonsolvability. The proof uses the original 14.2.3 centralization and proper
completion containment, before binary selection or any later residual
placement. It does not need a paired-rank hypothesis.

Source: Aschbacher–Smith 14.2.15, printed pp.985–986, and 1.1.5(3)(d).
-/

public section

namespace CFSG.Quasithin.Chapter14.Section02
open Subgroup Theory.GroupTheory Stellmacher
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure

/-- The literal seven-point action, including its central three-cover, fixes
only a solvable subgroup. -/
theorem seven_action_fixed_solvable {L : Type*} [Group L]
    (α : MulAut L) (σ : Equiv.Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2})
    (ha : AlternatingAction α 7 σ) : Group.IsSolvable α.fixedSubgroup := by
  rcases ha with ⟨e,he⟩ | ⟨_,_,e,he⟩
  · have hk : e.toMonoidHom.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact e.injective
    exact alternatingGroup.TripleTranspositionFixed.fixed_solvable_of_central_map
      α σ hσ e.toMonoidHom (hk ▸ bot_le) he
  · let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hk : f.ker = center L := by
      ext x
      change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    exact alternatingGroup.TripleTranspositionFixed.fixed_solvable_of_central_map
      α σ hσ f hk.le he

variable {G : Type*} [Group G] [Finite G]

/-- Original 14.2.15 excludes the literal seven-constructor action before
any binary-pair selection or later containing-overgroup residual identity. -/
theorem source_proper_completion_seven_action_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ∀ (z : G), z ∈ centralInvolutions T →
    ∀ (α : MulAut L), (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) →
    ∀ (σ : Equiv.Perm (Fin 7)), σ.cycleType = {2,2,2} → ¬ AlternatingAction α 7 σ := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ∀ z : G, z ∈ centralInvolutions T →
    ∀ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) →
    ∀ σ : Equiv.Perm (Fin 7), σ.cycleType = {2,2,2} → ¬ AlternatingAction α 7 σ
  intro z hzZ α hα σ hσ ha
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨_,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  have hKC : K ≤ centralizer ({z} : Set G) :=
    ((le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hzZ))
  let := seven_action_fixed_solvable α σ hσ ha
  let f : K →* α.fixedSubgroup := (inclusion hKL).codRestrict _ (by
    intro x
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    rw [hα]
    change z * (x : G) * z⁻¹ = (x : G)
    have hc := mem_centralizer_singleton_iff.mp (hKC x.property)
    rw [←hc,mul_inv_cancel_right])
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun v : α.fixedSubgroup => ((v : L) : G)) h
  exact Chapter1.mem_L_not_isSolvable hK
    (Group.isSolvable_of_isSolvable_injective (f := f) hf)

end CFSG.Quasithin.Chapter14.Section02
