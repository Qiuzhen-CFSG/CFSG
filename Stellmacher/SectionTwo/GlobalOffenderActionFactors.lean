module
public import Stellmacher.SectionTwo.QuotientOffenders
public import Stellmacher.SectionTwo.BaumannFixedPoints
public import Stellmacher.SectionOne.LemmaOneSeven

/-!
# Global offender factors on the original Section Two module

Use the named faithful quotient action on `V = ⟨Ω₁(Z(S))^G⟩`. When the
source's action-defined `J(V,q(S))` is nontrivial, the actual Baumann image
lies in it. Its normal closure has an injective family of one-seven factors,
normal in that closure, together with their original action modules and
the fixed complement.

Nontriviality of the action-defined J forces even quotient order; (2.1)
and quotient faithfulness supply the remaining Section One hypotheses.
The elementary Thompson image lies in J, so the Baumann image fixes the
J-fixed space and lies in the action Baumann subgroup, which (1.7) identifies
with J. The raw global factor family in the proof of (1.7) gives the common
group and module decomposition, retaining each factor's action predicate.
The product predicate records pairwise independence; no unrestricted product
cardinality is asserted.

Source: Stellmacher (6.4), assertions (1)–(3), Journal of Algebra 190 (1997),
p.31. The quotient bars in the journal scan are essential here.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem global_offender_action_factors
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)) :
    letI := quotientConjugationAction S q hq hker
    let J := SectionOne.oneJ (V := vSubgroup S) ((S : Subgroup G).map q)
    let E := SectionOne.oneE (V := vSubgroup S) ((S : Subgroup G).map q)
    J ≠ ⊥ → B.map q ≤ J ∧
      ∃ (n : ℕ) (D : Fin n → Subgroup barG),
        E = ⨆ i, D i ∧ IsInternalDirectProductFamily E D ∧ Function.Injective D ∧
        (∀ i, SectionOne.IsOneSevenFactor (V := vSubgroup S) (D i)) ∧
        (∀ i, ((D i).subgroupOf E).Normal) ∧
        IsInternalDirectProductFamily (⊤ : Subgroup (vSubgroup S))
          (fun i : Option (Fin n) => match i with
            | none => FixedPoints.subgroup E (vSubgroup S)
            | some i => commutatorAction (D i) (vSubgroup S)) := by
  classical
  let V := vSubgroup S
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let _ := quotientConjugationAction S q hq hker
  let T := S.mapSurjective hq
  let J := SectionOne.oneJ (V := V) (T : Subgroup barG)
  let E := SectionOne.oneE (V := V) (T : Subgroup barG)
  change J ≠ ⊥ → _
  intro hJ
  have hJS : J ≤ (T : Subgroup barG) := sSup_le fun A hA => hA.1
  have hTne : (T : Subgroup barG) ≠ ⊥ := by
    intro hb
    exact hJ (bot_unique (hb ▸ hJS))
  have htwo : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hone => hTne (Subgroup.card_eq_one.mp hone))
  let _ : Group.IsSolvable G := h.solvable
  have hOne : SectionOne.Hypotheses barG V :=
    ⟨Group.isSolvable_of_surjective hq,
      even_iff_two_dvd.mpr (htwo.trans (T : Subgroup barG).card_subgroup_dvd_card),
      quotientConjugationAction_faithful S q hq hker, lemma_two_one h S q hq hker⟩
  have hmaxJ : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≤ J :=
    elementaryAbelianMaxJ_map_le_oneJ h S q hq hker
  have hBfix := baumann_image_fixes_thompson_fixedPoints h S q hq hker B
    (hB ▸ inf_le_right)
  have hBJ : B.map q ≤ J := by
    rw [show J = SectionOne.oneJ (V := V) (T : Subgroup barG) from rfl,
      ← SectionOne.oneSeven_baumann_eq_j hOne T]
    refine le_inf (Subgroup.map_mono (hB ▸ inf_le_left)) ?_
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    apply ((mem_fixingSubgroup_iff (M := barG)).mp (hBfix hb)) v
    change v ∈ FixedPoints.subgroup J V at hv
    change v ∈ FixedPoints.subgroup ((elementaryAbelianMaxJ (S : Subgroup G)).map q) V
    rw [FixedPoints.mem_subgroup] at hv ⊢
    intro a
    exact hv ⟨a, hmaxJ a.property⟩
  obtain ⟨hEnormal, hprod, _hJE⟩ := SectionOne.oneSeven_global_product hOne T
  obtain ⟨_hJid, hEid⟩ := SectionOne.oneSeven_global_identification hOne T
  let E0 := SectionOne.oneSevenGenerated (G := barG) (V := V)
  let F := SectionOne.oneSevenFactors (G := barG) (V := V)
  let I := {D : Subgroup barG // D ∈ F}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup barG := fun i => (eI i).val
  have hDi (i : Fin n) : D i ∈ F := (eI i).property
  have hD (i : Fin n) : SectionOne.IsOneSevenFactor (V := V) (D i) :=
    (SectionOne.mem_oneSevenFactors_iff (D i)).mp (hDi i)
  have hinj : Function.Injective D := by
    intro i j hij
    exact eI.injective (Subtype.ext hij)
  change E = E0 at hEid
  change IsInternalDirectProduct E0 F at hprod
  have hgen : E0 = ⨆ i, D i := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro K
      obtain ⟨i, rfl⟩ := eI.surjective K
      exact le_iSup D i
    · exact iSup_le fun i => le_iSup (fun K : I => (K : Subgroup barG)) (eI i)
  have hfamily : IsInternalDirectProductFamily E0 D := by
    refine ⟨hgen, ?_, ?_⟩
    · intro i j hij
      exact hprod.2.2.1 (D i) (hDi i) (D j) (hDi j) (fun heq => hij (hinj heq))
    · intro i j hij
      exact hprod.2.2.2 (D i) (hDi i) (D j) (hDi j) (fun heq => hij (hinj heq))
  refine ⟨hBJ, n, D, ?_, ?_, hinj, hD, ?_, ?_⟩
  · exact hEid.trans hgen
  · change IsInternalDirectProductFamily E D
    rw [hEid]
    exact hfamily
  · intro i
    change ((D i).subgroupOf E).Normal
    rw [hEid]
    exact hprod.2.1 (D i) (hDi i)
  · exact SectionOne.oneSevenFactor_module_product hOne D hD hinj E (hEid.trans hgen)

end Stellmacher.SectionTwo
