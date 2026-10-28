module
public import Stellmacher.SectionOne.OneASL2Factors
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Theory.GroupAction.CommutatorDecomposition

/-!
# A factor support detecting a nontrivial offender

Under the faithful elementary-abelian action hypotheses of Section One,
every nontrivial offender Y has a nonidentity commutator point lying in
the support of a raw factor from Stellmacher (1.7). Neither fixed index
two nor fixedness under the ambient Sylow subgroup is required.

The local classification writes `[oddCore K,Y]Y` as an internal product
of raw factors. Each factor is normal in this product, so Y normalizes
it and preserves its action support. The proved factor-module decomposition
splits V into these supports and the product's fixed space. The general
invariant-summand commutator theorem then expresses `[V,Y]` as the join
of its intersections with those supports. Faithfulness makes `[V,Y]`
nontrivial, and hence at least one intersection contains a nonidentity point.
This is the support-selection input for the Sylow-fixed transvection
argument; it does not assert that every ambient Sylow normalizes a factor.

Source: the local and global factor constructions in the proof of
Stellmacher (1.7), printed p.19 (PDF page 9) of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne
universe u

public theorem oneSeven_factor_support_meets_offender
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (U : Sylow 2 K) (Y : Subgroup K)
    (hY : oneA (V := V) (U : Subgroup K) Y) (hne : Y ≠ ⊥) :
    ∃ D : Subgroup K, IsOneSevenFactor (V := V) D ∧
      ∃ v : V, v ≠ 1 ∧ v ∈ commutatorAction D V ∧ v ∈ commutatorAction Y V := by
  classical
  obtain ⟨F, hprod, hF⟩ := oneA_sl2_factors h U Y hY hne
  let E : Subgroup K := ⁅oddCore K, Y⁆ ⊔ Y
  change IsInternalDirectProduct E F at hprod
  let I := {D : Subgroup K // D ∈ F}
  let n := Fintype.card I
  let enum : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup K := fun index => (enum index).val
  have hDi (index : Fin n) : D index ∈ F := (enum index).property
  have hfactor (index : Fin n) : IsOneSevenFactor (V := V) (D index) :=
    hF (D index) (hDi index)
  have hinj : Function.Injective D := by
    intro first second heq
    exact enum.injective (Subtype.ext heq)
  have hgen : E = ⨆ index, D index := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro factor
      obtain ⟨index, rfl⟩ := enum.surjective factor
      exact le_iSup D index
    · exact iSup_le fun index => le_iSup (fun factor : I => (factor : Subgroup K))
        (enum index)
  have hmodule := oneSevenFactor_module_product h D hfactor hinj E hgen
  have hinvariant (index : Fin n) : IsInvariant Y V (commutatorAction (D index) V) := by
    have hDE : D index ≤ E := by rw [hgen]; exact le_iSup D index
    have hnorm : E ≤ Subgroup.normalizer (D index : Set K) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp
        (hprod.2.1 (D index) (hDi index))
    exact commutatorAction_isInvariant_of_normalizing_actor Y (D index)
      ((show Y ≤ E from le_sup_right).trans hnorm)
  have hsplit : commutatorAction Y V =
      ⨆ index, commutatorAction Y V ⊓ commutatorAction (D index) V := by
    apply commutatorAction_eq_iSup_inf_of_fixed_sup (FixedPoints.subgroup E V)
      (fun index => commutatorAction (D index) V) ?_ ?_ hinvariant
    · have htop := hmodule.1.symm
      rw [iSup_option] at htop
      exact htop
    · intro actor vector hvector
      exact (FixedPoints.mem_subgroup (M := E) (a := vector)).mp hvector
        ⟨actor, (show Y ≤ E from le_sup_right) actor.property⟩
  have hcomm : commutatorAction Y V ≠ ⊥ := by
    intro hbot
    apply hne
    apply le_bot_iff.mp
    rw [← h.action_faithful]
    intro actor hactor
    rw [mem_fixingSubgroup_iff]
    intro vector _
    exact actsTrivially_of_commutatorAction_eq_bot hbot ⟨actor, hactor⟩ vector
  have hex : ∃ index, commutatorAction Y V ⊓ commutatorAction (D index) V ≠ ⊥ := by
    by_contra hnone
    push Not at hnone
    apply hcomm
    rw [hsplit]
    simp only [hnone, iSup_bot]
  obtain ⟨index, hindex⟩ := hex
  obtain ⟨vector, hvector, hvne⟩ :=
    (commutatorAction Y V ⊓ commutatorAction (D index) V).bot_or_exists_ne_one.resolve_left hindex
  exact ⟨D index, hfactor index, vector, hvne, hvector.2, hvector.1⟩

end Stellmacher.SectionOne
