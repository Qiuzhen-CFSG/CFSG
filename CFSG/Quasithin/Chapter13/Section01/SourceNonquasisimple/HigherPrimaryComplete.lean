module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.HigherPrimaryControl
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.HigherPrimarySwapped
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OddStarModels

/-!
# Excluding the original higher-primary radical escape

The active higher homocyclic primary radical supplies characteristic-normalizer
control for R=O₂(Ξ_p(L)T). The resulting Configuration uses the original
canonical radical, its chosen Sylow p-subgroup, and N_G(L). The actual escaping
component from HigherPrimarySwapped consequently satisfies the literal
PushingUpComponent conditions. The proved even and odd swapped-model
contradictions eliminate both rank-one possibilities.

Thus failure of the solvable radical to centralize [R₂(N_G(L)),L] now produces
only the original nonnormal faithful quasisimple Chapter10 configuration.
No characteristic-control, block, Sylow, or C.2.7-classification premise remains
in this reduction; the Chapter10 normalization argument remains separate.
Source: Aschbacher--Smith13.1.4(5), p.867;3.2.14, p.585;
1.3.8, pp.513--514; C.2.7, pp.144--145.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions Chapter12.Section02 ChapterA.Section04
open Chapter3.RadicalCentralization
universe u
variable {G : Type u} [Group G] [Finite G]
open Chapter1.XiEmbedding Chapter1.RadicalExclusions Chapter1.RadicalExclusions.ModelReduction

/-- The active higher-primary source supplies the literal radical exclusion
configuration, with the original Sylow complement and original two-core. -/
theorem active_higher_primary_configuration
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p a : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 5 < p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (primaryRadical p L) ≠ ⊥) (ha : 1 ≤ a)
    (e : Nonempty (XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a))))
    (P : Sylow p (XiP p L)) :
    Configuration p T (XiP p L) ((P : Subgroup (XiP p L)).map (XiP p L).subtype)
      L (normalizer (L : Set G)) := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hQ := uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.2.2
  obtain ⟨hs,hN,hM⟩ := RadicalConjugateRigidity.maximal_radical_structure
    h.simpleQTKE T hL hn ho hd
  exact ⟨Fact.out,ho,by omega,
    (XiP_mem_XiPlus_source h.simpleQTKE T hL.1 hn ho hd).1,rfl,hL,hs,⟨P,rfl⟩,
    XiP_automizer_not_isCyclic_of_A36 h36 hL.1 hQ hn ho hd P,
    XiP_normalizer_irreducible_of_A36 h36 hL.1 hQ hn ho hd P,rfl,hN.symm,hM,
    active_higher_primary_characteristic_control h hmany hL hn ho hd hi ha e⟩

/-- The original active higher homocyclic primary alternative is impossible.
The literal escaping component receives the actual characteristic control,
and both swapped model alternatives satisfy the proved C.2.7 contradictions. -/
theorem active_higher_primary_impossible
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p a : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 5 < p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (primaryRadical p L) ≠ ⊥) (ha : 2 ≤ a)
    (e : Nonempty (XiQuotient (primaryRadical p L) ≃* Multiplicative (Fin 2 → ZMod (p^a)))) :
    False := by
  let P : Sylow p (XiP p L) := default
  let X := XiP p L
  let P₀ := (P : Subgroup X).map X.subtype
  let M := normalizer (L : Set G)
  have hc : Configuration p T X P₀ L M :=
    active_higher_primary_configuration h hmany hL hn ho hp hd hi (by omega) e P
  obtain ⟨H,K,hH,hIH,hout,hK,hKL,hq,hXK,hdinput,hplane,hs,hm,hKout,hF,hR,hRI⟩ :=
    active_higher_primary_escaping_swapped h hmany hL hn ho hp hd hi ha e P
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hIH
  have hXH : X ⊔ (T : Subgroup G) ≤ H :=
    (sup_le_sup_right (XiP_le_primaryRadical L hc.quotient) _).trans hIH
  have hSH : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hOver : H ∈ HOver G (T : Set G) := ⟨mem_H_of_isTwoLocal hH.1,hTH⟩
  have hcand : PushingUpComponent KnownSimple.IsKnownSimple p T X P₀ M H K :=
    { overgroup := hOver
      local_input := hdinput
      sylow_two := hSH
      component := hK
      quasisimple := hq
      containment := hXK
      alternatives := ⟨hplane,Or.inl ⟨hs,hm⟩⟩
      setup := hc.pushingUp_setup T (h.simpleQTKE.twoLocal_sqtk hH.1) hXH
      fitting := hF
      outside := fun hh => hKout (hh.trans inf_le_right)
      radical_normalizes := hR }
  exact hcand.false_of_swapped T hc
    (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)) hs hm

/-- Original radical movement now forces only the genuine nonnormal faithful
quasisimple Chapter 10 configuration; the higher-primary escape is eliminated. -/
theorem radical_moved_action_nonnormal_faithful
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (ha : ¬ (solvableRadical L).map L.subtype ≤ centralizer (normalizerMoved L : Set G)) :
    ∃ K : Subgroup G, Hypothesis1221 KnownSimple.IsKnownSimple T K ∧
      ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
  rcases radical_moved_action_obstruction h hmany hL hn ha with
    he | ⟨p,hp,ho,hp5,hd,hi,a,ha,e,_⟩
  · exact he
  · let : Fact p.Prime := ⟨hp⟩
    exact (active_higher_primary_impossible h hmany hL.1 hn ho hp5 hd hi ha e).elim

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
