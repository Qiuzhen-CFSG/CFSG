module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ComponentPlacement
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NormalDiagram
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.ComponentStructure.Source

/-!
# Diagram exchange for every terminal component with a surviving model

The component stabilizer N_T(K) permutes the two actual maximal parabolics
of the marked L₃(2) or A₆ quotient over its Sylow. If it fixed both,
ComponentPlacement would place both lifts in M. They generate the
component modulo its two-core, which already lies in T, so K would lie
in M, contradicting SourceOrbit. Hence an element of N_T(K) exchanges
the two nodes, whether or not the full T normalizes K.

The terminal consumer combines this action with the proved one/two-component
alternatives at the unchanged H=Mc. The individual component models remain
an explicit earlier step, discharged by the remaining sieve owned by
qt-e-suitable-component-supports. Original 14.6.18 remains with
qt-e-14625-source. No natural-module identification is inferred here.

Source: Aschbacher--Smith 14.6.20--21, printed pp.1037--1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Subgroup.NormalSylowQuotientAction
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Theory.SpecificGroups.SymmetricSix
variable {G B : Type*} [Group G] [Finite G] [Group B] [Finite B]

omit [Finite B] in
private theorem component_pair_swap_of_solvable_placement
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hout : ¬ K ≤ M)
    (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* B)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J L : Subgroup B) [Group.IsSolvable J] [Group.IsSolvable L]
    (hJ : IsCoatom J) (hL : IsCoatom L) (hne : J ≠ L) (hsup : J ⊔ L = ⊤)
    (hPJ : (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ J)
    (hPL : (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ L)
    (hall : ∀ N : Subgroup B, IsCoatom N →
      (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ N → N = J ∨ N = L) :
    ∃ s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G), J.map (markedCoreAction 2 K eK ⟨s,s.property.2⟩).toMonoidHom = L ∧
      L.map (markedCoreAction 2 K eK ⟨s,s.property.2⟩).toMonoidHom = J := by
  let a (s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G)) := markedCoreAction 2 K eK ⟨s,s.property.2⟩
  have hm (s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G)) (N : Subgroup B) (hN : IsCoatom N)
      (hPN : (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ N) :
      N.map (a s).toMonoidHom = J ∨ N.map (a s).toMonoidHom = L := by
    apply hall _ (((a s).mapSubgroup.isCoatom_iff N).mpr hN)
    have hh := map_mono (f := (a s).toMonoidHom) hPN
    rwa [markedCoreAction_preserves_component_sylow 2 T K eK P hP s] at hh
  have hmove : ∃ s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G), J.map (a s).toMonoidHom ≠ J := by
    by_contra! hf
    have hl (s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G)) : L.map (a s).toMonoidHom = L := by
      rcases hm s L hL hPL with he | he
      · exact (hne ((a s).mapSubgroup.injective ((hf s).trans he.symm))).elim
      · exact he
    have hJM := source_component_solvable_le_image T M hsolv H hH K hKH hK eK J hf
    have hLM := source_component_solvable_le_image T M hsolv H hH K hKH hK eK L hl
    let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    have hmap : (M.subgroupOf K).map q = ⊤ := by
      apply top_unique
      rw [←hsup]
      exact sup_le hJM hLM
    have hker : q.ker = pCore 2 K := by
      rw [MonoidHom.ker_comp_of_injective _ _ eK.injective, QuotientGroup.ker_mk']
    have hkM : q.ker ≤ M.subgroupOf K := by
      rw [hker]
      apply (pCore_isPGroup.le_sylow_of_normal P).trans
      rw [hP]
      exact fun _ hx => hTM hx
    have hMtop : M.subgroupOf K = ⊤ := by
      have hh := congrArg (Subgroup.comap q) hmap
      rwa [comap_map_eq,sup_eq_left.mpr hkM,comap_top] at hh
    exact hout fun k hk => show (⟨k,hk⟩ : K) ∈ M.subgroupOf K from hMtop ▸ mem_top _
  obtain ⟨s,hs⟩ := hmove
  have he : J.map (a s).toMonoidHom = L := (hm s J hJ hPJ).resolve_left hs
  refine ⟨s,he,?_⟩
  rcases hm s L hL hPL with hl | hl
  · exact hl
  · exact (hne ((a s).mapSubgroup.injective (he.trans hl.symm))).elim

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)

/-- A nontrivial action on the two actual parabolics over the quotient Sylow.
This retains the same model isomorphism and the induced normalizer action. -/
@[expose] def ComponentParabolicSwap (T : Sylow 2 G) (K : Subgroup G)
    (eK : (K ⧸ pCore 2 K) ≃* B) : Prop :=
  ∃ P : Sylow 2 K, (P : Subgroup K) = (T : Subgroup G).subgroupOf K ∧
    ∃ J L : Subgroup B, IsCoatom J ∧ IsCoatom L ∧ J ≠ L ∧
      J ⊓ L = (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ∧
      (∀ N : Subgroup B, IsCoatom N →
        ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ N ↔
          N = J ∨ N = L)) ∧
      ∃ s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G), J.map (markedCoreAction 2 K eK ⟨s,s.property.2⟩).toMonoidHom = L ∧
        L.map (markedCoreAction 2 K eK ⟨s,s.property.2⟩).toMonoidHom = J

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- In every binary L₃ component branch, an original element of N_T(K) exchanges the
literal point and line parabolics of the marked quotient. -/
theorem source_l3_component_parabolic_swap
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL) :
    ComponentParabolicSwap T K eK := by
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.1.2 hKH hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  obtain ⟨J,L,hJ,hL,hne,hi,hcardJ,hcardL,hall⟩ := Matrix.PSL3Two.sylow_parabolics Pq
  have hPJ : (Pq : Subgroup Matrix.PSL3Two.PSL) ≤ J := hi ▸ inf_le_left
  have hPL : (Pq : Subgroup Matrix.PSL3Two.PSL) ≤ L := hi ▸ inf_le_right
  have hsup : J ⊔ L = ⊤ := hJ.2 _ (lt_of_le_of_ne le_sup_left (by
    intro he
    have hh : L ≤ J := sup_eq_left.mp he.symm
    exact hne ((eq_of_le_of_not_lt hh (fun hlt => hJ.1 (hL.2 J hlt))).symm)))
  have hpc : Nat.card (Pq : Subgroup Matrix.PSL3Two.PSL) = 8 :=
    (Nat.card_congr (Pq.equiv Matrix.PSL3Two.borelSylow).toEquiv).trans Matrix.PSL3Two.card_borel
  have hindexJ : (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex J = 3 := by
    have hh := ((Pq : Subgroup Matrix.PSL3Two.PSL).subgroupOf J).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv,hpc,hcardJ] at hh
    change 8 * (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex J = 24 at hh
    omega
  have hindexL : (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex L = 3 := by
    have hh := ((Pq : Subgroup Matrix.PSL3Two.PSL).subgroupOf L).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv,hpc,hcardL] at hh
    change 8 * (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex L = 24 at hh
    omega
  let : Group.IsNilpotent (Pq : Subgroup Matrix.PSL3Two.PSL) := Pq.isPGroup'.isNilpotent
  let : Group.IsSolvable J := (Pq : Subgroup Matrix.PSL3Two.PSL).isSolvable_of_relIndex_le_four J (by omega)
  let : Group.IsSolvable L := (Pq : Subgroup Matrix.PSL3Two.PSL).isSolvable_of_relIndex_le_four L (by omega)
  refine ⟨P,hP,J,L,hJ,hL,hne,hi,hall,?_⟩
  exact component_pair_swap_of_solvable_placement T M hM.1.2 hsolv H hH.1 K hKH
    (source_component_not_le hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
    hK eK P hP J L hJ hL hne hsup hPJ hPL (fun N hN hp => (hall N hN).mp hp)

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- In every A₆ component branch the action exchanges duad and syntheme parabolics.
Thus the conclusion detects the diagram action, not just an outer automorphism. -/
theorem source_a6_component_parabolic_swap
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    ComponentParabolicSwap T K eK := by
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.1.2 hKH hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  obtain ⟨g,hg,hall⟩ := a6_coatoms_over_sylow Pq
  let a := (MulAut.conj g).mapSubgroup
  let J := a a6DuadStabilizer
  let L := a a6SynthemeStabilizer
  have hJ := (hall J).mpr (Or.inl rfl)
  have hL := (hall L).mpr (Or.inr rfl)
  have hne : J ≠ L := fun he => Theory.SpecificGroups.SymmetricSix.a6_parabolics_ne (a.injective he)
  have hi : J ⊓ L = (Pq : Subgroup (alternatingGroup (Fin 6))) := by
    rw [show J = a _ from rfl, show L = a _ from rfl, ← a.map_inf,
      Theory.SpecificGroups.SymmetricSix.a6_parabolics_inf,hg]
  have hs : J ⊔ L = ⊤ := by
    rw [show J = a _ from rfl, show L = a _ from rfl, ← a.map_sup,
      Theory.SpecificGroups.SymmetricSix.a6_parabolics_sup,a.map_top]
  let : Group.IsSolvable J := Group.isSolvable_of_surjective
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)
  let : Group.IsSolvable L := Group.isSolvable_of_surjective
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)
  have he : ∀ N : Subgroup (alternatingGroup (Fin 6)), IsCoatom N →
      ((Pq : Subgroup (alternatingGroup (Fin 6))) ≤ N ↔ N = J ∨ N = L) := by
    intro N hN
    exact ⟨fun hp => (hall N).mp ⟨hN,hp⟩,fun hh => ((hall N).mpr hh).2⟩
  refine ⟨P,hP,J,L,hJ.1,hL.1,hne,hi,he,?_⟩
  exact component_pair_swap_of_solvable_placement T M hM.1.2 hsolv H hH.1 K hKH
    (source_component_not_le hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
    hK eK P hP J L hJ.1 hL.1 hne hs hJ.2 hL.2 (fun N hN hp => (hall N).mp ⟨hN,hp⟩)


/-- The two actual component markings with the original nontrivial diagram action. -/
@[expose] def ComponentModelDiagram (T : Sylow 2 G) (K : Subgroup G) : Prop :=
  (∃ a : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL, ComponentParabolicSwap T K a) ∨
  (∃ a : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6), ComponentParabolicSwap T K a)

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- Once the two quotient models are known, every original component has
the required diagram action. The exchanged-component branch needs no extra input. -/
theorem source_component_diagram_of_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hm : ComponentQuotientModels K) : ComponentModelDiagram T K := by
  change Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∨
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) at hm
  rcases hm with ha | ha
  · let a := Classical.choice ha
    let b := a.trans Matrix.PSL3Two.equiv
    exact Or.inl ⟨b,source_l3_component_parabolic_swap hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK b⟩
  · let a := Classical.choice ha
    exact Or.inr ⟨a,source_a6_component_parabolic_swap hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK a⟩

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- Actual terminal consumer: the structural alternatives and diagram action
follow together from individual component models, with H fixed to Mc. -/
theorem terminal_alternatives_with_diagram_of_component_models
    (hm : ∀ J : Subgroup G, J ≤ Mc → (J.subgroupOf Mc).IsCComponent → ComponentQuotientModels J)
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    TerminalComponentAlternatives T Mc K ∧ ComponentModelDiagram T K := by
  exact ⟨terminal_alternatives_of_component_models hG T hempty hM hunique hmany hcard e hab hsolv
    hm K hKM hK,
    source_component_diagram_of_models hG T hempty hM hunique hmany hcard e hab hsolv Mc
      (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK (hm K hKM hK)⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
