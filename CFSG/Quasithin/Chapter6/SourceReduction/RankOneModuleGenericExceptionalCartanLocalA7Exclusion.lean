module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOrder
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalExtensionRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.NaturalBlockAlternative
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalModule

/-!
# Completing the original local Cartan omega-centralization

The Sylow order argument exhausts the right two-core by its natural
four-space. Restricting the original A7 action to the literal right
residual constructs an elementary natural extension, hence the forbidden
right block. This closes the degree-two left-block case and proves the
original universal A7 exclusion. The proved FF reduction then gives
omega-centralization of the witnessed component with no block premise.

At degree two the existing whole-module recognition now applies without
an A7-exclusion callback. The universal postcentralization degree argument
and the original witness sieve remain separate source obligations.
Source: Aschbacher–Smith 5.1.13, printed pp.637–638, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
/-- With the right core exhausted by its natural four-space, the literal
right residual is a natural block. -/
theorem LocalA7Configuration.right_block_of_core_eq_four
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hcore : (K ⊔ (T : Subgroup G)).pCoreIn 2 = localOmegaModule T K) :
    ChapterC.IsChiBlockIn (pResidual 2 H) := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let R := (residual H).subgroupOf M
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  obtain ⟨q,hq,hk,hQ,_,e,f,hf⟩ := a.four_residual_natural h hH hgen c d
  have hQU : pCore 2 M = U := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le a.reduced.1]
    exact hcore
  have hqU : q.ker = U := hQ.trans hQU
  have hUH : localOmegaModule T K ≤ H := by
    rw [←(a.right_omega_span_reduced h hH hgen c d).1]
    exact conjugateSpanBy_le_self
      ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from fun z hz =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans hH.1.1.2)
  have hUR : U ≤ R := by
    intro u hu
    have hh := (a.four_residual_full_movement h hH hgen c d).symm.le.trans
      (le_normalizer_iff_commutator_le_right.mp (hUH.trans (le_normalizer_residual H)))
    exact hh hu
  let V := U.subgroupOf R
  let ev : V ≃* U := subgroupOfEquivOfLe hUR
  let actor := e.toMonoidHom.comp (q.subgroupMap R)
  have hactor : Function.Surjective actor := e.surjective.comp (q.subgroupMap_surjective R)
  have hker : actor.ker = V := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,ker_subgroupMap,hqU]
  have hV : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective ev.toMonoidHom ev.injective
  let em : V ≃* Multiplicative (Fin 2 → SL2FourNatural.F) :=
    ev.trans f.toAddEquiv.toMultiplicativeRight
  have hF : Nat.card SL2FourNatural.F = 2^2 := by
    rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    decide
  have hel (r : R) (v : V) :
      (em (Theory.SpecificGroups.SymplecticFour.extensionConjugate V r v)).toAdd =
        (actor r).val.mulVec (em v).toAdd := by
    have hv : Additive.ofMul (ev (Theory.SpecificGroups.SymplecticFour.extensionConjugate V r v)) =
        NormalElementaryQuotient.representation U q hq hk (q r.val) (Additive.ofMul (ev v)) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply]
      rfl
    change f (Additive.ofMul (ev (Theory.SpecificGroups.SymplecticFour.extensionConjugate V r v))) = _
    rw [hv]
    exact hf (q.subgroupMap R r) (Additive.ofMul (ev v))
  have hnat : ChapterC.IsL2EvenBlock R 2 :=
    ChapterC.isL2EvenBlock_of_naturalExtension
      (Theory.SpecificGroups.SymplecticFour.naturalExtensionOfNatural hV actor hactor hker
        (by rw [hF]; decide) em hel) (by decide) hF
  have hRM : residual H ≤ M := (d.residual_le.trans a.contains).trans le_sup_left
  let er : R ≃* pResidual 2 H := (subgroupOfEquivOfLe hRM).trans
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  have hb : ChapterC.IsL2EvenBlock (pResidual 2 H) 2 := hnat.of_equiv er
  exact ⟨⟨inferInstance,hb.2.1,Normal.isSubnormal inferInstance⟩,Or.inl ⟨2,hb⟩⟩

/-- The remaining degree-two left-block configuration is impossible. -/
theorem LocalA7Configuration.impossible
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) : False :=
  a.not_right_block h hH hgen c d
    (a.right_block_of_core_eq_four h hH hgen c d (a.right_core_eq_four h hH hgen c d))

/-- The original noncentral A7 exclusion, with both block branches discharged. -/
theorem localCartan_a7Exclusion : LocalCartanA7Exclusion G := by
  intro T L W n h H hH hgen A B c Y _ X D d K a
  exact a.impossible h hH hgen c d

/-- The actual witnessed component centralizes the original Sylow omega-center. -/
theorem localCartan_centralizes
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) : X ≤ omegaCentralizer T := by
  by_contra hc
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hc
  exact a.impossible h hH hgen c d

/-- At degree two, the witnessed source inputs prove centralization and
recognize all of the original moved module, including its multiplicity. -/
theorem localCartan_centralization_degree_two
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    X ≤ omegaCentralizer T ∧ IsOneOrTwoA5Modules L (layer L W) := by
  have hc := localCartan_centralizes h hH hgen c hY d
  exact ⟨hc,d.module_of_exponent_eq_two h hH c hc rfl⟩

/-- At degree two only the original component-and-cubic sieve remains
explicit in the full exceptional conclusion and its relative relocation. -/
theorem localCartan_escape_of_sieve_degree_two
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L W H A B Y : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    CartanExceptionalConclusion T L W H :=
  localCartan_escape_of_sieve_a7_degree_two hsieve localCartan_a7Exclusion h hH hgen c hY hescape
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
