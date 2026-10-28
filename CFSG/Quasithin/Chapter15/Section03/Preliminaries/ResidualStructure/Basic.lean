module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ResidualSplitting.QuotientData

/-!
# Residual and normalizer calculations for 15.3.7

The residual remains the literal `O²(⟨O₂(M ∩ Mc)^M⟩)` from Constructions.
Comparison with the prime-residual definition proves normality in `M`;
residual functoriality proves its action-image formula and two-perfectness.

The intersection factorization uses precisely the residual-centralizer or
unique-overgroup dichotomy in 15.3.2(4). Uniqueness for `YT` follows from
that same dichotomy once its nontrivial action is established. A nontrivial
two-core then puts the normalizer of `Y` in a two-local subgroup, where
maximality identifies it with `M`.

These are conditional components of 15.3.7, not its full source theorem.
The orthogonal image calculation and both complete three-group alternatives
remain to be assembled in ResidualStructure. The normalizer lemma's core
containment must be proved from the natural action in that assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 14.1.17 and 15.3.2(4), 15.3.7, printed pp.980, 1121–1122.
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G]

private theorem twoResidualSubgroup_eq [Finite G] (H : Subgroup G) :
    twoResidualSubgroup H = pResidual 2 H := by
  unfold twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    refine ⟨hN, ?_⟩
    let := hN
    exact IsPGroup.iff_card.mpr ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨hN, n, by simpa [Subgroup.index_eq_card] using hn⟩

/-- The actual source residual is normal inside `M`. -/
public theorem residualY_normal [Finite G] (M Mc : Subgroup G) :
    ((residualY M Mc).subgroupOf M).Normal := by
  unfold residualY Chapter14.SourcePreliminaries.sourceResidual
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  unfold twoResidualAmbient
  rw [twoResidualSubgroup_eq]
  exact ConjAct.normal_of_characteristic_of_normal

/-- The action image is the residual of the normal closure of the core image.
Computing this normal closure in the natural orthogonal actor remains necessary. -/
public theorem residualY_image [Finite G] (M Mc V : Subgroup G) (d : NaturalOrthogonalAction M V) :
    ((residualY M Mc).subgroupOf M).map d.actor =
    twoResidualAmbient
      (normalClosure ((((M ⊓ Mc).pCoreIn 2).subgroupOf M).map d.actor : Set OrthogonalActor)) := by
  unfold residualY Chapter14.SourcePreliminaries.sourceResidual
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  apply map_twoResidualAmbient_of_subgroup_image
  rw [map_normalClosure _ _ d.onto]
  rfl

/-- The intersection factorization in 15.3.7 follows from 15.3.2(4),
distinct maximal overgroups, and the preceding centralizer containment. -/
public theorem intersection_eq_centralizer_sup_sylow [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hMc : IsMaximalTwoLocal Mc) (hne : Mc ≠ M)
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc)
    (hcases : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
      twoResidualAmbient X ≤ centralizer (V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X M) :
    M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  have hTI : (T : Subgroup G) ≤ M ⊓ Mc := le_inf hTM hTMc
  have hres : twoResidualAmbient (M ⊓ Mc) ≤ centralizer (V : Set G) := by
    rcases hcases (M ⊓ Mc) hTI inf_le_left with hc | hu
    · exact hc
    · exact (hne (hu.2.2 Mc hMc inf_le_right)).elim
  have hs := congrArg (Subgroup.map (M ⊓ Mc).subtype)
    (twoResidualAmbient_top_sup_sylow (T.subtype hTI))
  have hr := map_twoResidualAmbient_of_subgroup_image
    (⊤ : Subgroup ↥(M ⊓ Mc : Subgroup G)) (M ⊓ Mc).subtype (M ⊓ Mc)
    (by rw [← MonoidHom.range_eq_map, range_subtype])
  rw [Subgroup.map_sup, hr, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTI,
    ← MonoidHom.range_eq_map, range_subtype] at hs
  apply le_antisymm ?_ (sup_le (le_inf inf_le_left hC) hTI)
  rw [← hs]
  exact sup_le (le_sup_of_le_left (le_inf ((map_subtype_le _).trans inf_le_left) hres))
    le_sup_right

/-- A normal subgroup with nontrivial two-core has the expected normalizer
inside a maximal two-local subgroup. -/
public theorem normalizer_eq_of_nontrivial_core (M Y V : Subgroup G) (hYM : Y ≤ M) (hM : IsMaximalTwoLocal M)
    (hYn : (Y.subgroupOf M).Normal)
    (hV : V ≠ ⊥) (hVY : V ≤ Y.pCoreIn 2) :
    normalizer (Y : Set G) = M := by
  have hN : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp hYn
  have hC : normalizer (Y : Set G) ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  have hne : Y.pCoreIn 2 ≠ ⊥ := fun h => hV (le_bot_iff.mp (h ▸ hVY))
  have hlocal : IsTwoLocal (normalizer (Y.pCoreIn 2 : Set G)) :=
    ⟨Y.pCoreIn 2, hne, isPGroup_pCoreIn 2 Y, rfl⟩
  exact le_antisymm (hC.trans (hM.2 hlocal (hN.trans hC))) hN

private theorem twoResidualAmbient_isPPerfect [Finite G] (H : Subgroup G) :
    IsPPerfect 2 (twoResidualAmbient H) := by
  intro N hN hp
  have h := BenderSuzuki.External.hktPResidual_le N hN hp
  rw [twoResidualAmbient_has_top_twoResidual] at h
  exact top_unique h

/-- The residual has no nontrivial two-group quotient. -/
public theorem residualY_isPPerfect [Finite G] (M Mc : Subgroup G) : IsPPerfect 2 (residualY M Mc) := by
  unfold residualY Chapter14.SourcePreliminaries.sourceResidual
  let H := twoResidualAmbient
    (normalClosure (((M ⊓ Mc).pCoreIn 2).subgroupOf M : Set M))
  exact (twoResidualAmbient_isPPerfect _).of_surjective
    (Subgroup.equivMapOfInjective H M.subtype M.subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective H M.subtype M.subtype_injective).surjective

private theorem le_twoResidualAmbient_of_isPPerfect [Finite G]
    (Y X : Subgroup G) (hYX : Y ≤ X) (hp : IsPPerfect 2 Y) :
    Y ≤ twoResidualAmbient X := by
  have h := map_pResidual_le 2 (Subgroup.inclusion hYX)
  rw [(pResidual_eq_top_iff 2 Y).mpr hp] at h
  have hm := map_mono (f := X.subtype) h
  rw [Subgroup.map_map, ← MonoidHom.range_eq_map,
    show X.subtype.comp (Subgroup.inclusion hYX) = Y.subtype from rfl,
    range_subtype] at hm
  simpa only [twoResidualAmbient, twoResidualSubgroup_eq] using hm

/-- Nontrivial action of the source residual forces uniqueness for `YT`
by the earlier 15.3.2(4) dichotomy. -/
public theorem residualY_unique_of_not_centralizing [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hnoncentral : ¬ residualY M Mc ≤ centralizer (V : Set G))
    (hcases : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
      twoResidualAmbient X ≤ centralizer (V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X M) :
    Chapter4.UniqueMaximalOvergroup (residualY M Mc ⊔ (T : Subgroup G)) M := by
  rcases hcases (residualY M Mc ⊔ (T : Subgroup G)) le_sup_right
    (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM) with hc | hu
  · have hle := le_twoResidualAmbient_of_isPPerfect _
      (residualY M Mc ⊔ (T : Subgroup G)) le_sup_left (residualY_isPPerfect M Mc)
    exact (hnoncentral (hle.trans hc)).elim
  · exact hu

/-- The star commutator bound from 14.1.17 propagates from `Rc` to the
actual normal-closure residual; all three subgroups live inside `M`. -/
public theorem residualY_commutator_le (M Mc : Subgroup G) (C Q : Subgroup M)
    [C.Normal] [Q.Normal]
    (hcomm : ⁅C, ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ Q) :
    ⁅C, (residualY M Mc).subgroupOf M⁆ ≤ Q := by
  unfold residualY Chapter14.SourcePreliminaries.sourceResidual
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  exact Chapter14.SourcePreliminaries.residual_normalClosure_commutator_le C _ Q hcomm

end CFSG.Quasithin.Chapter15.Section03
