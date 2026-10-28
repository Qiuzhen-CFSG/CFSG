module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentAction
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalDeletedDescent
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.MarkingFormulas

/-!
# The deleted constituent retains the original point quotient

In the alternating-eight row, the original point-component quotient is the
actual hatted actor. The entire point centralizer acts on the chosen central
quotient, and the trivial deleted-module commutant forces that action through
the same hatted quotient. The returned coordinates intertwine every original
conjugator; no two-core identification for the full hatted kernel is assumed.
Source: Aschbacher--Smith 12.9.4, printed p.860.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V I : Subgroup G}

/-- The actual deleted central quotient admits full point-centralizer
coordinates with the unchanged hatted projection and original conjugation. -/
theorem nonabelian_caseFive_deleted_point_model
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (c : ChosenModule T C.K1 I) (hiZ : I ≤ F.ZU) :
    letI := c.actionCentralizer_normal
    ActionEquiv c.faithfulCentralAction (alternatingNatural 8) →
    ∃ (hHI : F.H ≤ normalizer (I : Set G))
      (ρ : Representation (ZMod 2) F.H c.chosenCentralQuotient)
      (e : F.TerminalHdot ≃* alternatingGroup (Fin 8))
      (E : c.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8)),
      (∀ a w, E (ρ a w) = BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
        (e (QuotientGroup.mk' F.terminalHatAction.ker a)) (E w)) ∧
      ∀ (a : F.H) (v : I), ρ a (c.toCentralQuotient v).toAdd =
        (c.toCentralQuotient (I.normalizerMonoidHom (inclusion hHI a) v)).toAdd := by
  let := c.actionCentralizer_normal
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  intro a
  have hHI := nonabelian_caseFive_point_normalizes_chosen
    modules h preferred earlier F hne g hgP hgH B h5 C c hiZ
  have hHK := (normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal
  obtain ⟨ρ, hj, he⟩ := exists_chosen_central_action_of_normalizes c hHI C.point_le hHK
  obtain ⟨e₀, he₀⟩ := nonabelian_caseFive_point_core_equiv h earlier F hne B h5 C
  obtain ⟨b⟩ := nonabelian_caseFive_alternating_eight h (Or.inl rfl) earlier F hne B h5
  have hs : IsSimpleGroup (C.K1 ⧸ pCore 2 C.K1) := (e₀.trans b).isSimpleGroup
  let e := (e₀.symm.trans (c.coreToFaithfulEquiv hs)).trans a.groupEquiv
  let K := C.K1.subgroupOf F.H
  let : K.Normal := C.normal
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hqK : Function.Surjective (q.comp K.subtype) := by
    intro x
    obtain ⟨y, rfl⟩ := e₀.surjective x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C.K1) y
    refine ⟨(subgroupOfEquivOfLe C.point_le).symm k, ?_⟩
    exact (he₀ k).symm
  have hE : ∀ (k : K) w, a.linearEquiv (ρ k w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e (q k))
        (a.linearEquiv w) := by
    intro k w
    let k' := (subgroupOfEquivOfLe C.point_le) k
    have hρ : ρ k = c.chosenCentralAction k' := hj k'
    have hq : q k = e₀ (QuotientGroup.mk' (pCore 2 C.K1) k') := (he₀ k').symm
    rw [hρ, hq]
    change a.linearEquiv (c.chosenCentralAction k' w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
        (a.groupEquiv (c.coreToFaithfulEquiv hs
          (e₀.symm (e₀ (QuotientGroup.mk' (pCore 2 C.K1) k'))))) (a.linearEquiv w)
    rw [e₀.symm_apply_apply, c.coreToFaithfulEquiv_mk]
    exact a.intertwines (QuotientGroup.mk' ((centralizer (I : Set G)).subgroupOf C.K1) k') w
  obtain ⟨σ, hσ, hmodel⟩ := exists_deleted_eight_action_descent K q hqK ρ e a.linearEquiv hE
  refine ⟨hHI, σ.comp q, e, a.linearEquiv, ?_, ?_⟩
  · intro x w
    exact hmodel (q x) w
  · intro x v
    change σ (q x) (c.toCentralQuotient v).toAdd = _
    rw [hσ]
    exact he x v

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
