module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.TerminalJanko
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.TerminalComponent
/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.TerminalJanko`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.TerminalJanko
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.TerminalJanko
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open OriginalPlaneCentralizers Chapter12.Section02
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
set_option backward.isDefEq.respectTransparency true
variable {G : Type*} [Group G] [Finite G]

/-- The two-primary multiplier bound removes precisely the original central cover. -/
theorem center_eq_bot {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hcore : pCore 2 X = ⊥) (e : X ⧸ center X ≃* Janko4.Model) : center X = ⊥ := by
  have hz : center X ≤ pCore 2 X :=
    le_sSup ⟨inferInstance,Janko4.OddPrimary.center_isPGroup_of_quotient_equiv e⟩
  exact bot_unique (hcore ▸ hz)

/-- The component equivalence is the supplied quotient marking composed with
its original quotient map. -/
@[expose] def componentEquiv {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hcore : pCore 2 X = ⊥) (e : X ⧸ center X ≃* Janko4.Model) : X ≃* Janko4.Model :=
  MulEquiv.ofBijective (e.toMonoidHom.comp (QuotientGroup.mk' (center X))) ⟨by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',center_eq_bot hcore e],
    e.surjective.comp (QuotientGroup.mk'_surjective _)⟩

theorem componentEquiv_apply {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hcore : pCore 2 X = ⊥) (e : X ⧸ center X ≃* Janko4.Model) (x : X) :
    componentEquiv hcore e x = e (QuotientGroup.mk' (center X) x) := rfl

/-- The literal residual in the selected component is normal in an actual
maximal two-local of the model. The original module supplies its nontrivial
binary normalizer witness. -/
theorem original_native_local
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V) (A : Subgroup G)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G))) (hK : IsComponent (normalizer (A : Set G)) K)
    (hcore : pCore 2 K = ⊥)
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hRK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : K ⧸ center K ≃* Janko4.Model) :
    ∃ (M : Subgroup Janko4.Model) (B : Subgroup M),
      IsMaximalTwoLocal M ∧ B.Normal ∧
      Nonempty (B ⧸ pCore 2 B ≃* Atlas.G2.Natural.BinaryNormalizer.Derived) := by
  let := hK.2
  let N := normalizer (A : Set G)
  let J := K.map N.subtype
  let R := oddActorResidual L A
  let d : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let c : J ≃* Janko4.Model := d.trans (componentEquiv hcore e)
  let f : R →* Janko4.Model := c.toMonoidHom.comp (inclusion hRK)
  let E := (V.subgroupOf J).map c.toMonoidHom
  have hEV : E ≃* V := (c.subgroupMap (V.subgroupOf J)).symm.trans
    (subgroupOfEquivOfLe hVK)
  have hp : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 V).of_equiv hEV.symm
  have hne : E ≠ ⊥ := by
    intro hz
    have hv : Nat.card V = 1 := (Nat.card_congr hEV.toEquiv).symm.trans (hz ▸ card_bot)
    exact s.chosen.ne_bot (card_eq_one.mp hv)
  have hRV : R ≤ normalizer (V : Set G) :=
    ((oddActorResidual_le L A).trans inf_le_left).trans s.chosen.normalizes
  have hRN : R.subgroupOf J ≤ normalizer (V.subgroupOf J : Set J) := by
    intro r hr v
    exact hRV hr (v : G)
  have hfN : f.range ≤ normalizer (E : Set Janko4.Model) := by
    have hrange : f.range = (R.subgroupOf J).map c.toMonoidHom := by
      rw [MonoidHom.range_comp]
      congr 1
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
    rw [hrange]
    exact (map_mono hRN).trans (le_normalizer_map c.toMonoidHom)
  obtain ⟨M,hNM,hM⟩ := (show IsTwoLocal (normalizer (E : Set Janko4.Model)) from
    ⟨E,hne,hp,rfl⟩).exists_le_maximal
  have hfM : f.range ≤ M := hfN.trans hNM
  have hker : c.toMonoidHom.ker ≤ center J := by
    rw [c.toMonoidHom.ker_eq_bot_iff.mpr c.injective]
    exact bot_le
  have hn := (NormalizedRankOneOddControl.central_quotient_parabolic_normality
    (map_subtype_le K) hRK hu c.toMonoidHom c.surjective hker M hM.1 hfM).2
  let B := f.range.subgroupOf M
  have hfi : Function.Injective f := c.injective.comp (inclusion_injective hRK)
  let b : B ≃* R := (subgroupOfEquivOfLe hfM).trans (MonoidHom.ofInjective hfi).symm
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  obtain ⟨a,_⟩ := chosen_oddActorResidual_quotient h12 s.chosen A hAN hcomm hodd hAV
  exact ⟨M,B,hM,hn,⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (a.trans s.quotient)⟩⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.TerminalJanko

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open OriginalPlaneCentralizers Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The terminal odd-normalizer component cannot have J₄ central quotient.
The literal residual and whole chosen module lie in that same component;
residual uniqueness supplies normality in the native local selected from V. -/
theorem unitary_original_terminal_janko_false
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V) (A : Subgroup G)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G))) (hK : IsComponent (normalizer (A : Set G)) K)
    (hcore : pCore 2 K = ⊥)
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hRK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : K ⧸ center K ≃* Janko4.Model) : False := by
  obtain ⟨M,B,hM,hn,⟨b⟩⟩ :=
    TerminalJanko.original_native_local s A hAN hcomm hodd hAV hu K hK hcore hVK hRK e
  let := hn
  exact Janko4.LocalStructure.UnitaryNormalResidual.maximal_twoLocal_no_normal_unitary
    Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.maximalTwoLocalCover M hM B b

/-- Remove precisely the J₄ disjunct from the original terminal component.
All earlier-source hypotheses, the prime actor, normality, module commutator,
escape, whole-module and residual inclusions, and centralizer identity remain
unchanged. The Rudvalis exclusion belongs to its separate assembly owner. -/
theorem unitary_original_terminal_component_rudvalis
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context D.T D.L D.V)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L) :
    centralizer (D.Vplus : Set G) ≤ normalizer (D.L : Set G) ∧
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧ Nat.card A = p ∧
      A ≤ normalizer (D.L : Set G) ∧ A ≤ centralizer (D.V : Set G) ∧
      ⁅A,D.L⁆ ≤ D.L.pCoreIn 2 ∧
      ¬ normalizer (A : Set G) ≤ normalizer (D.L : Set G) ∧
      UniqueMaximalOvergroup (oddActorResidual D.L A) (normalizer (D.L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (D.L : Set G) ∧
        pCore 2 K = ⊥ ∧
        Nonempty (K ⧸ center K ≃* Rudvalis.Model) ∧
        D.V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual D.L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) := by
  obtain ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,hu,K,hK,hn,hm,houtK,hcore,
      hmodel,hV,hR,hcent⟩ :=
    unitary_original_terminal_component D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five
  have hodd : Odd (Nat.card A) := by
    rw [hcard]
    exact hp.odd_of_ne_two (by omega)
  rcases hmodel with hj | hru
  · obtain ⟨e⟩ := hj
    exact (unitary_original_terminal_janko_false s A hAN hcomm hodd hAV hu
      K hK hcore hV hR e).elim
  · exact ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,hu,K,hK,hn,hm,houtK,hcore,
      hru,hV,hR,hcent⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
