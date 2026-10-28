module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableCores
public import Theory.Representation.BinaryAlternatingFiveExtension.SmallKernel

/-!
# The original nonsolvable branch with two-core of order at most thirty-two

The two original cores have equal order and are incomparable. A core of
order at most thirty-two is abelian, so the two natural modules cannot
commute. The original V therefore has outer four-group image under the
same marked S₅ action on H. The small-kernel cover theorem constructs a
separate elementary subgroup inside O²(H), with image four under the
literal H → H/O₂(H). Thus n(H)=2 and original 5.2.3 supplies the model.

The universal application retains the multiple-overgroup guard after every
original S,I rechoice. It leaves only cores larger than thirty-two in a
catalogue counterexample. It does not discharge the unrestricted parameter
premise or the earlier Context/13.3.2/5.2.3 source inputs.
Source: Aschbacher--Smith 13.2.8(1), printed p.880, and C.5.6(7), p.159.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original cross-action supplies the extra input needed to lift an
actual residual four-group through a core of order at most thirty-two. -/
theorem original_nonsolvable_core_le_thirtyTwo_parameter
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (hsmall : Nat.card (pCore 2 H) ≤ 32) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hd := localActor_surjective_of_omega_movement d hH hZ
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hab := core_commutative_of_card_le_thirtyTwo e hjoin hsmall
  have hm : ¬ V ≤ centralizer (W : Set G) := fun hv =>
    original_pair_commuting_core_nonabelian d e hjoin hH hd q hq hk hv hab
  have hWH : W ≤ H := e.chosen.le_sylow.trans hH.1.1.2
  have hVH : V ≤ H := d.chosen.le_sylow.trans hH.1.1.2
  have hCW := (e.local_centralizers e.normalizes_L).1
  rw [hjoin] at hCW
  have hkW : q.ker = centralizer (W.subgroupOf H : Set H) := by
    rw [hk]
    apply map_injective H.subtype_injective
    change H.pCoreIn 2 = _
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWH]
    exact hCW.symm
  have hfour := (d.cross_action_outer_four e hVH hWH q hkW he hm).1
  let U := W.subgroupOf H
  have hHW : H ≤ normalizer (W : Set G) :=
    hjoin.ge.trans (sup_le e.chosen.normalizes e.flag.T_normalizes)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hHW
  have hWQ : W ≤ H.pCoreIn 2 := by
    rw [←hjoin]
    exact e.chosen.le_core
  have hUk : U ≤ q.ker := by
    rw [hk]
    intro x hx
    obtain ⟨y,hy,heq⟩ := hWQ hx
    exact (show y=x from Subtype.ext heq) ▸ hy
  have hUR : U ≤ pResidual 2 H := by
    intro x hx
    have hh := (e.chosen.le_componentCore.trans (pCoreIn_le 2 _)) hx
    obtain ⟨y,hy,heq⟩ := hh
    exact (show y=x from Subtype.ext heq) ▸ hy
  have hUc : Nat.card U = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv).trans e.module_card
  let i : Multiplicative (BinaryPermutation.core (Fin 5)) →* H :=
    e.flag.module.map.codRestrict H (fun v => hWH (e.flag.module.range_eq.le ⟨v,rfl⟩))
  have hi : Function.Injective i := fun x y h =>
    e.flag.module.injective (congrArg H.subtype h)
  have hir : i.range = U := by
    apply map_injective H.subtype_injective
    rw [←MonoidHom.range_comp,map_subgroupOf_eq_of_le hWH]
    exact e.flag.module.range_eq
  have hie (g : H) (v : Multiplicative (BinaryPermutation.core (Fin 5))) :
      i (BinaryPermutation.AlternatingFiveExtension.coreAction (q g) v) = g * i v * g⁻¹ := by
    apply Subtype.ext
    exact (he g v.toAdd).symm
  let := d.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨A,hA,hAR,hcard⟩ :=
    BinaryPermutation.AlternatingFiveExtension.exists_residual_four_of_small_kernel q
      (hk.symm ▸ pCore_isPGroup) hr U hUk hUR hUc (hk.symm ▸ hsmall)
      (V.subgroupOf H) hfour i hi hir hie
  let bq : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) :=
    QuotientGroup.liftEquiv (pCore 2 H) hq hk.symm
  have hbq : bq.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) = q := by
    apply MonoidHom.ext
    intro h
    rfl
  rw [←hbq,←map_map,card_map_of_injective (f := bq.toMonoidHom) bq.injective] at hcard
  let := hA
  obtain ⟨_,⟨a⟩⟩ := nonsolvable_residual_faithful_A5 d
    (normalizes_faithful_of_source1332 d h1332) hH hZ hs
  exact ⟨⟨A,hA,hAR,hcard⟩,
    ChapterE.ValuesEvenClassical.ResidualFive.parameter_two_of_residual_A5_lift
      (T.subtype hH.1.1.2) a A hAR hcard⟩

/-- Original 5.2.3 now applies without a generation or lift premise in the
entire branch with core order at most thirty-two. -/
theorem original_nonsolvable_core_le_thirtyTwo_model
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (hsmall : Nat.card (pCore 2 H) ≤ 32) : ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_core_le_thirtyTwo_parameter d hc hmany h1332 hcontexts
    hH hZ hs hsmall).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- Every original guarded rechoice in a catalogue counterexample now has
core order greater than thirty-two. -/
theorem universal_original_nonsolvable_core_gt_thirtyTwo
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G) (hno : ¬ ClassificationModels.IsQTKEModel G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) : 32 < Nat.card (pCore 2 H) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  by_contra! hsmall
  exact hno (original_nonsolvable_core_le_thirtyTwo_model d hc hmanyS h1332 hcontexts
    h523 hH hZ hs hsmall)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
