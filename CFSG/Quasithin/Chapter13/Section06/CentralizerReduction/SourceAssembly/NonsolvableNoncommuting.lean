module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableCores
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CrossKernel
public import Theory.Representation.BinaryAlternatingFiveExtension.NormalElementary

/-!
# Excluding the original noncommuting nonsolvable pair without a core bound

The cross-centralizer calculation puts the original kernel commutators
with V inside the residual's natural module W. The Sylow-normal elementary
subgroup V then detects that W is the whole residual kernel. Splitting
constructs a different elementary subgroup inside the original O²(H),
with image four under the literal H → H/O₂(H). Thus n(H)=2, and original
5.2.3 applies. An abelian outside core forces noncommuting modules by the
proved incomparability of the two cores, so all abelian cores are excluded.

After every guarded S,I rechoice, a catalogue counterexample consequently
has commuting natural modules and a nonabelian outside core. The full
omega-action kernel, common actor marking and multiple-overgroup guard
are retained. The commuting nonabelian case, the earlier Context/13.3.2/
5.2.3 sources, and unconditional 13.2.7/13.6.7 remain with their owners.
Source: Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Subgroup Theory.GroupTheory Stellmacher
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
theorem original_nonsolvable_noncommuting_parameter
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    {W W₁ W₂ W₃ : Subgroup G}
    (e : Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker=pCore 2 H) (hr : (pResidual 2 H).map q=alternatingGroup (Fin 5))
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hm : ¬ V≤centralizer (W:Set G)) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
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
  have hfour := d.cross_action_outer_four e hVH hWH q hkW he hm
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
  have hnormal : ((T.subtype hH.1.1.2) : Subgroup H) ≤
      normalizer (V.subgroupOf H : Set H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (d.flag.T_normalizes ht) v.val
  have hcross := d.cross_centralizer_le_module e hVH hWH q hkW he hm
  have hQT : H.pCoreIn 2≤(T:Subgroup G) :=
    map_le_iff_le_comap.mpr (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
  have hQN : H≤normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQV : ⁅H.pCoreIn 2,V⁆≤V := le_normalizer_iff_commutator_le_right.mp
    (hQT.trans d.flag.T_normalizes)
  have hQQ : ⁅H.pCoreIn 2,V⁆≤H.pCoreIn 2 := le_normalizer_iff_commutator_le_left.mp
    (hVH.trans hQN)
  have hQW : H.pCoreIn 2≤centralizer (W:Set G) := hCW.ge.trans inf_le_right
  have hcommG : ⁅H.pCoreIn 2,V⁆≤W := (le_inf hQV (hQQ.trans hQW)).trans hcross
  have hcomm : ⁅q.ker,V.subgroupOf H⁆≤U := by
    intro x hx
    have hh := mem_map_of_mem H.subtype hx
    rw [map_commutator,hk,map_subgroupOf_eq_of_le hVH] at hh
    exact hcommG hh
  obtain ⟨A,hA,hAR,hcard⟩ :=
    BinaryPermutation.AlternatingFiveExtension.exists_residual_four_of_normal_elementary
      (T.subtype hH.1.1.2) q hq hk hr U (V.subgroupOf H) hUk hUR
      (fun _ hx => d.chosen.le_sylow hx) hnormal hfour.1 hfour.2 hcomm i hi hir hie
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


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly


namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Subgroup Theory.GroupTheory Stellmacher
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 5.2.3 applies to every abelian outside core, with no order bound. -/
theorem original_nonsolvable_abelian_core_model
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
    (hs : ¬ Group.IsSolvable H) (hab : IsMulCommutative (pCore 2 H)) :
    ClassificationModels.IsQTKEModel G := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,_,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hm : ¬ V≤centralizer (W:Set G) := fun hv =>
    original_pair_commuting_core_nonabelian d e hjoin hH
      (localActor_surjective_of_omega_movement d hH hZ) q hq hk hv hab
  have hn := (original_nonsolvable_noncommuting_parameter d h1332 hH hZ hs e q hq hk hr he hm).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- Every remaining original outside pair has commuting natural modules
and a nonabelian core. The same marked quotient and full omega kernel remain. -/
theorem universal_original_nonsolvable_commuting_pair
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
    (hs : ¬ Group.IsSolvable H) :
    ¬ IsMulCommutative (pCore 2 H) ∧
    ∃ (V V₁ V₂ V₃ : Subgroup G) (_ : Context S I V V₁ V₂ V₃)
      (W W₁ W₂ W₃ : Subgroup G)
      (e : Context S ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (q : H →* Equiv.Perm (Fin 5)),
      W ≤ omegaOrbit S H ∧ Function.Surjective q ∧ q.ker = pCore 2 H ∧
        q.ker = centralizer ((omegaOrbit S H).subgroupOf H : Set H) ∧
        (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
        (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
          h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
            e.flag.module.map (Multiplicative.ofAdd
              (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) ∧
        V ≤ centralizer (W : Set G) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  have hab : ¬ IsMulCommutative (pCore 2 H) := fun h => hno
    (original_nonsolvable_abelian_core_model d hc hmanyS h1332 hcontexts h523 hH hZ hs h)
  obtain ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmanyS h1332 hcontexts hH hZ hs
  refine ⟨hab,V,V₁,V₂,V₃,d,W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he,?_⟩
  by_contra hm
  have hn := (original_nonsolvable_noncommuting_parameter d h1332 hH hZ hs e q hq hk hr he hm).2
  exact hno (main_model_of_source523_omega_movement d h523 hH hZ (by omega))
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
