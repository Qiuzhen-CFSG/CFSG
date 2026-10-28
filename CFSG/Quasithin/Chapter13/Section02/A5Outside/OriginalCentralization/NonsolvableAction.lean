module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Nonsolvable
public import CFSG.Quasithin.Chapter13.Section02.A5Local.FullAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockCoordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The original nonsolvable outside action is symmetric five

Apply the genuine A5 Context to the same embedded two-residual. Its flag
line lies in the original Sylow omega-center, so its conjugates place the
whole chosen natural module inside the original H-orbit of that center.
The original omega-action kernel is O2(H). Thompson movement therefore
passes to the chosen module, whose actual five-point action is onto S5.
Transport along O²(H)T = H keeps that action, its full kernel, the residual
image and the original natural-module coordinates together.

The residual Context is supplied by the existing earlier-source constructor
in SourceAssembly/NonsolvableAction. This identifies the surviving action;
it does not construct an elementary lift through its two-core or prove the
remaining generation-parameter bound.

Source: Aschbacher--Smith 13.2.8(1), printed p.880; 13.2.4(2b), p.879.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The actual chosen module is contained in the whole original omega orbit. -/
theorem module_le_original_omegaOrbit
    (e : Section05.A5Source.Context T K W W₁ W₂ W₃) (hKH : K ≤ H) :
    W ≤ omegaOrbit T H := by
  rw [← e.line_span_eq]
  apply conjugateSpanBy_le ?_ (hKH.trans (le_normalizer_conjugateSpanBy _ _))
  apply (le_conjugateSpanBy _ _).trans' ?_
  rw [←e.flag.flag.line_eq]
  exact zpowers_le.mpr e.flag.flag.z_central

private theorem residual_sylow_join (hTH : (T : Subgroup G) ≤ H) :
    (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
  have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
    ←MonoidHom.range_eq_map,range_subtype] using hh

private theorem nonsolvable_thompson_not_le_core
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ H.pCoreIn 2 := by
  have hker := nonsolvable_omega_centralizer_eq_twoCore d hn hH hZ hs
  have hU : omegaOrbit T H ≤ H := conjugateSpanBy_le
    (fun z hz => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) H.le_normalizer
  intro hJ
  apply thompson_moves_omegaOrbit d.hypothesis.qtke T hH hB hZ
  intro j hj u hu
  obtain ⟨a,ha,he⟩ := hJ hj
  have hc : a ∈ centralizer ((omegaOrbit T H).subgroupOf H : Set H) := hker.symm ▸ ha
  rw [←he]
  exact congrArg H.subtype (hc ⟨u,hU hu⟩ hu)

private theorem residual_context_thompson_moves
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (e : Section05.A5Source.Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
  intro hJ
  apply nonsolvable_thompson_not_le_core d hn hH hB hZ hs
  have hcore := (e.local_centralizers e.normalizes_L).1
  rw [residual_sylow_join hH.1.1.2] at hcore
  rw [←hcore]
  exact le_inf ((sSup_le fun _ hA => hA.1).trans hH.1.1.2) hJ

private theorem residual_context_action
    (e : Section05.A5Source.Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
    (hTH : (T : Subgroup G) ≤ H)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    ∃ q : H →* Equiv.Perm (Fin 5), Function.Surjective q ∧ q.ker = pCore 2 H ∧
      (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
      (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
        h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
          e.flag.module.map (Multiplicative.ofAdd
            (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) := by
  let a := MulEquiv.subgroupCongr (residual_sylow_join hTH)
  let q := e.localActor.comp a.symm.toMonoidHom
  have hq : Function.Surjective q := (e.localActor_surjective_of_thompson_moves hJ).comp a.symm.surjective
  refine ⟨q,hq,?_,?_,?_⟩
  · change e.localActor.ker.comap a.symm.toMonoidHom = pCore 2 H
    rw [e.localActor_kernel_eq_core e.normalizes_L]
    have hm := pCore_map_iso 2 a.symm
    rw [←hm, comap_map_eq_self_of_injective a.symm.injective]
  · rw [map_pResidual_of_surjective 2 q hq,Equiv.Perm.twoResidual_eq_alternating]
  · intro h w
    exact e.flag.normalizer_equivariant
      ⟨h.val,(sup_le e.chosen.normalizes e.flag.T_normalizes) (a.symm h).property⟩ w

/-- The same H acts as S5, with its literal two-core and omega-centralizer
kernels equal. The natural submodule and its marked action are retained. -/
theorem nonsolvable_residual_action
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (e : Section05.A5Source.Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃) :
    W ≤ omegaOrbit T H ∧
      ∃ q : H →* Equiv.Perm (Fin 5), Function.Surjective q ∧ q.ker = pCore 2 H ∧
        q.ker = centralizer ((omegaOrbit T H).subgroupOf H : Set H) ∧
        (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
        (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
          h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
            e.flag.module.map (Multiplicative.ofAdd
              (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) := by
  obtain ⟨q,hq,hk,hr,he⟩ := residual_context_action e hH.1.1.2
    (residual_context_thompson_moves d hn hH hB hZ hs e)
  exact ⟨module_le_original_omegaOrbit e (map_subtype_le _), q,hq,hk,
    hk.trans (nonsolvable_omega_centralizer_eq_twoCore d hn hH hZ hs).symm,hr,he⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
