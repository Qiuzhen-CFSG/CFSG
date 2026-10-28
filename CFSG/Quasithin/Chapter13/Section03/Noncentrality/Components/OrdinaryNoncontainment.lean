module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryCore
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryComponents
public import Theory.GroupTheory.ElementaryEightCommutingTwoGroup
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryNormalizers
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.ReducedNormal.ComponentSeed

/-!
# The original seed in the containing-component branch of 13.3.14(g)

If the point residual lies in the selected component, its generation of the
original seed puts that seed in the component's intrinsic module. The
containment uses the actual omega-center in reduction (a), the selected
component's subnormality, and the original subtype into the point normalizer.
The local two-core centralizes this elementary seed of order eight because
it commutes with a nontrivial cubic action. The seed's normal closure inside
J is reduced by the quasisimple kernel theorem, so the seed belongs to the
literal W_K. Its original fixed line supplies nontrivial component-fixed
vectors. The remaining five-dimensional module sieve is separate; no
faithfulness of the raw local group is assumed.

Source: Aschbacher--Smith, Lemma 13.3.14(g), printed pp.892--893.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterA.Section04 Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section07.ModelExclusions
variable {G : Type*} [Group G] [Finite G]

/-- The full omega-center commutator, rather than only its nontriviality,
lies in the intrinsic module of a subnormal two-perfect subgroup. -/
theorem subnormal_omega_commutator_le_intrinsicModule
    (K : Subgroup G) (hK : K.IsSubnormal) (hp : IsPPerfect 2 K) :
    ⁅omegaOneCenterAmbient (pCore 2 G), K⁆ ≤ intrinsicSignalizerModule K := by
  have hn : K ≤ normalizer (pCore 2 G : Set G) := le_normalizer_of_normal
  have hc : ⁅K,pCore 2 G⁆ ≤ K.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal K (pCore 2 G)
      hK hp pCore_isPGroup hn).trans (map_mono (commutator_le_left _ _))
  simpa only [signalizerModule_eq_commutator_omegaCenter, commutator_comm K] using
    signalizerModule_le_intrinsicModule K (pCore 2 G) hp hn
      (pCoreIn_le_of_subnormal 2 hK) hc

/-- The literal seed containment in the contrary branch L₊ ≤ K of (g).
All the omega-center and generation premises come from the original setup. -/
theorem ordinary_seed_le_intrinsic_of_actor_le
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    U ≤ intrinsicSignalizerModule (K.map H.subtype) := by
  let := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hi := map_mono (f := H.subtype)
    (subnormal_omega_commutator_le_intrinsicModule K hK.subnormal hp)
  rw [map_commutator, ← intrinsicSignalizerModule_map_of_injective H.subtype
    H.subtype_injective, ← omegaOneCenterAmbient_map_injective H.subtype
    H.subtype_injective] at hi
  have hU : U ≤ omegaOneCenterAmbient (H.pCoreIn 2) :=
    (le_conjugateSpanBy U H).trans (ordinary_reduction_a d hc).2
  exact (seed_commutator_point_residual d).symm.le.trans
    ((commutator_mono hU hAK).trans hi)

/-- Consequently the actual seed is in the selected component's two-core,
with its original eight elements retained. -/
theorem ordinary_seed_le_component_core_of_actor_le
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    U ≤ (K.map H.subtype).pCoreIn 2 := by
  refine (ordinary_seed_le_intrinsic_of_actor_le d hc K hK hAK).trans ?_
  exact signalizerModule_le_right _ _
    ((K.map H.subtype).le_normalizer.trans
      (normalizer_le_normalizer_intrinsicCore (K.map H.subtype)))

/-- In the containing branch, the original local two-core centralizes the
actual seed. The point residual has cubic core quotient and generates the
seed; its nontrivial cubic action excludes any commuting two-group action. -/
theorem ordinary_local_core_centralizes_seed_of_actor_le
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    (Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T).pCoreIn 2 ≤
      centralizer (U : Set G) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAK.trans B.le_normalizer)) (h1332 B hf).1
  have hQB : J.pCoreIn 2 ≤ normalizer (B : Set G) := (pCoreIn_le 2 J).trans hJN
  have hBQ : B ≤ normalizer (J.pCoreIn 2 : Set G) :=
    hBJ.trans (J.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore J))
  have hcomm : ⁅B,J.pCoreIn 2⁆ ≤ B.pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hQB)
      (le_normalizer_iff_commutator_le_right.mp hBQ)).trans (inf_pCoreIn_le_of_le 2 hBJ)
  have hUI : U ≤ intrinsicSignalizerModule B :=
    ordinary_seed_le_intrinsic_of_actor_le d hc K hK hAK
  have hcommU : ⁅sourceOne L T P,J.pCoreIn 2⁆ ≤ centralizer (U : Set G) :=
    (commutator_mono hAK le_rfl).trans
      ((commutator_le_centralizer_intrinsicModule B _ hcomm).trans (centralizer_le hUI))
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    have ht := pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using ht
  let := Section07.NaturalAction.elementary d
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le d.seed_le
  have hm : ⁅U,sourceOne L T P⁆ ≠ ⊥ := by
    rw [seed_commutator_point_residual d]
    intro he
    have hu := d.seed_card
    rw [he,card_bot] at hu
    omega
  exact centralizes_elementary_eight_of_commuting_cubic_section U (sourceOne L T P)
    (J.pCoreIn 2) d.seed_card ordinary_point_residual_twoPerfect
    (ordinary_point_residual_quotient_card d e) (point_residual_normalizes_seed d)
    (hQT.trans d.seed_stable) (isPGroup_pCoreIn 2 J) hcommU hm

/-- The original seed lies in the very W_K used in the diagonal endgame.
The normal closure inside J is reduced by the quasisimple kernel theorem,
then generation by L₊ places the seed in [R₂(J),K]. -/
theorem ordinary_seed_le_movedModule_of_actor_le
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    U ≤ Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let K₀ := B.subgroupOf J
  let S := (T : Subgroup G).subgroupOf J
  let I := intrinsicSignalizerModule B
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hJH : J ≤ H := sup_le
    (sup_le (map_subtype_le _) (ordinary_point_residual_le_point d)) hTH
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAK.trans B.le_normalizer)) (h1332 B hf).1
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hK₀ : K₀.IsCComponent := by
    have hh : (B.subgroupOf H).IsCComponent := by
      change ((K.map H.subtype).comap H.subtype).IsCComponent
      rwa [comap_map_eq_self_of_injective H.subtype_injective]
    exact hh.subgroupOf_of_le hBJ hJH
  let := hqK
  let c : K ≃* K₀ := (K.equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hBJ).symm
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c))
  have hgen : K₀ ⊔ S = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBJ, map_subgroupOf_eq_of_le hTJ,
      ← MonoidHom.range_eq_map, range_subtype]
    change B ⊔ (T : Subgroup G) = (B ⊔ sourceOne L T P) ⊔ (T : Subgroup G)
    rw [sup_eq_left.mpr (show sourceOne L T P ≤ B from hAK)]
  have hIJ : I ≤ J := (intrinsicModule_le_self B).trans hBJ
  let : (I.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (hJN.trans (normalizer_le_normalizer_intrinsicModule B))
  let : IsElementaryAbelian 2 I := signalizerModule_elementaryAbelian B _
    (B.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore B))
  let : IsElementaryAbelian 2 (I.subgroupOf J) := IsElementaryAbelian.subgroupOf hIJ
  have hUI : U ≤ I := ordinary_seed_le_intrinsic_of_actor_le d hc K hK hAK
  have hUJ : U ≤ J := hUI.trans hIJ
  have hcore := ordinary_local_core_centralizes_seed_of_actor_le d e h1332 hc K hK hf hAK
  have hc₀ : pCore 2 J ≤ centralizer (U.subgroupOf J : Set J) := by
    intro q hq u hu
    apply Subtype.ext
    exact hcore (mem_map_of_mem J.subtype hq) u hu
  have hm : ⁅U.subgroupOf J,K₀⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (fun D : Subgroup J => D.map J.subtype) he
    rw [map_commutator, map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le hBJ, Subgroup.map_bot] at hh
    have hu : U = ⊥ := le_bot_iff.mp ((seed_commutator_point_residual d).symm.le.trans
      ((commutator_mono le_rfl hAK).trans hh.le))
    have hn := d.seed_card
    rw [hu,card_bot] at hn
    omega
  have hred := seed_le_reduced_of_component_supplement K₀ S (I.subgroupOf J)
    (U.subgroupOf J) hK₀ T.isPGroup'.comap_subtype hgen (comap_mono hUI) hc₀ hm
  have hUW : U ≤ Diagonal.reducedModule B (sourceOne L T P) T := by
    have hh := map_mono (f := J.subtype) hred
    rwa [map_subgroupOf_eq_of_le hUJ] at hh
  exact (seed_commutator_point_residual d).symm.le.trans (commutator_mono hUW hAK)

/-- The fixed line used by the five-dimensional row sieve belongs to the
literal W_K and is centralized by the selected component. -/
theorem ordinary_movedModule_contains_fixed_line_of_actor_le
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    P ≤ Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T ⊓
      centralizer (K.map H.subtype : Set G) := by
  refine le_inf ((d.line_le_plane.trans d.plane_le_seed).trans
    (ordinary_seed_le_movedModule_of_actor_le d e h1332 hc K hK hqK hf hAK)) ?_
  apply le_centralizer_iff.mp
  exact (map_subtype_le K).trans (d.first_normalizer ▸
    normalizer_le_centralizer_of_card_two P d.line_card)

/-- The nontrivial fixed subgroup needed by the source B.5 row sieve is
now obtained from the original flag, without a fixed-vector premise. -/
theorem ordinary_movedModule_fixed_ne_bot_of_actor_le
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : NaturalSetup T L V P E U M H)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T ⊓
      centralizer (K.map H.subtype : Set G) ≠ ⊥ := by
  intro he
  have hP := ordinary_movedModule_contains_fixed_line_of_actor_le d e h1332 hc K hK hqK hf hAK
  have hb : P = ⊥ := le_bot_iff.mp (hP.trans he.le)
  have hn := d.line_card
  rw [hb,card_bot] at hn
  omega

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
