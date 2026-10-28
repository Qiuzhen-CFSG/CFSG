module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.CriticalSetup
/-!
# The doubled critical pair in the original Sylow subgroup

If W₀(T,V_M) lies in O₂(H), the literal F.7.6 setup has even track.
F.7.11 produces a noncommuting conjugate in N_M(C_T(V_M)), with commutator
in the intersection. Sylow conjugacy inside that local subgroup puts the
conjugate into the original T while preserving V_M.

Consequently the local assertion that mutually normalizing doubled conjugates
commute implies weak-closure escape. Its parameter consumer applies E.3.20
to the same D, S and H. The local commuting assertion and numerical bounds
remain to be proved; this module does not assert 11.3.6.

Source: Aschbacher--Smith, 11.3.6, printed p.772, using F.7.9(4)
and F.7.11(2), printed pp.313--314.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterF.Section07
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (exists_smul_base)
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
private theorem doubled_pair_in_local (d : Coordinates D S) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hW : ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    ∃ g : G, (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ criticalLocal T L V ∧
      ⁅fullModule L V, (fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅fullModule L V, (fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤ fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom := by
  let J := criticalLocal T L V ⊔ H
  let F := criticalFamily (T := T) (L := L) (V := V) H
  let E := criticalSetup d H hTH hout
  have hne := criticalSeed_ne_bot d H hTH hout
  have heven : Even (E.track hne) := by
    apply CriticalPairs.Completion.even_track_of_ambient_weakClosure_core F E hne
      J.subtype J.subtype_injective
    rw [criticalSeed_map, criticalSylow_map,
      show (F true).map J.subtype = H from map_subgroupOf_eq_of_le le_sup_right]
    exact hW
  obtain ⟨v, hd, hcrit⟩ := (E.critical_witness hne).1
  have hv := CriticalPairs.even_endpoint_type F E hne hd heven
  have hp := CriticalPairs.SourceAction.even_critical_pair E hne hd heven hcrit
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  rw [CriticalPairs.vertexModule_first F E.seed hv, ← hg,
    CriticalPairs.firstModule_translate_base F E.seed E.seed_normalized] at hp
  have hc : (E.seed.map (MulAut.conj g).toMonoidHom).map J.subtype =
      (fullModule L V).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [map_map]
    change (E.seed.map ((MulAut.conj (g : G)).toMonoidHom.comp J.subtype)) = _
    rw [← map_map, criticalSeed_map]
  refine ⟨g, ?_, ?_, ?_⟩
  · have hm := map_mono (f := J.subtype) hp.2.2.1
    rwa [hc, show (F false).map J.subtype = criticalLocal T L V from
      map_subgroupOf_eq_of_le le_sup_left] at hm
  · intro hz
    apply hp.1
    apply (map_eq_bot_iff_of_injective _ J.subtype_injective).mp
    rw [map_commutator, criticalSeed_map, hc]
    exact hz
  · have hm := map_mono (f := J.subtype) hp.2.1
    rwa [map_commutator, Subgroup.map_inf _ _ _ J.subtype_injective, criticalSeed_map, hc] at hm

/-- F.7.11 supplies the required conjugate in the original T, without a pair premise. -/
theorem exists_doubled_critical_pair (d : Coordinates D S) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hW : ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    ∃ g : G, (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T ∧
      ⁅fullModule L V, (fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅fullModule L V, (fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤ fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hA, hne, hcomm⟩ := doubled_pair_in_local d H hTH hout hW
  let J := criticalLocal T L V
  let A := (fullModule L V).map (MulAut.conj g).toMonoidHom
  let := fullModule_elementary d
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hAp : IsPGroup 2 (A.subgroupOf J) := (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  obtain ⟨P, hP⟩ := hAp.exists_le_sylow
  let Q : Sylow 2 J := T.subtype (le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S)))
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq J P Q
  have hlocal : (A.subgroupOf J).map (MulAut.conj t).toMonoidHom ≤
      (Q : Subgroup J) := by
    rw [← ht]
    exact map_mono hP
  have hcomp : J.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t : G)).toMonoidHom.comp J.subtype := rfl
  have hamb := map_mono (f := J.subtype) hlocal
  rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hA,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S)))] at hamb
  have hV : (fullModule L V).map (MulAut.conj (t : G)).toMonoidHom = fullModule L V :=
    mem_normalizer_iff_map_conj_eq.mp ((criticalLocal_normalizes (T := T)) t.property)
  have hAeq : A.map (MulAut.conj (t : G)).toMonoidHom =
      (fullModule L V).map (MulAut.conj ((t : G) * g)).toMonoidHom :=
    ChapterE.offender_map_conj_map (fullModule L V) g (t : G)
  refine ⟨(t : G) * g, hAeq ▸ hamb, ?_, ?_⟩
  · intro hz
    apply hne
    apply (map_eq_bot_iff_of_injective _
      (f := (MulAut.conj (t : G)).toMonoidHom) (MulAut.conj (t : G)).injective).mp
    rw [map_commutator, hV, hAeq]
    exact hz
  · have hm := map_mono (f := (MulAut.conj (t : G)).toMonoidHom) hcomm
    change (⁅fullModule L V, A⁆).map _ ≤ (fullModule L V ⊓ A).map _ at hm
    rwa [map_commutator, Subgroup.map_inf _ _ _ (MulAut.conj (t : G)).injective, hV, hAeq] at hm

/-- F.7.11 reduces doubled weak-closure escape to the reciprocal local-module
calculation. The latter must prove that mutually normalizing conjugates commute. -/
theorem weak_escape_of_pair_centralization
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}
    (h : Hypothesis1131At D S U₁ H) (d : Coordinates D S)
    (hpair : ∀ g : G, (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
        fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom →
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2 := by
  intro hw
  obtain ⟨g,hg,hne,hcomm⟩ :=
    exists_doubled_critical_pair d H h.outside.1.1.2 h.outside.1.2 hw
  exact hne (hpair g hg hcomm)

/-- Literal parameter application: after the reciprocal pair calculation,
E.3.20 yields k=2n on the same chosen input and outside H. The s-value and
the preceding generation bound remain separate source obligations. -/
theorem parameter_eq_twice_of_pair_centralization
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}
    (h : Hypothesis1131At D S U₁ H) (d : Coordinates D S)
    (hpair : ∀ g : G, (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T →
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
        fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom →
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) =
      (2 * S.field.degree : ℕ∞))
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree) :
    ChapterE.generationParameter H = 2 * S.field.degree :=
  parameter_eq_twice h d (weak_escape_of_pair_centralization h d hpair) hs hu

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
