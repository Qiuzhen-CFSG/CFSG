module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup
public import CFSG.Quasithin.Chapter11.Section01To02.NormalizerSteps

/-!
# Constructing the critical pair in the original Sylow subgroup

The zero-corank source closure equals the actual E.3 indexed closure. Its
containment in O₂(H) makes the F.7 track even. F.7.11 gives a noncommuting
conjugate inside LT with commutator in the intersection. Sylow conjugacy
inside LT puts that conjugate in the original T while preserving V.

The final conditional application has only the 11.2.4 non-normalization
conclusion left as a premise. All graph, parity and pair-existence premises
are discharged here. The separate module analysis proving 11.2.4 must be
supplied before this is a proof of 11.2.5.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.4--5, printed pp.769--770, and F.7.9(4), F.7.11(2), pp.313--314.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterF.Section07
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (exists_smul_base)
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

omit [Finite G] in
/-- The two literal definitions of W₀ agree, including the ambient conjugators. -/
theorem source_zero_eq_indexed (P U : Subgroup G) :
    Source.weakClosureZero P U = ChapterE.indexedWeakClosure U P 0 := by
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  unfold Source.weakClosureZero
  apply congrArg sSup
  ext A
  exact (ChapterE.mem_gamma_zero_iff U P A).symm

include D S

private theorem pair_in_join (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hW : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ L ⊔ (T : Subgroup G) ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  let J := L ⊔ (T : Subgroup G) ⊔ H
  let F := family (T := T) (L := L) H
  let E := f7Setup D S H hTH hout
  have hne := f7V_ne_bot D S H hTH hout
  have heven : Even (E.track hne) := by
    apply CriticalPairs.Completion.even_track_of_ambient_weakClosure_core F E hne
      J.subtype J.subtype_injective
    rw [f7Seed_map, f7Sylow_map,
      show (F true).map J.subtype = H from map_subgroupOf_eq_of_le le_sup_right]
    rwa [← source_zero_eq_indexed]
  obtain ⟨v, hd, hcrit⟩ := (E.critical_witness hne).1
  have hv := CriticalPairs.even_endpoint_type F E hne hd heven
  have hp := CriticalPairs.SourceAction.even_critical_pair E hne hd heven hcrit
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  rw [CriticalPairs.vertexModule_first F E.seed hv, ← hg,
    CriticalPairs.firstModule_translate_base F E.seed E.seed_normalized] at hp
  have hc : (E.seed.map (MulAut.conj g).toMonoidHom).map J.subtype =
      V.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [map_map]
    change (E.seed.map ((MulAut.conj (g : G)).toMonoidHom.comp J.subtype)) = _
    rw [← map_map, f7Seed_map]
  refine ⟨g, ?_, ?_, ?_⟩
  · have hm := map_mono (f := J.subtype) hp.2.2.1
    rwa [hc, show (F false).map J.subtype = L ⊔ (T : Subgroup G) from
      map_subgroupOf_eq_of_le le_sup_left] at hm
  · intro hz
    apply hp.1
    apply (map_eq_bot_iff_of_injective _ J.subtype_injective).mp
    rw [map_commutator, f7Seed_map, hc]
    exact hz
  · have hm := map_mono (f := J.subtype) hp.2.1
    rwa [map_commutator, Subgroup.map_inf _ _ _ J.subtype_injective, f7Seed_map, hc] at hm

/-- F.7.11 supplies the required conjugate in the original T, without a pair premise. -/
theorem exists_critical_pair (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (hW : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hA, hne, hcomm⟩ := pair_in_join D S H hTH hout hW
  let J := L ⊔ (T : Subgroup G)
  let A := V.map (MulAut.conj g).toMonoidHom
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hAp : IsPGroup 2 (A.subgroupOf J) := (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  obtain ⟨P, hP⟩ := hAp.exists_le_sylow
  let Q : Sylow 2 J := T.subtype le_sup_right
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq J P Q
  have hlocal : (A.subgroupOf J).map (MulAut.conj t).toMonoidHom ≤
      (Q : Subgroup J) := by
    rw [← ht]
    exact map_mono hP
  have hcomp : J.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t : G)).toMonoidHom.comp J.subtype := rfl
  have hamb := map_mono (f := J.subtype) hlocal
  rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hA,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] at hamb
  have hV : V.map (MulAut.conj (t : G)).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp ((sup_le D.normalizes S.sylow_normalizes) t.property)
  have hAeq : A.map (MulAut.conj (t : G)).toMonoidHom =
      V.map (MulAut.conj ((t : G) * g)).toMonoidHom :=
    ChapterE.offender_map_conj_map V g (t : G)
  refine ⟨(t : G) * g, hAeq ▸ hamb, ?_, ?_⟩
  · intro hz
    apply hne
    apply (map_eq_bot_iff_of_injective _
      (f := (MulAut.conj (t : G)).toMonoidHom) (MulAut.conj (t : G)).injective).mp
    rw [map_commutator, hV, hAeq]
    exact hz
  · have hm := map_mono (f := (MulAut.conj (t : G)).toMonoidHom) hcomm
    change (⁅V, A⁆).map _ ≤ (V ⊓ A).map _ at hm
    rwa [map_commutator, Subgroup.map_inf _ _ _ (MulAut.conj (t : G)).injective, hV, hAeq] at hm

/-- The constructed pair also supplies the noncentrality premise of 11.2.4. -/
theorem noncentral_zero_of_le_outside_core (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hout : ¬ H ≤ normalizer (L : Set G))
    (hW : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2) :
    ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥ := by
  obtain ⟨g, hg, hne, _⟩ := exists_critical_pair D S H hTH hout hW
  intro hz
  apply hne
  exact bot_unique ((commutator_mono le_rfl (Source.conjugate_le_weakClosureZero hg)).trans hz.le)

/-- Conditional 11.2.5: only the source 11.2.4(2) module argument remains.
The parent must supply it under the full flag and extra SL3 centralizer hypotheses. -/
theorem obstruction_of_nonnormalization (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hout : ¬ H ≤ normalizer (L : Set G))
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hSL3 : Nonempty (ActionEquiv D.centralQuotientAction
      (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))
    (hrestriction : (Nonempty (ActionEquiv D.centralQuotientAction
      (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)) →
      IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V) →
      ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥ →
      ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
          ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H := by
  by_cases hW : Source.weakClosureZero (T : Subgroup G) V ≤ H.pCoreIn 2
  · exact Or.inr (Source.nonabelian_span_of_critical_pair
      (fun ha => hrestriction hSL3 ha (noncentral_zero_of_le_outside_core D S H hTH hout hW))
      (exists_critical_pair D S H hTH hout hW))
  · exact Or.inl hW

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
