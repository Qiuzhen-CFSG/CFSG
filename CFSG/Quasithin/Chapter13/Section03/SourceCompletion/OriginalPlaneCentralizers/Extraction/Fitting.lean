module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Hyperplanes
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Setup
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment
public import Theory.GroupTheory.Fitting.TwoCorePreimage

/-!
# Solvable overgroups in the original plane-centralizer argument

If Q=O₂(LT) is Sylow in a solvable subgroup H, E-generation and s(G,V)>1
force H into M=N_G(L). In each E-generator, the intersection of a conjugate
of V with its two-core has corank at most one and centralizes V, so the
whole conjugate centralizes V. The weak-closure normalizer is controlled
by the source uniqueness hypothesis.

Applying this argument to O₂,F(C_G(A))Q, with the Sylow subgroup supplied by
C.2.6, puts the actual Fitting preimage of the plane centralizer inside M.
This discharges the solvable-preimage premise in local component extraction;
extracting the escaping component remains an obligation of the original
plane-centralizer assembly.

Source: Aschbacher--Smith 13.3.12, printed p.889, using E.3.19 and C.2.6.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

private theorem normalClosure_centralizes_of_core_centralizes {V S : Subgroup G} [IsElementaryAbelian 2 V]
    (hSC : S ≤ centralizer (V : Set G))
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (f : K →* G) (hf : Function.Injective f) (g : G)
    (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hcore : (pCore 2 K).map f ≤ S) {i : ℕ}
    (hrank : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ i)
    (hs : (i : ℕ∞) < globalS V) :
    (normalClosure (A : Set K)).map f ≤ centralizer (V : Set G) := by
  have hi := SourceContainment.core_corank_le A hrank
  have hconj (k : K) :
      (A.map (f.comp (MulAut.conj k).toMonoidHom)) ≤ centralizer (V : Set G) := by
    let f' := f.comp (MulAut.conj k).toMonoidHom
    have hinj : Function.Injective f' := hf.comp (MulAut.conj k).injective
    have he : A.map f' = V.map (MulAut.conj (f k * g)).toMonoidHom := by
      have hcomp : f' = (MulAut.conj (f k)).toMonoidHom.comp f := by ext x; simp [f']
      rw [hcomp, ← map_map, hAg, map_map]
      congr 1
      ext x
      simp [mul_assoc]
    have hBC : ((A ⊓ pCore 2 K).map f') ≤ S := by
      apply le_trans _ hcore
      rintro x ⟨a, ha, rfl⟩
      exact mem_map_of_mem f ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 k)
    have hb : subgroupCorank (V.map (MulAut.conj (f k * g)).toMonoidHom)
        ((A ⊓ pCore 2 K).map f') ≤ i := by
      rw [← he, subgroupCorank, relIndex_map_map_of_injective _ _ hinj]
      exact hi
    have hBV := he ▸ map_mono (f := f') (show A ⊓ pCore 2 K ≤ A from inf_le_left)
    let A' := V.map (MulAut.conj (f k * g)).toMonoidHom
    let B' := (A ⊓ pCore 2 K).map f'
    let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
    have hc := centralizer_inf_eq_of_corank_lt_globalS (V := A') (B := B') (E := V)
      hBV (by
        change (subgroupCorank A' B' : ℕ∞) < globalS (V.map (MulAut.conj (f k * g)).toMonoidHom)
        rw [globalS_map_equiv]
        exact lt_of_le_of_lt (by exact_mod_cast hb) hs)
      (IsElementaryAbelian.isPGroup 2 V)
    have hVC : V ≤ centralizer (B' : Set G) := le_centralizer_iff.mp (hBC.trans hSC)
    have hVA : V ≤ centralizer (A' : Set G) := by
      intro v hv
      exact (hc ▸ (show v ∈ V ⊓ centralizer (B' : Set G) from ⟨hv,hVC hv⟩)).2
    rw [he]
    exact le_centralizer_iff.mp hVA
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (A : Set K)) ≤ _
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)


theorem Context.solvable_overgroup_le (s : Context T L V) (d : MarkedPlane V)
    (H : Subgroup G) [Group.IsSolvable H] (S : Sylow 2 H)
    (hSQ : (S : Subgroup H).map H.subtype = (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    H ≤ normalizer (L : Set G) := by
  let M := normalizer (L : Set G)
  let i : ℕ := 1
  have hgen := isEGenerated_one_of_solvable S
  have hs := s.one_lt_globalS d
  have he := s.earlier_geometry.1
  have hCV : H ⊓ centralizer (V : Set G) ≤ M := inf_le_right.trans he.centralizer_le
  let Ω := conjugateCorankFamily V 0
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro A ⟨g, hAV, hi⟩
      let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
      exact IsElementaryAbelian.of_injective (Subgroup.inclusion hAV) (Subgroup.inclusion_injective _)
    · intro g A hA
      exact conjugateCorankFamily_invariant V 0 A hA g
  let ΩH := ChiefOrbit.restrictedFamily H Ω
  have hΩH : IsElementaryFamily ΩH := ChiefOrbit.restrictedFamily_elementary H hΩ
  let Sg := (S : Subgroup H).map H.subtype
  have hSg : IsPGroup 2 Sg := S.2.map H.subtype
  have hVSg : V ≤ Sg := by simpa only [Sg,hSQ] using s.chosen.le_core
  have hSgC : Sg ≤ centralizer (V : Set G) := by
    simpa only [Sg,hSQ] using s.chosen.core_centralizes
  have hNM : normalizer (indexedWeakClosure V Sg 0 : Set G) ≤ M := by
    apply normalizer_le_of_unique_maximalTwoLocal
      (J := normalizer (Sg : Set G))
      (fun N hN hSN => he.unique N hN (by
        apply inf_le_right.trans
        simpa only [Section06.sylowCentralizer, he, s.earlier_geometry.2.1, ← hSQ] using hSN))
      (hSg.to_le (indexedWeakClosure_le V Sg 0))
      (fun hb => s.chosen.ne_bot (le_bot_iff.mp (hb ▸ self_le_weakClosure_zero hVSg)))
    exact normalizer_le_weakClosure_normalizer V Sg 0
  have hSM : Sg ≤ M := (Sg.le_normalizer.trans (normalizer_le_weakClosure_normalizer V Sg 0)).trans hNM
  have hSMH : (S : Subgroup H) ≤ M.subgroupOf H := map_le_iff_le_comap.mp hSM
  have hWmap : (weakClosure (S : Subgroup H) ΩH).map H.subtype = indexedWeakClosure V Sg 0 := by
    have he := ChiefOrbit.map_weakClosure_restrictedFamily Sg H (map_subtype_le _) Ω
    have hsub : Sg.subgroupOf H = (S : Subgroup H) := by
      change ((S : Subgroup H).map H.subtype).comap H.subtype = (S : Subgroup H)
      rw [comap_map_eq_self_of_injective H.subtype_injective]
    rwa [hsub] at he
  have hN : normalizer (weakClosure (S : Subgroup H) ΩH : Set H) ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    apply le_trans (Subgroup.le_normalizer_map H.subtype)
    rw [hWmap]
    exact hNM
  have hE : eFamilySubgroup i (S : Subgroup H) ΩH ≤ M.subgroupOf H := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hA := A.property.1
    have hAS : A.val.map H.subtype ≤ Sg := map_mono A.property.2
    obtain ⟨g, hAg, _⟩ := (mem_gamma_zero_iff V Sg (A.val.map H.subtype)).mp ⟨hA, hAS⟩
    let AK := A.val.subgroupOf K
    let _ : IsElementaryAbelian 2 A.val := hK.1.1
    let _ : IsElementaryAbelian 2 AK := IsElementaryAbelian.subgroupOf hK.1.2.2.1
    let f := H.subtype.comp K.subtype
    have hf : Function.Injective f := H.subtype_injective.comp K.subtype_injective
    have heA : AK.map f = V.map (MulAut.conj g).toMonoidHom := by
      rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hAg
    have hcore : (pCore 2 K).map f ≤ Sg := by
      obtain ⟨U, hU⟩ := hK.1.2.2.2.2.1
      have hcu := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal U)
      rw [hU, subgroupOf_map_subtype] at hcu
      change (pCore 2 K).map (H.subtype.comp K.subtype) ≤ Sg
      rw [← map_map]
      exact map_mono (hcu.trans inf_le_left)
    have hNC := normalClosure_centralizes_of_core_centralizes hSgC AK f hf g heA hcore
      (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK) hs
    have hRC : (pResidual 2 K).map f ≤ centralizer (V : Set G) :=
      (map_mono hK.1.residual_le_normalClosure).trans hNC
    apply hK.1.le_of_residual_le hSMH
    rintro x ⟨k, hk, rfl⟩
    exact hCV ⟨k.val.property, hRC (mem_map_of_mem f hk)⟩
  have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    rw [← hgen ΩH hΩH]
    exact sup_le hE hN
  intro x hx
  exact htop (show (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)

/-- The source solvable Fitting preimage of the actual plane centralizer is in M. -/
theorem Context.plane_twoFittingCore_le (s : Context T L V) (d : MarkedPlane V) :
    (twoFittingCore (centralizer (d.A : Set G))).map (centralizer (d.A : Set G)).subtype ≤
      centralizer (d.A : Set G) ⊓ normalizer (L : Set G) := by
  let H := centralizer (d.A : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := Q.subgroupOf H
  let D := twoFittingCore H ⊔ R
  let Dg := D.map H.subtype
  have hQH : Q ≤ H := (s.plane_local_control d).1
  have hr : IsPRadical 2 R := s.core_plane_radical d
  let : Group.IsSolvable D := twoFittingCore_sup_solvable R hr.isPGroup
  let e : D ≃* Dg := equivMapOfInjective D H.subtype H.subtype_injective
  let : Group.IsSolvable Dg := Group.isSolvable_of_isSolvable_injective
    (f := e.symm.toMonoidHom) e.symm.injective
  have hSylow : ∃ S : Sylow 2 D, (S : Subgroup D).map D.subtype = R :=
    twoFittingCore_sup_sylow R hr
  obtain ⟨S,hS⟩ := hSylow
  let Sg := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSg : (Sg : Subgroup Dg).map Dg.subtype = Q := by
    change ((S : Subgroup D).map e.toMonoidHom).map Dg.subtype = Q
    have hecomp : Dg.subtype.comp e.toMonoidHom = H.subtype.comp D.subtype := by
      ext x; rfl
    rw [map_map,hecomp,← map_map,hS,map_subgroupOf_eq_of_le hQH]
  have hDM := s.solvable_overgroup_le d Dg Sg hSg
  exact le_inf (map_subtype_le _) ((map_mono (show twoFittingCore H ≤ D from le_sup_left)).trans hDM)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
