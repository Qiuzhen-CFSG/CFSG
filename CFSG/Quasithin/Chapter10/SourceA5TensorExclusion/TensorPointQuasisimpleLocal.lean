module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointMembership
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointFFSource
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The original tensor residual modulo a containing center

The moved subgroup [V,L₀] lies in L₀ and is a normal two-subgroup there.
If its image modulo the containing center vanished, commutator idempotence
would make the entire action trivial, contradicting the fixed field line of
order four in V of order 256. Thus the actual image of L₀ has nontrivial
two-core. Restricting the original Sylow centralizer and taking the central
quotient gives a Sylow-normalized local A₅ section with that same image.
Held's completed two-local catalogue excludes this exact configuration.

Source: Aschbacher--Smith 9.4.1, printed p.735, and A.3.12, pp.47--48.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual residual image retains a nontrivial two-core modulo every
containing center. -/
theorem tensorPoint_containing_quotient_residual_core_ne_bot (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    pCore 2 (((m.tensorPointResidual v).subgroupOf I).map
      (QuotientGroup.mk' (center I))) ≠ ⊥ := by
  let B := (m.tensorPointResidual v).subgroupOf I
  let q := QuotientGroup.mk' (center I)
  let W := ⁅D.fullModule,m.tensorPointResidual v⁆
  have hWL : W ≤ m.tensorPointResidual v := le_normalizer_iff_commutator_le_right.mp
    (m.tensorPointResidual_fullModule_normalized v)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)
  have hWI : W ≤ I := hWL.trans hLI
  have hpW : IsPGroup 2 (W.subgroupOf I) :=
    (T.isPGroup'.to_le (hWV.trans m.fullModule_le_sylow)).comap_subtype
  have hnW : B ≤ normalizer (W.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hWI]
    exact comap_mono (normalizer_commutator_ge_right D.fullModule (m.tensorPointResidual v))
  have hBW : B.map q ≤ normalizer ((W.subgroupOf I).map q : Set (I ⧸ center I)) :=
    (map_mono hnW).trans ((W.subgroupOf I).le_normalizer_map q)
  have hcore : (W.subgroupOf I).map q ≤ (B.map q).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hpW.map q) (map_mono (comap_mono hWL)) hBW
  intro hbot
  change pCore 2 (B.map q) = ⊥ at hbot
  have hwbot : (W.subgroupOf I).map q = ⊥ := by
    apply le_antisymm _ bot_le
    simpa only [Subgroup.pCoreIn,hbot,Subgroup.map_bot] using hcore
  have hc : W ≤ centralizer (m.tensorPointResidual v : Set G) := by
    intro w hw b hb
    have hwq : q ⟨w,hWI hw⟩ = 1 := mem_bot.mp
      (hwbot ▸ mem_map_of_mem q (show (⟨w,hWI hw⟩ : I) ∈ W.subgroupOf I from hw))
    have hwz : (⟨w,hWI hw⟩ : I) ∈ center I := (QuotientGroup.eq_one_iff _).mp hwq
    exact congrArg (fun x : I => (x : G)) (mem_center_iff.mp hwz ⟨b,hLI hb⟩)
  have hw : W = ⊥ := by
    change ⁅D.fullModule,m.tensorPointResidual v⁆ = ⊥
    rw [←m.tensorPoint_moved_idempotent v]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hVC : D.fullModule ≤ centralizer (m.tensorPointResidual v : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hw
  have he : D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) = D.fullModule :=
    inf_eq_left.mpr hVC
  have hh := m.tensorPointResidual_fixed_card v hv
  rw [he,m.card_fullModule] at hh
  norm_num at hh

/-- The original Sylow centralizer gives the full local A₅ section on the
literal central quotient, with its nontrivial two-core. -/
theorem tensorPoint_containing_quotient_local (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ∃ S : Sylow 2 (I ⧸ center I),
      let B := ((m.tensorPointResidual v).subgroupOf I).map (QuotientGroup.mk' (center I))
      B ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup (I ⧸ center I)) ≤ normalizer (B : Set (I ⧸ center I)) ∧
      pCore 2 B ≠ ⊥ ∧ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨R,_hTR,hRM,hSyl⟩ := m.tensorPoint_exists_sylow v
  have hRN := hRM.trans (m.tensorPointResidual_normalized v)
  have hN : (I.subgroupOf (centralizer ({(v : G)} : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer hIN
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hIX hN.isSubnormal
  have hSI : (S : Subgroup I) = R.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  have hl : m.tensorPointResidual v ∈ ChapterA.Section03.localCComponents R :=
    m.tensorPointResidual_cComponent v hv le_sup_left
      (sup_le (m.tensorPointResidual v).le_normalizer hRN)
  let B := (m.tensorPointResidual v).subgroupOf I
  have hBi : B ∈ ChapterA.Section03.localCComponents S := by
    rw [hSI]
    exact ChapterA.Section03.SourceEmbeddings.local_restrict hl hLI
  have hSn : (S : Subgroup I) ≤ normalizer (B : Set I) := by
    rw [hSI,←subgroupOf_normalizer_eq hLI]
    exact comap_mono hRN
  let q := QuotientGroup.mk' (center I)
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (center I)).ker
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun x y =>
      Subtype.ext (mem_center_iff.mp y.property x)
  let a : B ≃* m.tensorPointResidual v := subgroupOfEquivOfLe hLI
  let eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans (m.tensorPointResidualA5Equiv v hv)
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective (center I)),
    Chapter1.Section02.localCComponents_map_of_solvable_ker hBi q,
    (map_mono hSn).trans (B.le_normalizer_map q),
    m.tensorPoint_containing_quotient_residual_core_ne_bot v hv hLI,?_⟩
  exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.section_map q B hBi eB

/-- Held's actual local catalogue excludes the original containing quotient. -/
theorem tensorPoint_containing_not_held (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (a : I ⧸ center I ≃* Held.He) : False := by
  obtain ⟨S,hl,hn,hc,⟨eB⟩⟩ := m.tensorPoint_containing_quotient_local v hv hLI hIX hIN
  exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held.not_section a S _ hl hn hc eB

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
