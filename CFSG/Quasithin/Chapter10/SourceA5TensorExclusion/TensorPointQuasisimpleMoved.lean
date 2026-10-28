module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleLocal
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The moved module in the original point-component central quotient

For W=[V,L₀], the actual point-stabilizer map sends O₂(L₀) trivially,
so this core centralizes V. Prime cores map onto prime cores through a
central quotient, giving the corresponding centralizer bound for the
literal images E and B in I/Z(I). Commutator idempotence makes E fully
moved by B. The original Sylow centralizer normalizes both V and L₀;
its image therefore supplies one Sylow group normalizing B and E.

These are the moved-module marks in the Janko-four local-section
exclusion used in Aschbacher--Smith 9.4.1, printed p.735.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The two-core of the actual point residual acts trivially on V. -/
theorem tensorPointResidual_core_le_centralizer_fullModule (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    (m.tensorPointResidual v).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
  let f := (m.tensorPointStabilizerEquiv v hv).toMonoidHom.comp
    (m.tensorPointResidualQuotient v)
  have hf : Function.Surjective f := (m.tensorPointStabilizerEquiv v hv).surjective.comp
    (m.tensorPointResidualQuotient_surjective v hv)
  have hc : (pCore 2 (m.tensorPointResidual v)).map f ≤
      pCore 2 (alternatingGroup (Fin 5)) :=
    le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  rw [alternatingGroup.five_twoCore_eq_bot] at hc
  rintro x ⟨r,hr,rfl⟩
  let rO : localOrbit T L := ⟨r,m.tensorPointResidual_le_orbit v r.property⟩
  apply (m.centralizer_localOrbit_iff rO).mpr
  have hr1 : f r = 1 := mem_bot.mp (hc (mem_map_of_mem f hr))
  have hq1 : m.tensorPointResidualQuotient v r = 1 :=
    (m.tensorPointStabilizerEquiv v hv).injective (hr1.trans (map_one _).symm)
  change m.quotient rO = 1
  exact congrArg Subtype.val hq1

/-- The literal moved image is elementary, fully moved, and centralized
by the two-core of the literal residual image. -/
theorem tensorPoint_containing_quotient_moved_marks (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    let B := ((m.tensorPointResidual v).subgroupOf I).map (QuotientGroup.mk' (center I))
    let E := ((⁅D.fullModule,m.tensorPointResidual v⁆).subgroupOf I).map
      (QuotientGroup.mk' (center I))
    IsElementaryAbelian 2 E ∧ E ≤ B ∧
      B.pCoreIn 2 ≤ centralizer (E : Set (I ⧸ center I)) ∧ ⁅E,B⁆ = E := by
  let W := ⁅D.fullModule,m.tensorPointResidual v⁆
  let B := (m.tensorPointResidual v).subgroupOf I
  let E := W.subgroupOf I
  let q := QuotientGroup.mk' (center I)
  have hWL : W ≤ m.tensorPointResidual v := le_normalizer_iff_commutator_le_right.mp
    (m.tensorPointResidual_fullModule_normalized v)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)
  have hWI := hWL.trans hLI
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hWI
  refine ⟨IsElementaryAbelian.map q, map_mono (comap_mono hWL), ?_, ?_⟩
  · have hce : B.pCoreIn 2 ≤ centralizer (E : Set I) := by
      rw [pCoreIn_subgroupOf 2 _ I hLI]
      intro r hr w hw
      exact Subtype.ext (m.tensorPointResidual_core_le_centralizer_fullModule v hv hr w (hWV hw))
    have hk : (q.subgroupMap B).ker ≤ center B := by
      intro b hb
      have hz : (b : I) ∈ center I := (QuotientGroup.eq_one_iff _).mp
        (congrArg Subtype.val (MonoidHom.mem_ker.mp hb))
      exact mem_center_iff.mpr fun c => Subtype.ext (mem_center_iff.mp hz c)
    have hm := (q.subgroupMap B).map_pCore_of_central_kernel
      (q.subgroupMap_surjective B) hk (p := 2)
    have he : (B.pCoreIn 2).map q = (B.map q).pCoreIn 2 := by
      calc
        _ = ((pCore 2 B).map (q.subgroupMap B)).map (B.map q).subtype := by
          rw [pCoreIn,map_map,map_map]
          rfl
        _ = _ := by rw [hm]; rfl
    rw [←he]
    exact (map_mono hce).trans (map_centralizer_le_centralizer_image (E : Set I) q)
  · change ⁅E.map q,B.map q⁆ = E.map q
    rw [←map_commutator]
    congr 1
    apply map_injective I.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWI,map_subgroupOf_eq_of_le hLI]
    exact m.tensorPoint_moved_idempotent v

/-- One original Sylow centralizer supplies the local residual section
and simultaneously normalizes its literal moved module. -/
theorem tensorPoint_containing_quotient_moved_local (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ∃ S : Sylow 2 (I ⧸ center I),
      let B := ((m.tensorPointResidual v).subgroupOf I).map (QuotientGroup.mk' (center I))
      let E := ((⁅D.fullModule,m.tensorPointResidual v⁆).subgroupOf I).map
        (QuotientGroup.mk' (center I))
      B ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup (I ⧸ center I)) ≤ normalizer (B : Set (I ⧸ center I)) ∧
      pCore 2 B ≠ ⊥ ∧ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) ∧
      (S : Subgroup (I ⧸ center I)) ≤ normalizer (E : Set (I ⧸ center I)) := by
  obtain ⟨R,_hTR,hRM,hSyl⟩ := m.tensorPoint_exists_sylow v
  have hRN := hRM.trans (m.tensorPointResidual_normalized v)
  have hRV : R ≤ normalizer (D.fullModule : Set G) := by
    rw [source_fullModule_normalizer D]
    exact hRM.trans inf_le_left
  let W := ⁅D.fullModule,m.tensorPointResidual v⁆
  have hRW : R ≤ normalizer (W : Set G) := by
    intro r hr
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hRV hr),
      mem_normalizer_iff_map_conj_eq.mp (hRN hr)]
  have hWI : W ≤ I := (le_normalizer_iff_commutator_le_right.mp
    (m.tensorPointResidual_fullModule_normalized v)).trans hLI
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
  have hSe : (S : Subgroup I) ≤ normalizer (W.subgroupOf I : Set I) := by
    rw [hSI,←subgroupOf_normalizer_eq hWI]
    exact comap_mono hRW
  let q := QuotientGroup.mk' (center I)
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (center I)).ker
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun x y =>
      Subtype.ext (mem_center_iff.mp y.property x)
  let a : B ≃* m.tensorPointResidual v := subgroupOfEquivOfLe hLI
  let eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans (m.tensorPointResidualA5Equiv v hv)
  exact ⟨S.mapSurjective (QuotientGroup.mk'_surjective (center I)),
    Chapter1.Section02.localCComponents_map_of_solvable_ker hBi q,
    (map_mono hSn).trans (B.le_normalizer_map q),
    m.tensorPoint_containing_quotient_residual_core_ne_bot v hv hLI,
    ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.section_map q B hBi eB,
    (map_mono hSe).trans ((W.subgroupOf I).le_normalizer_map q)⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
