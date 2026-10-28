module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointResidual
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorCorankPairs
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorFusionSource
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointGeneration

/-!
The actual diagonal residuals above two nonsingular field lines generate L₀.
Thus source 9.4.1 point-normality gives the pair-centralizer bound 9.4.2 and
the corank bound r(G,V)>3. Thompson weak closure upgrades each such
centralizer bound to a normalizer bound, giving uniqueness of the full module
through every subgroup containing the pair. Point normality is the one
independent source input retained by these implications.

Source: Aschbacher--Smith, 9.4.1--3, printed pp.735--736.
-/

public section
open Subgroup Theory.GroupTheory Representation Stellmacher
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

theorem tensorPointResidual_pair_sup (v w : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hw : ((m.sectionData.coordinates w).toAdd).det ≠ 0)
    (hne : (m.sectionData.coordinates w).toAdd ∉
      Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V)) :
    m.tensorPointResidual v ⊔ m.tensorPointResidual w = localOrbit T L := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) Binary.F) := m.firstMarking.symm.isSimpleGroup
  exact m.tensorPointResidual_sup_eq_of_stabilizers_generate v w hv hw
    (pointStabilizer_sup_eq_top _ _ hv hw hne)

theorem tensor_pair_centralizer_le_of_point_normality
    (hpoint : ∀ v : D.fullModule, ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G))
    (v w : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hw : ((m.sectionData.coordinates w).toAdd).det ≠ 0)
    (hne : (m.sectionData.coordinates w).toAdd ∉
      Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V)) :
    centralizer ({(v : G),(w : G)} : Set G) ≤ D.maximalLocal := by
  change centralizer ({(v : G),(w : G)} : Set G) ≤ normalizer (localOrbit T L : Set G)
  rw [← m.tensorPointResidual_pair_sup v w hv hw hne]
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_inf
  · exact (centralizer_le (by simp)).trans (hpoint v hv)
  · exact (centralizer_le (by simp)).trans (hpoint w hw)

theorem tensor_globalR_gt_three_of_point_normality
    (hpoint : ∀ v : D.fullModule, ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G)) :
    3 < ChapterE.globalR D.fullModule :=
  m.globalR_gt_three_of_nonsingular_pair_control
    (m.tensor_pair_centralizer_le_of_point_normality hpoint)

theorem tensor_normalizer_le_of_centralizer_le {U : Subgroup G}
    (hUV : U ≤ D.fullModule) (hCU : centralizer (U : Set G) ≤ D.maximalLocal) :
    normalizer (U : Set G) ≤ D.maximalLocal := by
  intro g hg
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let A := J.map (MulAut.conj g).toMonoidHom
  have hJC : J ≤ centralizer (U : Set G) :=
    m.thompson_centralizes_fullModule.trans (centralizer_le hUV)
  have hAM : A ≤ D.maximalLocal := by
    apply le_trans _ hCU
    have he : U.map (MulAut.conj g).toMonoidHom = U := mem_normalizer_iff_map_conj_eq.mp hg
    have hc := (map_mono (f := (MulAut.conj g).toMonoidHom) hJC).trans
      (map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj g).toMonoidHom)
    change A ≤ centralizer (U.map (MulAut.conj g).toMonoidHom : Set G) at hc
    rwa [he] at hc
  have hJp : IsPGroup 2 J := T.isPGroup'.to_le (sSup_le fun _ h => h.1)
  obtain ⟨Q,hQ⟩ := ((hJp.map (MulAut.conj g).toMonoidHom).comap_subtype
    (K := D.maximalLocal)).exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq D.maximalLocal Q D.ambientSylow
  have hm : (Q : Subgroup D.maximalLocal).map (MulAut.conj c).toMonoidHom =
      (T : Subgroup G).subgroupOf D.maximalLocal := by
    exact congrArg Sylow.toSubgroup hc
  have hcg : (c : G) * g ∈ normalizer (J : Set G) := by
    apply maxJ_weakly_closed_normalizer T
    rintro _ ⟨j,hj,rfl⟩
    have hjA : MulAut.conj g j ∈ A := mem_map_of_mem _ hj
    have hh := map_mono (f := (MulAut.conj c).toMonoidHom) hQ
      (mem_map_of_mem _ (show (⟨MulAut.conj g j,hAM hjA⟩ : D.maximalLocal) ∈
        A.subgroupOf D.maximalLocal from hjA))
    rw [hm] at hh
    change (c : G) * (g*j*g⁻¹) * (c : G)⁻¹ ∈ (T : Subgroup G) at hh
    change ((c : G)*g)*j*((c : G)*g)⁻¹ ∈ (T : Subgroup G)
    simpa only [mul_inv_rev,mul_assoc] using hh
  have hcgM := source_thompson_normalizer_le_of_centralizes D
    m.thompson_centralizes_fullModule hcg
  have hh := D.maximalLocal.mul_mem (D.maximalLocal.inv_mem c.property) hcgM
  simpa only [←mul_assoc,inv_mul_cancel,one_mul] using hh

theorem tensor_unique_conjugate_of_nonsingular_pair
    (hpoint : ∀ v : D.fullModule, ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G))
    (v w : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hw : ((m.sectionData.coordinates w).toAdd).det ≠ 0)
    (hne : (m.sectionData.coordinates w).toAdd ∉
      Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V))
    {U : Subgroup G} (hUV : U ≤ D.fullModule) (hvU : (v : G) ∈ U) (hwU : (w : G) ∈ U)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule := by
  apply m.tensor_unique_conjugate hUV _ g hg
  apply m.tensor_normalizer_le_of_centralizer_le hUV
  apply le_trans _ (m.tensor_pair_centralizer_le_of_point_normality hpoint v w hv hw hne)
  exact centralizer_le (by simpa only [Set.insert_subset_iff,Set.singleton_subset_iff] using ⟨hvU,hwU⟩)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
