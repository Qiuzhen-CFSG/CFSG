module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointNormalitySource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Normalizer
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerSingularity

/-!
# Choosing the original nonsingular point with a Sylow centralizer

The ambient point-centralizer Sylow supplied by the full-module fusion theorem
lies in the maximal local subgroup M. Conjugate it into the original T inside M.
Sylow maximality then identifies its image with the literal C_T(w), while the
binary matrix normalizer preserves nonsingularity. The actual component-orbit
point centralizer and its two-residual commute with this conjugation.

Thus normality for all nonsingular points reduces to the source choice
C_T(w) ∈ Syl₂(M ∩ C_G(w)); no additional fusion or placement premise remains.
This discharges the initial Sylow choice in Aschbacher–Smith 9.4.1,
printed p.735. The exclusion of strict containing components is separate.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual maximal-local conjugation preserves nonsingularity. -/
theorem tensorPoint_nonsingular_of_maximal_conjugate
    (v w : D.fullModule) (g : D.maximalLocal)
    (hconj : MulAut.conj (g : G) (v : G) = (w : G))
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    ((m.sectionData.coordinates w).toAdd).det ≠ 0 := by
  have he : D.fullModule.normalizerMonoidHom
      ⟨g,D.maximalLocal_normalizes_fullModule g.property⟩ v = w := Subtype.ext hconj
  have hc := m.maximalAction_coordinates g v
  rw [he] at hc
  rw [←hc]
  exact mt (Binary.normalizer_det_zero_iff _ (m.maximalAction_mem_normalizer g) _).mp hv

/-- Conjugation inside M carries the literal orbit point centralizer to its counterpart. -/
theorem tensorPointCentralizer_conjugate
    (v w : D.fullModule) (g : D.maximalLocal)
    (hconj : MulAut.conj (g : G) (v : G) = (w : G)) :
    (m.tensorPointCentralizer v).map (MulAut.conj (g : G)).toMonoidHom =
      m.tensorPointCentralizer w := by
  have ho : (localOrbit T L).map (MulAut.conj (g : G)).toMonoidHom = localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp g.property
  rw [tensorPointCentralizer,map_inf _ _ _ (MulAut.conj (g : G)).injective,
    ho,map_centralizer_equiv,Set.image_singleton,hconj]
  rfl

/-- The literal diagonal two-residual commutes with maximal-local conjugation. -/
theorem tensorPointResidual_conjugate
    (v w : D.fullModule) (g : D.maximalLocal)
    (hconj : MulAut.conj (g : G) (v : G) = (w : G)) :
    (m.tensorPointResidual v).map (MulAut.conj (g : G)).toMonoidHom =
      m.tensorPointResidual w := by
  rw [tensorPointResidual,map_embedded_pResidual,
    m.tensorPointCentralizer_conjugate v w g hconj]
  rfl

/-- Normality at a maximal-local conjugate transports back to the original point. -/
theorem tensorPointResidual_normality_of_maximal_conjugate
    (v w : D.fullModule) (g : D.maximalLocal)
    (hconj : MulAut.conj (g : G) (v : G) = (w : G))
    (hw : centralizer ({(w : G)} : Set G) ≤
      normalizer (m.tensorPointResidual w : Set G)) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G) := by
  apply (map_le_map_iff_of_injective (f := (MulAut.conj (g : G)).toMonoidHom)
    (MulAut.conj (g : G)).injective).mp
  rwa [map_centralizer_equiv,Set.image_singleton,hconj,
    map_normalizer_eq_of_bijective _ (MulAut.conj (g : G)).bijective,
    m.tensorPointResidual_conjugate v w g hconj]

/-- Every nonsingular point has a maximal-local conjugate satisfying the original
Sylow choice, with the literal intersection C_T(w). -/
theorem exists_maximal_conjugate_sylow_point (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    ∃ (g : D.maximalLocal) (w : D.fullModule),
      MulAut.conj (g : G) (v : G) = (w : G) ∧
      ((m.sectionData.coordinates w).toAdd).det ≠ 0 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G))
        (D.maximalLocal ⊓ centralizer ({(w : G)} : Set G)) := by
  obtain ⟨R,_hTR,hRM,hSyl⟩ := m.tensorPoint_exists_sylow v
  have hp := (Chapter1.isSylowIn_iff.mp hSyl).1
  obtain ⟨P,hRP⟩ := (hp.comap_subtype :
    IsPGroup 2 (R.subgroupOf D.maximalLocal)).exists_le_sylow
  let S := T.subtype (le_normalizer_componentOrbit L T)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D.maximalLocal P S
  let f := MulAut.conj (g : G)
  let w := D.fullModule.normalizerMonoidHom
    ⟨g,D.maximalLocal_normalizes_fullModule g.property⟩ v
  have hw : f (v : G) = (w : G) := rfl
  have hRT : R.map f.toMonoidHom ≤ (T : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    have hmem : MulAut.conj g ⟨y,(hRM hy).1⟩ ∈ (S : Subgroup D.maximalLocal) := by
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hRP hy)
    exact hmem
  have hSyl' := (Chapter1.IsSylowIn.map_iff f.toMonoidHom f.injective).mpr hSyl
  rw [map_centralizer_equiv,Set.image_singleton,hw] at hSyl'
  have hmax := Chapter1.isSylowIn_iff.mp hSyl'
  have he : (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) =
      R.map f.toMonoidHom :=
    hmax.2.2 _ (T.isPGroup'.to_le inf_le_left) (le_inf hRT hmax.2.1) inf_le_right
  refine ⟨g,w,hw,m.tensorPoint_nonsingular_of_maximal_conjugate v w g hw hv,?_⟩
  exact he.symm ▸ hSyl'.restrict (by
    rw [←he]
    exact inf_le_inf (le_normalizer_componentOrbit L T) le_rfl) inf_le_right

/-- It suffices to prove source 9.4.1 for nonsingular points with the original
Sylow choice in M; both placement and transport are discharged here. -/
theorem tensorPointResidual_normality_of_sylow_points
    (hgood : ∀ w : D.fullModule,
      ((m.sectionData.coordinates w).toAdd).det ≠ 0 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G))
        (D.maximalLocal ⊓ centralizer ({(w : G)} : Set G)) →
      centralizer ({(w : G)} : Set G) ≤ normalizer (m.tensorPointResidual w : Set G))
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G) := by
  obtain ⟨g,w,hconj,hw,hs⟩ := m.exists_maximal_conjugate_sylow_point v hv
  exact m.tensorPointResidual_normality_of_maximal_conjugate v w g hconj (hgood w hw hs)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
