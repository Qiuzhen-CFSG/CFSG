module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalOrdinarySource

/-!
# An actual ordinary normal overcomponent in the original HS configuration

The unchanged returned pair lies in the actual singular two-core.
Consequently the central covering kernel vanishes in its star quotient,
and the native common residual forces the containing component to be
ordinary. The original module moves both the residual and the component.
No quasisimplicity or central-kernel containment is added as a source premise.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original escaping HS branch produces an actual normal C-component
with quasisimple intrinsic two-core quotient, moved above the whole singular
two-core and retaining both returned points in its own core. -/
theorem SourceHypothesis.exists_original_hs_ordinary_normal_overcomponent
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ u w : V,
      D.Nonsingular u ∧ D.Nonsingular w ∧ w ≠ u ∧
      ∃ P : Sylow 2 G, ∃ t ∈ (P : Subgroup G),
        (MulAut.conj t) (u : G) = w ∧ (MulAut.conj t) (w : G) = u ∧
        let z := u*w
        z ≠ 1 ∧ ¬ D.Nonsingular z ∧
        (T : Subgroup G) ≤ Gv (z : G) ∧ (P : Subgroup G) ≤ Gv (z : G) ∧
        ¬ Gv (z : G) ≤ M L ∧ (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz ∧
        let B := Gv (u : G) ⊓ Gv (z : G)
        let J := (primeToResidual 3 B).map B.subtype
        J ≤ Kv (u : G) ⊓ Kv (w : G) ∧
        (P : Subgroup G) ≤ normalizer (J : Set G) ∧
        Group.IsPerfect J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∧
        ¬ ⁅V,J⁆ ≤ (Gv (z : G)).pCoreIn 2 ∧
        ∃ K : Subgroup G, K ≤ Gv (z : G) ∧
          (K.subgroupOf (Gv (z : G))).IsCComponent ∧
          IsQuasisimple (K ⧸ pCore 2 K) ∧ J ≤ K ∧
          Gv (z : G) ≤ normalizer (K : Set G) ∧
          (u : G) ∈ K.pCoreIn 2 ∧ (w : G) ∈ K.pCoreIn 2 ∧
          ¬ ⁅V,K⁆ ≤ (Gv (z : G)).pCoreIn 2 := by
  classical
  obtain ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hsz,hTz,hPz,hout,hHz,
    hK,hnot,⟨e⟩,S,hzS,hJC,hPJ,hJ,hperf,hquot⟩ :=
    H.exists_original_hs_singular_local_component D hTV hTI v hv he
  let z : V := u*w
  let B := Gv (u : G) ⊓ Gv (z : G)
  let J := (primeToResidual 3 B).map B.subtype
  have hzc : (z : G) ∉ centralizer (Kv (u : G) : Set G) := by
    intro hc
    have hmem : (z : G) ∈ zpowers (u : G) :=
      (H.nonsingular_hs_original_geometry D u hu hK hTV hnot e).2.1 ▸ ⟨z.property,hc⟩
    have huo : orderOf (u : G) = 2 := by
      apply orderOf_eq_prime
      · exact elemPow_eq_one_of_isElementaryAbelian (u : G) u.property
      · intro hh
        exact nonsingular_ne_one D hu (Subtype.ext hh)
    rw [mem_zpowers_iff_mem_range_orderOf,huo] at hmem
    obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp hmem
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · apply hz
      apply Subtype.ext
      change (z : G) = 1
      simpa only [pow_zero] using hei.symm
    · have hzsing : ¬ D.Nonsingular z := hsz
      apply hzsing
      have hzu : z = u := Subtype.ext (by simpa using hei.symm)
      rw [hzu]
      exact hu
  have hmove := H.nonsingular_hs_common_residual_moved D u hu hK e S z hzS hzc
  have hpoint := H.original_hs_nonsingular_pair_mem_singular_core
    D hTV hTI v hv he hZ u w hu hw hz hsz
  have hHz' : Gv (z : G) ∈ (D.fullSetup hZ T z).Hz := by
    rwa [(D.fullSetup hZ T z).Gz_eq] at hHz
  obtain ⟨K,⟨hKGz,hKC,hJK,hKN⟩,_⟩ :=
    H.original_singular_normal_overcomponent D hZ z hz hHz' P hPz hJ hPJ
  have hZJ := H.nonsingular_hs_center_le_common_residual D u hu hK e S (z : G) hzS
    (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property) hzc
  have hcenter := (H.nonsingular_hs_original_geometry D u hu hK hTV hnot e).2.2.2
  have huJ : (u : G) ∈ J := hZJ (hcenter.symm ▸ mem_zpowers (u : G))
  have hwJ : (w : G) ∈ J := by
    have hconj := mem_normalizer_iff_map_conj_eq.mp (hPJ ht)
    change J.map (MulAut.conj t).toMonoidHom = J at hconj
    rw [←htu]
    exact hconj ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom huJ
  have huCore : (u : G) ∈ K.pCoreIn 2 :=
    (inf_pCoreIn_le_of_le 2 hKGz) ⟨hJK huJ,hpoint.2.2.2.1⟩
  have hwCore : (w : G) ∈ K.pCoreIn 2 :=
    (inf_pCoreIn_le_of_le 2 hKGz) ⟨hJK hwJ,hpoint.2.2.2.2⟩
  have hcenterCore : (center (Kv (u : G))).map (Kv (u : G)).subtype ≤
      (Gv (z : G)).pCoreIn 2 := by
    rw [hcenter]
    exact zpowers_le.mpr hpoint.2.2.2.1
  have hordinary := H.nonsingular_hs_overcomponent_quasisimple D hZ z hz hHz'
    u hu hK e S hzS hzc hcenterCore hKGz hKC hJK
  refine ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hsz,hTz,hPz,hout,hHz,
    hJC,hPJ,hperf,hquot,hmove,K,hKGz,hKC,hordinary,hJK,hKN,huCore,hwCore,?_⟩
  exact fun hc => hmove ((commutator_mono le_rfl hJK).trans hc)

end CFSG.Quasithin.Chapter12.Section06
