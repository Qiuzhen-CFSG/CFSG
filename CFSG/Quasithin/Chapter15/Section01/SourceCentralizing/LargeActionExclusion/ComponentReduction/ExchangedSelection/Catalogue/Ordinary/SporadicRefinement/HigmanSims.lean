module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.SporadicRefinement.HigmanSimsCore

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.CentralCoverAbelian
public import Theory.GroupTheory.MSCharacteristicIntrinsicCommutator

/-!
# Excluding the original Higman--Sims component, including central covers

Use the previously constructed escaping perfect residual K in L(G₁,S),
with its surjection onto the actual C₄³ normalizer. The concrete central
extension calculation makes O₂(K) abelian. Source 14.1.6(3) supplies the
characteristic-subgroup obstruction on the full original S. Applying the
abelian MS exponent theorem inside KS now makes [O₂(K),K] elementary,
contradicting its checked surjection onto C₄³.

All relative normality, Sylow restrictions and quotient maps are proved
at their actual carriers. No universal MS classification, exchanged plane,
or centerless-cover assumption is used. The original marker application
retains d, Z₁, row and prime. Binary-linear generation, Ru, and Ordinary22
assembly remain with qt-e-15122-ordinary-pre-exclusion; the independent
nonblock premise retains producer qt-e-1515-constrained-source-catalogue
and final discharge by qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.22, printed p.1100 of refs/quasithin.pdf,
using the genuine abelian-core implication of C.1.31--34, pp.135--137.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem characteristic_equiv_image {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y,hy,rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy,?_⟩
  exact e.apply_symm_apply (a (e y))

/-- The original HS component is impossible. Its escaping perfect residual
has a central cover of the actual C₄³ normalizer; the abelian-core MS exponent
argument contradicts its non-elementary moving core at the full original S. -/
theorem PreExclusionSource.not_higmanSims
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  obtain ⟨K,hKL,hperf,hn,_,_,_,⟨eqK⟩,⟨f,hf,hk,hz⟩,hne,hno⟩ :=
    s.higmanSims_local_core_obstruction (h := h) hG hempty hM hu hL e
  let := hperf
  let J := K ⊔ d.S
  let K0 := K.subgroupOf J
  let ek : K0 ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  let : Group.IsPerfect K0 := Group.IsPerfect.ofSurjective
    (f := ek.symm.toMonoidHom) ek.symm.surjective
  let eq0 := (QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)).trans eqK
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.sl_perfect 3 (by decide)
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq
        Atlas.Comparisons.Exceptional.sl3Two_center_eq_bot).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) := IsQuasisimple.of_mulEquiv eq0.symm
  obtain ⟨Q,hQ⟩ := s.centralizer_sylow.restrict
    (show d.S ≤ J from le_sup_right) (sup_le (hKL.trans d.L_component.1) d.S_le_G1)
  let es : (Q : Subgroup J) ≃* d.S :=
    ((Q : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ)
  have hgen : K0 ⊔ (Q : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left),hQ,
      ←MonoidHom.range_eq_map,range_subtype]
  have hms : ∀ C : Subgroup (Q : Subgroup J), C.Characteristic →
      (C.map (Q : Subgroup J).subtype).Normal → C = ⊥ := by
    intro C hC hCN
    let := hC
    let := hCN
    let D := C.map es.toMonoidHom
    have hD : D.Characteristic := characteristic_equiv_image es C
    by_contra hc
    have hDne : D ≠ ⊥ := fun hh => hc ((map_eq_bot_iff_of_injective _ es.injective).mp hh)
    apply hno D hD hDne
    have hnJ := (C.map (Q : Subgroup J).subtype).le_normalizer_map J.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hnJ
    have he : D.map d.S.subtype = (C.map (Q : Subgroup J).subtype).map J.subtype := by
      rw [map_map,map_map]
      rfl
    rw [he]
    exact le_sup_left.trans hnJ
  let f0 := f.comp ek.toMonoidHom
  have hf0 : Function.Surjective f0 := hf.comp ek.surjective
  have hk0 : IsPGroup 2 f0.ker := by
    rw [show f0 = f.comp ek.toMonoidHom from rfl,←MonoidHom.comap_ker]
    exact hk.comap_of_injective _ ek.injective
  have hz0 : f0.ker ≤ center K0 := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply ek.injective
    exact mem_center_iff.mp (hz hx) (ek y)
  have hc0 := Sporadic.LeechRelated.HS.BlockNormalizer.CentralCoverAbelian.core_abelian f0 hf0 hk0 hz0
  have hc : IsMulCommutative (⁅pCore 2 K0,(⊤ : Subgroup K0)⁆ : Subgroup K0) := by
    apply le_centralizer_iff_isMulCommutative.mp
    exact (commutator_le_left _ _).trans
      ((le_centralizer_iff_isMulCommutative.mpr hc0).trans
        (centralizer_le (commutator_le_left _ _)))
  have hel := MSAbelianCommutator.intrinsic_elementary_of_abelian K0 Q hgen hms hc
  have he : (⁅pCore 2 K0,(⊤ : Subgroup K0)⁆).map ek.toMonoidHom =
      ⁅pCore 2 K,(⊤ : Subgroup K)⁆ := by
    rw [map_commutator,pCore_map_iso,map_top_of_surjective _ ek.surjective]
  apply hne
  rw [←he]
  let := hel
  exact IsElementaryAbelian.map _

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- Exclude HS at the original marker, with the same component, Z₁, row and
source prime, retaining all covering centers. -/
theorem PreparedChosenModule.source_preExclusion_not_higmanSims
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  rintro hL ⟨e⟩
  exact s.not_higmanSims (h := h) hG hempty hM hu hL e

end CFSG.Quasithin.Chapter15.Section01
