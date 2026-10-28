module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUpRank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.FittingOvergroup
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.NormalityReduction

/-!
# Excluding the contained generalized-Fitting branch of pushing up

In an overgroup of F*(H/O₂(H)), the local two-core quotient has trivial
two-core. The covering residual therefore maps to an ordinary component,
which promotes through F* and lifts to a C-component of H. Its full natural
quotient forces normality by odd rank. The genuine C.2.12 normalizer identity
then contradicts strict local containment.

This excludes the contained-Fitting alternative without assuming that the
residual is nonnormal in the local subgroup: in the actual application it
is already normal there. The escaping-component classification remains.
Source: Aschbacher--Smith C.2.13 and C.4.8, printed pp.148,153, used in
4.2.12--13 and 4.4.6, printed pp.610--611,620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G]

private theorem component_of_fitting_overgroup {B M : Subgroup G} (hBM : B ≤ M)
    (hB : (B.subgroupOf M).IsCComponent) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hF : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ M) : B.IsCComponent := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let C := M.map q
  let f := q.subgroupMap M
  let D := B.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.subgroupMap M).ker
    rw [ker_subgroupMap]
    change Group.IsSolvable ((QuotientGroup.mk' (pCore 2 G)).ker.subgroupOf M)
    rw [QuotientGroup.ker_mk']
    change Group.IsSolvable ((pCore 2 G).comap M.subtype)
    exact Group.isSolvable_of_isSolvable_injective
      (f := M.subtype.subgroupComap (pCore 2 G)) (fun a b he =>
        Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 G => (x : G)) he)))
  have he : (B.subgroupOf M).map f = D.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact mem_map.mpr ⟨b,hb,rfl⟩
    · rintro ⟨b,hb,hbx⟩
      exact ⟨⟨b,hBM hb⟩,hb,Subtype.ext hbx⟩
  have hD : (D.subgroupOf C).IsCComponent :=
    he ▸ cComponent_map_of_solvable_ker hB f (q.subgroupMap_surjective M)
  have hFC : generalizedFitting (G ⧸ pCore 2 G) ≤ C := by
    have hh := map_mono (f := q) hF
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hh
  have hDC : D ≤ C := map_mono hBM
  have hcoreC : pCore 2 C = ⊥ :=
    twoCore_eq_bot_of_generalizedFitting_le C hFC (pCore_quotient_pCore_eq_bot 2)
  have hcoreD' : pCore 2 (D.subgroupOf C) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hD.subnormal, hcoreC]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (D.subgroupOf C).subtype_injective
  have hcoreD : pCore 2 D = ⊥ := by
    rw [← pCore_map_iso 2 (subgroupOfEquivOfLe hDC), hcoreD', Subgroup.map_bot]
  let fB := q.subgroupMap B
  have hk : IsPGroup 2 fB.ker := by
    change IsPGroup 2 (q.subgroupMap B).ker
    rw [ker_subgroupMap]
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 G)).ker.subgroupOf B)
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  have heker : fB.ker = pCore 2 B := by
    have hh := fB.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective B) hk
    rw [hcoreD] at hh
    exact hh
  let e : (B ⧸ pCore 2 B) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq heker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fB (q.subgroupMap_surjective B))
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e
  let : IsQuasisimple (D.subgroupOf C) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hDC).symm
  have hDcomp : IsComponent (G ⧸ pCore 2 G) D :=
    IsComponent.of_generalizedFitting_overgroup hDC ⟨hD.subnormal,inferInstance⟩ hFC
  let := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBM).toMonoidHom) (subgroupOfEquivOfLe hBM).surjective
  obtain ⟨K,hK,hBK,himage⟩ := exists_cComponent_lift_containing_map
    (B := B) (pCore 2 G) hDcomp.isCComponent le_rfl
  have hKM : K ≤ M := by
    have hh : K ≤ B ⊔ pCore 2 G := by
      simpa only [D,q,comap_map_eq,QuotientGroup.ker_mk'] using
        map_le_iff_le_comap.mp himage.le
    apply hh.trans
    apply sup_le hBM
    have hk : pCore 2 G ≤ (generalizedFitting (G ⧸ pCore 2 G)).comap q := by
      simpa only [q,QuotientGroup.ker_mk'] using
        MonoidHom.ker_le_comap q (generalizedFitting (G ⧸ pCore 2 G))
    exact hk.trans hF
  have hBK' := hB.eq_of_le (hK.subgroupOf hKM) (comap_mono hBK)
  have hBK'' : B = K := by
    have hh := congrArg (map M.subtype) hBK'
    simpa only [map_subgroupOf_eq_of_le hBM,map_subgroupOf_eq_of_le hKM] using hh
  exact hBK''.symm ▸ hK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The literal C.2.8 configuration must have an escaping generalized-Fitting component. -/
theorem pushingUp_fitting_escape {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L)) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
  intro hf
  have hBH := h.component_le.trans h.local_le
  let A := B.subgroupOf H
  let N := M.subgroupOf H
  let eM : N ≃* M := subgroupOfEquivOfLe h.local_le
  let eB : A ≃* B := subgroupOfEquivOfLe hBH
  let eqB : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans e
  let := S.source.toHypothesis1221.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eqB.symm
  have he : (B.subgroupOf M).map eM.symm.toMonoidHom = A.subgroupOf N := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact hb
    · intro hx
      exact ⟨⟨(x : H),x.property⟩,hx,rfl⟩
  have hA : A.IsCComponent := component_of_fitting_overgroup
    (comap_mono h.component_le) (he ▸ h.component.map_equiv eM.symm) hf
  let : A.Normal := normal_of_natural_core_quotient D S h.sqtk A hA eqB
  have hs : conjugateSpanBy B M = B := h.span_eq_of_ambient_component hstrict hA
  have hHN : H ≤ normalizer (B : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [A,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hBH] using hh
  have hHM : H ≤ M := by
    rw [← h.normalizer_span_eq, hs]
    exact le_inf le_rfl hHN
  exact hstrict.not_ge hHM

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
