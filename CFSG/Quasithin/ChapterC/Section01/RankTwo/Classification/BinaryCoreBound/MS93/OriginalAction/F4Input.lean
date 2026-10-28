module
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCanonicalSylow
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.OriginalAction.F4SourceHypotheses
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.OriginalAction.F4Characteristic
/-!
# Complete MS input on the original binary F4 parabolic

The canonical positive subgroup is identified with a full Sylow subgroup of
the same explicit matrix parabolic used by the original-core calculation.
Transporting the canonical characteristic-subgroup theorem through this
actual isomorphism supplies MS3. Together with `F4SourceHypotheses`, this
constructs every field of the genuine binary MS input on one carrier.

The existing explicit fixed factor still fails to centralize the original
two-core. Thus all these input clauses do not imply that proposed local
centrality conclusion. This module makes no replacement-to-original
centrality transfer. The full five-alternative interface is checked separately.

Sources: Aschbacher--Smith C.1.31--34, printed pp.135--137, especially the
original-group centrality clause of C.1.34(4); Meierfrankenfeld--Stellmacher
(1993), the F4 examples on printed p.831 and the replacement calculation
(4.4)--(4.5).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
open Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates
private theorem characteristic_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (C : Subgroup G) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y,hy,rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy,?_⟩
  exact e.apply_symm_apply _

private theorem msCharacteristic_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (R : Subgroup G) (S : Subgroup H)
    (hRS : R.map e.toMonoidHom = S) (h : MSCharacteristicCondition R) :
    MSCharacteristicCondition S := by
  let eR : R ≃* S := (e.subgroupMap R).trans (MulEquiv.subgroupCongr hRS)
  intro C hc hne hn
  let := hc
  let D := C.map eR.symm.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv eR.symm C
  have hD : D ≠ ⊥ := fun hd => hne ((map_eq_bot_iff_of_injective C eR.symm.injective).mp hd)
  have he : D.map R.subtype = (C.map S.subtype).map e.symm.toMonoidHom := by
    rw [show D = C.map eR.symm.toMonoidHom from rfl, map_map,map_map]
    congr 1
  have hnD : (D.map R.subtype).Normal := he.symm ▸ hn.map e.symm.toMonoidHom e.symm.surjective
  exact h D inferInstance hD hnD

/-- MS3 for the full Sylow subgroup of the same binary matrix parabolic. -/
theorem originalSylow_msCharacteristic :
    MSCharacteristicCondition (Canonical.originalSylow : Subgroup P) := by
  rw [Canonical.originalSylow_coe]
  exact @msCharacteristic_map_equiv
    (Theory.SpecificGroups.LieType.F4LongParabolic.longParabolic 0) P
    (inferInstance : Group (Theory.SpecificGroups.LieType.F4LongParabolic.longParabolic 0))
    (inferInstance : Group P) Canonical.parabolicEquiv
    _ _ Canonical.parabolicEquiv_positive (positiveInParabolic_msCharacteristic 0)

/-- All genuine binary MS input clauses on the original matrix carrier. -/
noncomputable def originalInput :
    BinaryMS.Input KnownSimple.IsKnownSimple (L.subgroupOf P)
      (Canonical.originalSylow : Subgroup P) :=
  originalInput_of_characteristic Canonical.originalSylow originalSylow_msCharacteristic

/-- Original two-core fixation fails even under every binary MS input clause.
This concerns the original parabolic, not the characteristic replacement. -/
theorem original_input_fixed_not_central :
    Nonempty (BinaryMS.Input KnownSimple.IsKnownSimple (L.subgroupOf P)
      (Canonical.originalSylow : Subgroup P)) ∧
    ¬ BinaryMS.commutatorCore (L.subgroupOf P) ⊓
      centralizer (L.subgroupOf P : Set P) ≤ centralizer (pCore 2 P : Set P) :=
  ⟨⟨originalInput⟩, original_binaryCore_fixed_not_central⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
