module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Conjugation
public import Theory.GroupTheory.CentralCoprimeLiftUnique
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Exact involution-centralizer descent through the central root kernel

The root kernel is central of order three. Uniqueness of order-two lifts
therefore identifies the full preimage of the quotient involution centralizer
with the original centralizer. Restriction of the quotient map gives an actual
quotient equivalence and the factor-three cardinality formula. Sylow subgroups
also descend isomorphically through this odd kernel.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, printed p.237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

noncomputable section
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)

@[expose] public def quotientInvolution : rootQuotient D e L :=
  QuotientGroup.mk' (rootKernel D e L) (involution D e L)

public theorem quotientInvolution_order : orderOf (quotientInvolution D e L) = 2 := by
  apply orderOf_eq_prime
  · change (QuotientGroup.mk' (rootKernel D e L) (involution D e L)) ^ 2 = 1
    rw [← map_pow, ← involution_order D e L, pow_orderOf_eq_one, map_one]
  · intro h
    have ht : involution D e L ∈ rootKernel D e L := (QuotientGroup.eq_one_iff _).mp h
    have hd := orderOf_dvd_natCard (⟨involution D e L, ht⟩ : rootKernel D e L)
    have ho : orderOf (⟨involution D e L, ht⟩ : rootKernel D e L) = 2 :=
      (Subgroup.orderOf_coe _).symm.trans (involution_order D e L)
    rw [ho, rootKernel_card] at hd
    norm_num at hd

public theorem centralizer_lifts (x : rootCentralizer D e L) :
    QuotientGroup.mk' (rootKernel D e L) x ∈
      centralizer ({quotientInvolution D e L} : Set (rootQuotient D e L)) ↔
        x ∈ centralizerInRoot D e L := by
  let q := QuotientGroup.mk' (rootKernel D e L)
  constructor
  · intro hx
    have hc := mem_centralizer_singleton_iff.mp hx
    have hconj : q (x * involution D e L * x⁻¹) = q (involution D e L) := by
      rw [map_mul, map_mul, map_inv]
      change q x * quotientInvolution D e L * (q x)⁻¹ = quotientInvolution D e L
      rw [hc, mul_inv_cancel_right]
    have hker : q.ker = rootKernel D e L := QuotientGroup.ker_mk' _
    have hcenter : q.ker ≤ center (rootCentralizer D e L) := by
      rw [hker]
      exact rootKernel_le_center D e L
    have hp : IsPGroup 3 q.ker := by
      apply IsPGroup.of_card (n := 1)
      rw [hker, rootKernel_card]
      rfl
    have ht : involution D e L ^ 2 = 1 := by
      rw [← involution_order D e L, pow_orderOf_eq_one]
    have h := q.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker hcenter hp
      (by decide : Nat.Coprime 3 2) hconj (by
        change (MulAut.conj x (involution D e L)) ^ 2 = 1
        rw [← map_pow, ht, map_one]) ht
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
  · intro hx
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute x (involution D e L) from mem_centralizer_singleton_iff.mp hx).map q).eq

@[expose] public def quotientCentralizerMap : centralizerInRoot D e L →*
    centralizer ({quotientInvolution D e L} : Set (rootQuotient D e L)) where
  toFun x := ⟨QuotientGroup.mk' (rootKernel D e L) x,
    (centralizer_lifts D e L x).mpr x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

public theorem quotientCentralizerMap_surjective : Function.Surjective (quotientCentralizerMap D e L) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (rootKernel D e L) y
  exact ⟨⟨x, (centralizer_lifts D e L x).mp (hx ▸ y.property)⟩, Subtype.ext hx⟩

public abbrev localKernel : Subgroup (centralizerInRoot D e L) :=
  (rootKernel D e L).subgroupOf (centralizerInRoot D e L)

public theorem quotientCentralizerMap_ker : (quotientCentralizerMap D e L).ker = localKernel D e L := by
  ext x
  change quotientCentralizerMap D e L x = 1 ↔ (x : rootCentralizer D e L) ∈ rootKernel D e L
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

@[expose] public def localQuotientEquiv : centralizerInRoot D e L ⧸ localKernel D e L ≃*
    centralizer ({quotientInvolution D e L} : Set (rootQuotient D e L)) :=
  (QuotientGroup.quotientMulEquivOfEq (quotientCentralizerMap_ker D e L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (quotientCentralizerMap_surjective D e L))

public theorem rootKernel_le_centralizerInRoot : rootKernel D e L ≤ centralizerInRoot D e L := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (mem_center_iff.mp (rootKernel_le_center D e L hx) (involution D e L)).symm

public theorem localKernel_card : Nat.card (localKernel D e L) = 3 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (rootKernel_le_centralizerInRoot D e L)).toEquiv,
    rootKernel_card]

public theorem quotientCentralizer_card_mul [Finite G] :
    Nat.card (centralizer ({quotientInvolution D e L} : Set (rootQuotient D e L))) * 3 =
      Nat.card (intersection D e L) := by
  rw [← Nat.card_congr (localQuotientEquiv D e L).toEquiv,
    ← localKernel_card D e L, ← card_eq_card_quotient_mul_card_subgroup]
  exact Nat.card_congr (centralizerInRootEquiv D e L).toEquiv

public theorem quotient_sylow_of_root_sylow [Finite G]
    (S : Sylow 2 (rootCentralizer D e L)) (hs : Nonempty (S ≃* DihedralGroup 4)) :
    ∃ T : Sylow 2 (rootQuotient D e L), Nonempty (T ≃* DihedralGroup 4) := by
  let q := QuotientGroup.mk' (rootKernel D e L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk', rootKernel_card]
    decide
  let T := S.mapSurjective hq
  exact ⟨T, ⟨(Sylow.equivOfSurjectiveCoprime q hq hk S T).symm.trans hs.some⟩⟩

end
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry
