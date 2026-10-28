module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.Commutator
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.Marking
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.PrimeRankZero

/-!
# The cubic rank deduction in the four-space branch

Let `I` be the actual section in case (3a), so that `I/O₂(I)` is the
literal symmetric group on three letters.  The containing component commutes
with `I` modulo its two-core.  In the relative join `H = K ⊔ I`, the two
cores generate a normal two-subgroup of `H`; after quotienting by `O₂(H)`,
the images of `K` and `I` are disjoint commuting subgroups.  Their prime
ranks therefore add.  The SQTK bound gives rank at most two for `H`, while
the symmetric-three image has rank exactly one, forcing the cubic rank of
`K` to be at most one.

Source: Aschbacher--Smith, proof of Proposition 8.2.8(1), printed p.719
(PDF p.736).  The hypotheses retain the literal centralizer section and the
actual quotient `I/O₂(I)`, rather than replacing them by an abstract action
kernel or an arbitrary quotient-rank assertion.
-/

public section
open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection

variable {G : Type*} [Group G] [Finite G]

local notation "S3" => Equiv.Perm (Fin 3)

private theorem symmetricThree_primeRank_ne_zero : primeRank 3 S3 ≠ 0 := by
  intro hz
  apply (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

/-- The component and the actual S₃-section have cubic rank at most two in
    their relative join, with the component contributing at most one. -/
theorem containingComponent_threeRank_le_one
    (C : CFSG.Quasithin.GroupClass) (L K U I : Subgroup G)
    [Group.IsPerfect K]
    [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hSQTK : IsSQTK C (normalizer (U : Set G)))
    (hRK : localResidual L U ≤ K)
    (hKU : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hnontriv : ¬ localResidual L U ≤ centralizer (U : Set G))
    (hIC : I ≤ centralizer (U : Set G))
    (eI : (I ⧸ pCore 2 I) ≃* S3) :
    primeRank 3 K ≤ 1 := by
  let H := K ⊔ I
  let KH : Subgroup H := K.subgroupOf H
  let IH : Subgroup H := I.subgroupOf H
  let QK := K.pCoreIn 2
  let QI := I.pCoreIn 2
  let P := QK ⊔ QI
  have hIN : I ≤ normalizer (K : Set G) :=
    hIC.trans (centralizer_le_normalizer _)
      |>.trans hNK
  have hKQK : K ≤ normalizer (QK : Set G) :=
    K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hIQK : I ≤ normalizer (QK : Set G) :=
    hIN.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hIQI : I ≤ normalizer (QI : Set G) :=
    I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hKNP : K ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk x hx
    have hQK : QK.map (MulAut.conj k).toMonoidHom ≤ P := by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_sup_left ((mem_normalizer_iff.mp (hKQK hk) y).mp hy)
    have hQI : QI.map (MulAut.conj k).toMonoidHom ≤ P := by
      rintro _ ⟨i, hi, rfl⟩
      have hm := P.mul_mem
        (mem_sup_left (containingComponent_commutator L K U I hRK hKU hNK hnontriv hIC
          (commutator_mem_commutator hk (pCoreIn_le 2 I hi))))
        (mem_sup_right hi)
      change k * i * k⁻¹ ∈ P
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm
    have hm : P.map (MulAut.conj k).toMonoidHom ≤ P := by
      rw [Subgroup.map_sup]
      exact sup_le hQK hQI
    exact hm (mem_map_of_mem _ hx)
  have hINP : I ≤ normalizer (P : Set G) :=
    (le_inf hIQK hIQI).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hHP : H ≤ normalizer (P : Set G) := sup_le hKNP hINP
  have hPtwo : IsPGroup 2 P :=
    (isPGroup_pCoreIn 2 K).to_sup_of_normal_left'
      (isPGroup_pCoreIn 2 I) ((pCoreIn_le 2 I).trans hIQK)
  have hPHcore : P.subgroupOf H ≤ pCore 2 H := by
    let : (P.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHP
    exact le_sSup ⟨inferInstance, hPtwo.comap_subtype⟩
  have hQKH : QK.subgroupOf H ≤ pCore 2 H :=
    (subgroupOf_mono _ (show QK ≤ P from le_sup_left)).trans hPHcore
  have hQIH : QI.subgroupOf H ≤ pCore 2 H :=
    (subgroupOf_mono _ (show QI ≤ P from le_sup_right)).trans hPHcore
  have hQKG : QK ≤ (pCore 2 H).map H.subtype := by
    rw [← map_subgroupOf_eq_of_le (show QK ≤ H from (pCoreIn_le 2 K).trans le_sup_left)]
    exact map_mono hQKH
  have hcommG : ⁅K, I⁆ ≤ QK :=
    containingComponent_commutator L K U I hRK hKU hNK hnontriv hIC
  have hcommH : ⁅KH, IH⁆ ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show I ≤ H from le_sup_right)]
    exact hcommG.trans hQKG

  let q := QuotientGroup.mk' (pCore 2 H)
  let Kbar := KH.map q
  let Ibar := IH.map q
  have hcentral : Kbar ≤ centralizer (Ibar : Set (H ⧸ pCore 2 H)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcommH
  have hkerI : (q.subgroupMap IH).ker = pCore 2 IH := by
    apply le_antisymm
    · rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
      let : ((pCore 2 H).subgroupOf IH).Normal := inferInstance
      exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    · rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
      intro x hx
      have hmap : (pCore 2 IH).map IH.subtype = QI.subgroupOf H := by
        apply map_injective H.subtype_injective
        rw [map_subgroupOf_eq_of_le (show QI ≤ H from (pCoreIn_le 2 I).trans le_sup_right)]
        rw [map_map]
        change (pCore 2 IH).map (H.subtype.comp IH.subtype) = I.pCoreIn 2
        have he : H.subtype.comp IH.subtype = I.subtype.comp
            (subgroupOfEquivOfLe (show I ≤ H from le_sup_right)).toMonoidHom := by rfl
        rw [he, ← map_map, pCore_map_iso]
        rfl
      have hxQ : (IH.subtype x : H) ∈ QI.subgroupOf H := by
        rw [← hmap]
        exact ⟨x, hx, rfl⟩
      exact hQIH hxQ
  let eIH : (IH ⧸ pCore 2 IH) ≃* (I ⧸ pCore 2 I) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show I ≤ H from le_sup_right))
      (pCore_map_iso 2 (subgroupOfEquivOfLe (show I ≤ H from le_sup_right)))
  let eIbar : Ibar ≃* S3 :=
    (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap IH)
      (q.subgroupMap_surjective IH)).symm
      |>.trans (QuotientGroup.quotientMulEquivOfEq hkerI)
      |>.trans eIH
      |>.trans eI
  have hdis : Disjoint Kbar Ibar := by
    apply disjoint_def.mpr
    intro x hxK hxI
    have hxi : (⟨x, hxI⟩ : Ibar) = 1 := by
      apply eIbar.injective
      rw [map_one]
      apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
      intro y
      obtain ⟨y, rfl⟩ := eIbar.surjective y
      have he : y * (⟨x, hxI⟩ : Ibar) = ⟨x, hxI⟩ * y :=
        Subtype.ext (hcentral hxK y y.property)
      simpa only [map_mul] using congrArg eIbar he
    exact congrArg Subtype.val hxi
  have hC : H ≤ normalizer (U : Set G) :=
    sup_le hKU (hIC.trans (centralizer_le_normalizer _))
  have hrankH : primeRank 3 H ≤ 2 := by
    apply (primeRank_mono 3 hC).trans
    exact hSQTK.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hrankQ : primeRank 3 (H ⧸ pCore 2 H) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hrankH
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hrankKbar : primeRank 3 Kbar = primeRank 3 K := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel
      (by decide) q hq KH]
    exact primeRank_congr 3 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
  have hsum := Subgroup.primeRank_sup_eq_add_of_disjoint_commuting Kbar Ibar hdis hcentral 3
  have hjoin : primeRank 3 (Kbar ⊔ Ibar : Subgroup _) ≤ 2 :=
    (primeRank_subgroup_le 3 _).trans hrankQ
  have hIpos : 1 ≤ primeRank 3 Ibar := by
    rw [primeRank_congr 3 eIbar]
    exact Nat.pos_of_ne_zero symmetricThree_primeRank_ne_zero
  rw [hsum, hrankKbar] at hjoin
  omega

/-- The cubic bound in the form consumed by the marked action argument. -/
theorem actionImage_threeRank_le_one_of_commuting_s3
    (C : CFSG.Quasithin.GroupClass) (L K U I : Subgroup G)
    [Group.IsPerfect K]
    [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hSQTK : IsSQTK C (normalizer (U : Set G)))
    (hRK : localResidual L U ≤ K)
    (hKU : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hnontriv : ¬ localResidual L U ≤ centralizer (U : Set G))
    (hIC : I ≤ centralizer (U : Set G))
    (eI : (I ⧸ pCore 2 I) ≃* S3) :
    primeRank 3 (SmallOvergroups.actionImage K U) ≤ 1 :=
  actionImage_threeRank_le_one K U hKU
    (containingComponent_threeRank_le_one C L K U I hSQTK hRK hKU hNK hnontriv hIC eI)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection
