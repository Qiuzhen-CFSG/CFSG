module

public import CFSG.Quasithin.ChapterJ.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections

/-!
# The literal dual module Q/HC in J.2.2(3)

F.9.7 pairs Q/C_Q(U) with the binary dual of U/C_U(Q) inside H.
The established equality C_U(Q)=Z and the Ru2 coordinate map identify
its second argument with the actual natural module U/Z. Transporting the
pairing gives a surjective coordinate map on Q with kernel HC. Simultaneous
conjugation invariance proves equivariance for the contragredient action
through the original H/Q quotient map. In particular |HC/U|=4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3), printed p.432 (PDF p.443), using F.9.7, printed p.321.
The printed U/HC in the proof is Q/HC.
-/

@[expose] public section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

/-- F.9.7 transported through the given U/Z coordinates, with its literal kernel. -/
theorem LocalSetup.exists_dualSection (d : LocalSetup G) :
    Nonempty (BinaryConjugationSection d.toTypeRuSetup.H d.toTypeRuSetup.Q
      d.toTypeRuSetup.HC (d.ru2.naturalAction.action.dual.comp d.ru2.quotientMap)) := by
  let QH := d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.H
  let UH := d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H
  let ZH := d.toTypeRuSetup.Z.subgroupOf d.toTypeRuSetup.H
  have hUH := d.ru2.natural.section_le
  have hQH := pCoreIn_le 2 d.toTypeRuSetup.H
  have hZH := d.ru2.natural.kernel_le.trans hUH
  let : QH.Normal :=
    (normal_subgroupOf_iff_le_normalizer hQH).mpr d.ru2.six.normalized
  let : UH.Normal :=
    (normal_subgroupOf_iff_le_normalizer hUH).mpr d.ru2.natural.normalized
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  let : IsElementaryAbelian 2 UH := IsElementaryAbelian.subgroupOf hUH
  have hZQ : ZH ≤ QH := fun z hz =>
    d.ru2.six.kernel_le (d.ru2.natural.kernel_le hz)
  have hZcentral : ZH ≤ center d.toTypeRuSetup.H := by
    intro z hz
    apply mem_center_iff.mpr
    intro h
    exact Subtype.ext ((h.property z hz).symm)
  have hcomm : ⁅QH, UH⁆ ≤ ZH := by
    apply commutator_le.mpr
    intro q hq u hu
    exact d.toTypeRuSetup.commutator_Q_U_le_Z (commutator_mem_commutator hq hu)
  have hcard : Nat.card ZH = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv]
    exact d.card_Z
  obtain ⟨eZ, e, _he, hinv⟩ := ChapterF.lemma_F_9_7 QH UH ZH hZQ hZcentral hcomm hcard
  let eU : UH ≃* d.toTypeRuSetup.U := subgroupOfEquivOfLe hUH
  let eQ : QH ≃* d.toTypeRuSetup.Q := subgroupOfEquivOfLe hQH
  let N := (centralizer (QH : Set d.toTypeRuSetup.H)).subgroupOf UH
  let M := (centralizer (UH : Set d.toTypeRuSetup.H)).subgroupOf QH
  let f : UH →* Multiplicative FourSpace := d.ru2.natural.coordinates.comp eU.toMonoidHom
  have hf : f.ker = N := by
    ext u
    change d.ru2.natural.coordinates (eU u) = 1 ↔ _
    rw [d.ru2.natural.coordinates_eq_one_iff]
    change (eU u : G) ∈ d.toTypeRuSetup.Z ↔ _
    rw [← d.centralizer_Q_inf_U]
    constructor
    · intro hu q hq
      exact Subtype.ext (hu.2 q hq)
    · intro hu
      refine ⟨u.property, ?_⟩
      intro q hq
      exact congrArg Subtype.val (hu ⟨q, hQH hq⟩ hq)
  have honto : Function.Surjective f := d.ru2.natural.onto.comp eU.surjective
  let eW : (UH ⧸ N) ≃* Multiplicative FourSpace :=
    (QuotientGroup.quotientMulEquivOfEq hf.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f honto)
  let lW : Additive (UH ⧸ N) ≃ₗ[ZMod 2] FourSpace :=
    LinearEquiv.ofBijective (eW.toAdditiveLeft.toAddMonoidHom.toZModLinearMap 2)
      eW.toAdditiveLeft.bijective
  have hlW (u : UH) : lW (Additive.ofMul (QuotientGroup.mk' N u)) =
      (d.ru2.natural.coordinates (eU u)).toAdd := rfl
  let t : Multiplicative (Module.Dual (ZMod 2) (Additive (UH ⧸ N))) ≃*
      Multiplicative (Module.Dual (ZMod 2) FourSpace) :=
    lW.symm.dualMap.toAddEquiv.toMultiplicative
  let c : d.toTypeRuSetup.Q →* Multiplicative (Module.Dual (ZMod 2) FourSpace) :=
    t.toMonoidHom.comp (e.toMonoidHom.comp ((QuotientGroup.mk' M).comp eQ.symm.toMonoidHom))
  have hc (q : QH) (u : UH) :
      (c (eQ q)).toAdd (d.ru2.natural.coordinates (eU u)).toAdd =
      (e (QuotientGroup.mk' M q)).toAdd (Additive.ofMul (QuotientGroup.mk' N u)) := by
    change (e (QuotientGroup.mk' M (eQ.symm (eQ q)))).toAdd
      (lW.symm (d.ru2.natural.coordinates (eU u)).toAdd) = _
    rw [eQ.symm_apply_apply, ← hlW, lW.symm_apply_apply]
  refine ⟨{
    section_le := hQH
    kernel_le := d.toTypeRuSetup.HC_le_Q
    normalized := d.ru2.six.normalized
    coordinates := c
    onto := t.surjective.comp (e.surjective.comp ((QuotientGroup.mk'_surjective M).comp eQ.symm.surjective))
    kernel_eq := ?_
    equivariant := ?_ }⟩
  · ext q
    change c q = 1 ↔ _
    have hc1 : c q = 1 ↔ eQ.symm q ∈ M := by
      change t (e (QuotientGroup.mk' M (eQ.symm q))) = 1 ↔ _
      rw [← t.map_one, t.injective.eq_iff, ← e.map_one, e.injective.eq_iff,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hc1]
    constructor
    · intro h
      refine ⟨hQH q.property, ?_⟩
      intro u hu
      exact congrArg Subtype.val (h ⟨u, hUH hu⟩ hu)
    · intro h u hu
      exact Subtype.ext (h.2 u hu)
  · intro h q
    apply LinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := honto (Multiplicative.ofAdd
      (d.ru2.naturalAction.action (d.ru2.quotientMap h⁻¹) v))
    let qH := eQ.symm q
    let q' : QH := ⟨h * qH * h⁻¹, (inferInstance : QH.Normal).conj_mem qH qH.property h⟩
    let u' : UH := ⟨h * u * h⁻¹, (inferInstance : UH.Normal).conj_mem u u.property h⟩
    have hu' : (d.ru2.natural.coordinates (eU u')).toAdd = v := by
      have hh := d.ru2.natural.equivariant h (eU u)
      change (d.ru2.natural.coordinates (eU u')).toAdd = _ at hh
      rw [show (d.ru2.natural.coordinates (eU u)).toAdd =
        d.ru2.naturalAction.action (d.ru2.quotientMap h⁻¹) v from
          congrArg Multiplicative.toAdd hu] at hh
      simpa only [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul,
        mul_inv_cancel, map_one, Module.End.one_apply] using hh
    change (c (eQ q')).toAdd v =
      (c (eQ qH)).toAdd (d.ru2.naturalAction.action ((d.ru2.quotientMap h)⁻¹) v)
    have hu0 : (d.ru2.natural.coordinates (eU u)).toAdd =
        d.ru2.naturalAction.action ((d.ru2.quotientMap h)⁻¹) v := by
      have hh := congrArg Multiplicative.toAdd hu
      change (d.ru2.natural.coordinates (eU u)).toAdd =
        d.ru2.naturalAction.action (d.ru2.quotientMap h⁻¹) v at hh
      rwa [map_inv] at hh
    rw [← hu0]
    conv_lhs => rw [← hu']
    rw [hc, hc]
    exact hinv h qH u

/-- The H-equivariant dual-natural coordinates on the actual quotient Q/HC. -/
def LocalSetup.dualSection (d : LocalSetup G) :
    BinaryConjugationSection d.toTypeRuSetup.H d.toTypeRuSetup.Q
      d.toTypeRuSetup.HC (d.ru2.naturalAction.action.dual.comp d.ru2.quotientMap) :=
  Classical.choice (d.exists_dualSection)

/-- The centralizer has order 128, as follows from the perfect commutator pairing. -/
theorem LocalSetup.card_HC (d : LocalSetup G) : Nat.card d.toTypeRuSetup.HC = 128 := by
  have h := d.dualSection.card_section
  have hd : Nat.card (Module.Dual (ZMod 2) FourSpace) = 16 := by
    rw [← Nat.card_congr (Module.finBasis (ZMod 2) FourSpace).toDualEquiv.toEquiv]
    exact (Nat.card_eq_fintype_card).trans SL2FourNatural.card_vector
  rw [hd, d.ru2.card_Q d.card_Z] at h
  omega

/-- The actual section HC/U is a binary plane. -/
theorem LocalSetup.card_HC_quotient_U (d : LocalSetup G) :
    Nat.card (d.toTypeRuSetup.HC ⧸ d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.HC) = 4 := by
  have h := card_eq_card_quotient_mul_card_subgroup
    (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.HC)
  rw [Nat.card_congr (subgroupOfEquivOfLe d.U_le_HC).toEquiv,
    d.card_HC, d.ru2.card_U d.card_Z] at h
  omega

end CFSG.Quasithin.ChapterJ
