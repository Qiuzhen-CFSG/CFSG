module

public import Theory.Representation.InvertedOddSupportRank
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions

/-!
# The upper bound on the section in the nonquasisimple exclusion

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 8.2.7, printed p.718 (PDF p.735).

For a literal elementary section E/D of O₂(X)U/U, inversion in its action
image gives |E/D| = |[E/D,v]|². The displacement lifts into B = V ∩ O₂(X),
whose image has order at most |B:U|. This proves the dimension bound ten
from the L₃(4) and M₂₂ rows of 8.2.5. The ambient commutator containment is
derived from T-normalization, rather than assumed.

Inversion is required only on the image of the odd subgroup in Aut(E/D).
The book's inversion modulo O₂(H) does not imply literal inversion of an
arbitrary Sylow p-subgroup. The theorem applies to any suitable elementary
section; constructing a section on which the larger containing component
acts is a separate source obligation. None of the statements below asserts
that this section or the replacement offender configuration exists.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type*} [Group G] [finiteG : Finite G]
include finiteG
private theorem image_card_le (E D U B : Subgroup G) [(D.subgroupOf E).Normal]
    (hUD : U ≤ D) :
    Nat.card ((B.subgroupOf E).map (QuotientGroup.mk' (D.subgroupOf E))) ≤ U.relIndex B := by
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  change (D.comap E.subtype).relIndex (B.subgroupOf E) ≤ _
  rw [relIndex_comap, subgroupOf_map_subtype]
  exact (relIndex_le_of_le_left (L := B ⊓ E) hUD (U.subgroupOf (B ⊓ E)).index_ne_zero_of_finite).trans
    (relIndex_le_of_le_right (H := U) inf_le_left (U.subgroupOf B).index_ne_zero_of_finite)

omit finiteG in
private theorem displacement_le_image (J E D B V : Subgroup G)
    [(D.subgroupOf E).Normal]
    [MulDistribMulAction J (E ⧸ D.subgroupOf E)]
    (hJE : J ≤ normalizer (E : Set G))
    (hact : ∀ j : J, ∀ e : E,
      j • (QuotientGroup.mk' (D.subgroupOf E) e) =
        QuotientGroup.mk' (D.subgroupOf E)
          ⟨(j : G) * (e : G) * (j : G)⁻¹,
            (mem_normalizer_iff.mp (hJE j.property) e).mp e.property⟩)
    (hcomm : ⁅E, V⁆ ≤ B) (t : J) (htV : (t : G) ∈ V) :
    commutatorAction (zpowers (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t))
      (E ⧸ D.subgroupOf E) ≤
      (B.subgroupOf E).map (QuotientGroup.mk' (D.subgroupOf E)) := by
  rw [commutatorAction_eq_closure, closure_le]
  rintro _ ⟨a, w, rfl⟩
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf E) w
  let α := MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E)
  obtain ⟨n, hn⟩ := a.property
  let j : J := t ^ n
  have hja : α j = (a : MulAut (E ⧸ D.subgroupOf E)) := by
    exact (map_zpow α t n).trans hn
  have hjV : (j : G) ∈ V := by
    change ((t ^ n : J) : G) ∈ V
    simpa only [Subgroup.coe_zpow] using V.zpow_mem htV n
  let c : E := e⁻¹ * ⟨(j : G) * (e : G) * (j : G)⁻¹,
    (mem_normalizer_iff.mp (hJE j.property) e).mp e.property⟩
  have hc : c ∈ B.subgroupOf E := by
    change (e : G)⁻¹ * ((j : G) * (e : G) * (j : G)⁻¹) ∈ B
    have hm := hcomm (commutator_mem_commutator (E.inv_mem e.property) hjV)
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using hm
  refine ⟨c, hc, ?_⟩
  change QuotientGroup.mk' (D.subgroupOf E) c =
    (QuotientGroup.mk' (D.subgroupOf E) e)⁻¹ *
      (a : MulAut (E ⧸ D.subgroupOf E)) (QuotientGroup.mk' (D.subgroupOf E) e)
  rw [← hja]
  change QuotientGroup.mk' (D.subgroupOf E) c =
    (QuotientGroup.mk' (D.subgroupOf E) e)⁻¹ *
      j • (QuotientGroup.mk' (D.subgroupOf E) e)
  rw [hact, ← map_inv, ← map_mul]

private theorem section_card_bound (J E D U B V : Subgroup G)
    [(D.subgroupOf E).Normal]
    [IsElementaryAbelian 2 (E ⧸ D.subgroupOf E)]
    [MulDistribMulAction J (E ⧸ D.subgroupOf E)]
    (hJE : J ≤ normalizer (E : Set G))
    (hact : ∀ j : J, ∀ e : E,
      j • (QuotientGroup.mk' (D.subgroupOf E) e) =
        QuotientGroup.mk' (D.subgroupOf E)
          ⟨(j : G) * (e : G) * (j : G)⁻¹,
            (mem_normalizer_iff.mp (hJE j.property) e).mp e.property⟩)
    (hUD : U ≤ D) (hcomm : ⁅E, V⁆ ≤ B)
    (Y : Subgroup (MulAut (E ⧸ D.subgroupOf E))) (hodd : Odd (Nat.card Y))
    (t : J)
    (ht : IsInvolution (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t))
    (htV : (t : G) ∈ V)
    (hinv : ∀ y ∈ Y,
      MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t * y *
        (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t)⁻¹ = y⁻¹)
    (hfull : commutatorAction Y (E ⧸ D.subgroupOf E) = ⊤) :
    Nat.card (E ⧸ D.subgroupOf E) ≤ (U.relIndex B) ^ 2 := by
  obtain ⟨hsquare, _, hle⟩ :=
    invertedOddSubgroup_support_card_data (W := E ⧸ D.subgroupOf E) Y hodd
      (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t) ht hinv
  rw [hfull] at hsquare hle
  rw [Subgroup.card_top] at hsquare
  rw [hsquare]
  apply Nat.pow_le_pow_left
  exact (Subgroup.card_le_of_le
    (hle.trans (displacement_le_image J E D B V hJE hact hcomm t htV))).trans
      (image_card_le E D U B hUD)

private theorem section_finrank_bound (J E D U B V : Subgroup G)
    [(D.subgroupOf E).Normal]
    [IsElementaryAbelian 2 (E ⧸ D.subgroupOf E)]
    [IsElementaryAbelian 2 B]
    [MulDistribMulAction J (E ⧸ D.subgroupOf E)]
    (hJE : J ≤ normalizer (E : Set G))
    (hact : ∀ j : J, ∀ e : E,
      j • (QuotientGroup.mk' (D.subgroupOf E) e) =
        QuotientGroup.mk' (D.subgroupOf E)
          ⟨(j : G) * (e : G) * (j : G)⁻¹,
            (mem_normalizer_iff.mp (hJE j.property) e).mp e.property⟩)
    (hUD : U ≤ D) (hcomm : ⁅E, V⁆ ≤ B)
    (Y : Subgroup (MulAut (E ⧸ D.subgroupOf E))) (hodd : Odd (Nat.card Y))
    (t : J)
    (ht : IsInvolution (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t))
    (htV : (t : G) ∈ V)
    (hinv : ∀ y ∈ Y,
      MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t * y *
        (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t)⁻¹ = y⁻¹)
    (hfull : commutatorAction Y (E ⧸ D.subgroupOf E) = ⊤) :
    Module.finrank (ZMod 2) (Additive (E ⧸ D.subgroupOf E)) ≤
      2 * Module.finrank (ZMod 2) (Additive (B ⧸ U.subgroupOf B)) := by
  have hc := section_card_bound J E D U B V hJE hact hUD hcomm Y hodd t ht htV hinv hfull
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (E ⧸ D.subgroupOf E))
  change Nat.card (E ⧸ D.subgroupOf E) = _ at hcard
  rw [hcard, Nat.card_zmod, relIndex_eq_two_pow_quotient_finrank, ← pow_mul] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa only [Nat.mul_comm] using hc)

omit finiteG in
/-- The literal containment [O₂(X)U,V] ≤ O₂(X) ∩ V in 8.2.7. -/
theorem core_product_commutator_le (X U V T : Subgroup G)
    (hTX : T ≤ normalizer (X : Set G))
    (hQT : X.pCoreIn 2 ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hVT : V ≤ T) (hUT : U ≤ T) (hUC : U ≤ centralizer (V : Set G)) :
    ⁅X.pCoreIn 2 ⊔ U, V⁆ ≤ X.pCoreIn 2 ⊓ V := by
  let Q := X.pCoreIn 2
  have hTQ : T ≤ normalizer (Q : Set G) := hTX.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hQV : ⁅Q, V⁆ ≤ Q ⊓ V :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (hVT.trans hTQ))
      (le_normalizer_iff_commutator_le_right.mp (hQT.trans hTV))
  apply commutator_le.mpr
  intro r hr v hv
  have hr' : r ∈ (Q : Set G) * (U : Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left Q U (hUT.trans hTQ)]
  obtain ⟨q, hq, u, hu, rfl⟩ := hr'
  have huv := mem_centralizer_iff.mp (hUC hu) v hv
  have he : ⁅q * u, v⁆ = ⁅q, v⁆ := by
    simp only [commutatorElement_def, mul_inv_rev]
    calc
      q * u * v * (u⁻¹ * q⁻¹) * v⁻¹ = q * (u * v) * u⁻¹ * q⁻¹ * v⁻¹ := by group
      _ = q * (v * u) * u⁻¹ * q⁻¹ * v⁻¹ := by rw [huv]
      _ = q * v * q⁻¹ * v⁻¹ := by group
  rw [he]
  exact hQV (commutator_mem_commutator hq hv)

/-- Every elementary section of O₂(X)U/U with full odd support inverted by
an element of V has dimension at most ten. The five-dimensional bound is
on the earlier table's B/U, not on the section being bounded. -/
theorem section_finrank_le_ten (X U V T J E D : Subgroup G)
    [(D.subgroupOf E).Normal]
    [IsElementaryAbelian 2 (V ⊓ X.pCoreIn 2 : Subgroup G)]
    [IsElementaryAbelian 2 (E ⧸ D.subgroupOf E)]
    [MulDistribMulAction J (E ⧸ D.subgroupOf E)]
    (hTX : T ≤ normalizer (X : Set G))
    (hQT : X.pCoreIn 2 ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hVT : V ≤ T) (hUT : U ≤ T) (hUC : U ≤ centralizer (V : Set G))
    (hER : E ≤ X.pCoreIn 2 ⊔ U) (hUD : U ≤ D)
    (hJE : J ≤ normalizer (E : Set G))
    (hact : ∀ j : J, ∀ e : E,
      j • (QuotientGroup.mk' (D.subgroupOf E) e) =
        QuotientGroup.mk' (D.subgroupOf E)
          ⟨(j : G) * (e : G) * (j : G)⁻¹,
            (mem_normalizer_iff.mp (hJE j.property) e).mp e.property⟩)
    (Y : Subgroup (MulAut (E ⧸ D.subgroupOf E))) (hodd : Odd (Nat.card Y))
    (t : J)
    (ht : IsInvolution (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t))
    (htV : (t : G) ∈ V)
    (hinv : ∀ y ∈ Y,
      MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t * y *
        (MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) t)⁻¹ = y⁻¹)
    (hfull : commutatorAction Y (E ⧸ D.subgroupOf E) = ⊤)
    (hrow : Module.finrank (ZMod 2)
      (Additive ((V ⊓ X.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ X.pCoreIn 2))) ≤ 5) :
    Module.finrank (ZMod 2) (Additive (E ⧸ D.subgroupOf E)) ≤ 10 := by
  have hcomm : ⁅E, V⁆ ≤ V ⊓ X.pCoreIn 2 := by
    rw [inf_comm]
    exact (commutator_mono hER le_rfl).trans
      (core_product_commutator_le X U V T hTX hQT hTV hVT hUT hUC)
  have hd := section_finrank_bound J E D U (V ⊓ X.pCoreIn 2) V
    hJE hact hUD hcomm Y hodd t ht htV hinv hfull
  omega

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
