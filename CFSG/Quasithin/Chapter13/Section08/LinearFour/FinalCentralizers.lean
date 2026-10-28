module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# The final centralizer calculation in the L₄(2) branch

These are the group and cardinality arguments on printed pp.965–966 in
the proof of Aschbacher–Smith 13.8.28 (*The Classification of Quasithin
Groups*, combined manuscript, 1 March 2004).

The index-four parabolic bound and the index-four duality calculation
force `C_{Q_H}(V₃) = Q ∩ Q_H`. Thus `H_C ≤ Q`; normality inside `H`
propagates centralization of `V` to its `H`-conjugate span `V_H`. Using
`A₁ ≤ V_H` places `H_C` in the vertex stabilizer of `γ`, which normalizes
`Uγ`. The commutator therefore lies in `H_C ∩ Uγ`. Finally, the orders
`|Uγ| = 32`, `|Uγ : Uγ ∩ Q_H| = 2` and `|Uγ ∩ V_H| ≥ 8` bound its
image in the literal quotient `H_C/V_H` by two.

All normality hypotheses are relative to the indicated local groups.
The source's order-four assertion is about the image of `O₂(L₁T)`
modulo `Q`, not the order of `O₂(L₁T)` itself. The model calculation
giving that index, duality from 13.7.4, and 13.8.32 remain explicit
inputs. These lemmas do not supply the chief-factor count or G.6.4.
-/

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

open Subgroup

variable {G : Type*} [Group G]

private theorem centralizes_span (H C V : Subgroup G)
    (hHC : H ≤ normalizer (C : Set G))
    (hCV : C ≤ centralizer (V : Set G)) :
    C ≤ centralizer (conjugateSpanBy V H : Set G) := by
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro _ ⟨h, hh, v, hv, rfl⟩
  intro c hc
  have hc' : h⁻¹ * c * h ∈ C := by
    simpa using le_normalizer_iff.mp hHC h⁻¹ (H.inv_mem hh) c hc
  have he := congrArg (fun z : G => h * z * h⁻¹) (hCV hc' v hv)
  simpa [mul_assoc] using he.symm

/-- The two index-four calculations force the actual centralizer equality.
In the source `R = O₂(L₁T)`, with `[R : Q] = 4`. -/
public theorem centralizer_eq_core_intersection
    [Finite G] (Q QH V3 R : Subgroup G)
    (hQR : QH ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ QH ≤ centralizer (V3 : Set G))
    (hdual : (QH ⊓ centralizer (V3 : Set G)).relIndex QH = 4) :
    QH ⊓ centralizer (V3 : Set G) = Q ⊓ QH := by
  let C := QH ⊓ centralizer (V3 : Set G)
  have hIC : Q ⊓ QH ≤ C := le_inf inf_le_right hcent
  have hi : (Q ⊓ QH).relIndex QH ≤ 4 := by
    rw [inf_relIndex_right]
    simpa only [hindex] using relIndex_le_of_le_right (H := Q) hQR
      (show Q.relIndex R ≠ 0 by omega)
  have hm := relIndex_mul_relIndex (Q ⊓ QH) C QH hIC inf_le_left
  rw [show C.relIndex QH = 4 from hdual] at hm
  have hn : (Q ⊓ QH).relIndex C ≠ 0 :=
    ((Q ⊓ QH).subgroupOf C).index_ne_zero_of_finite
  have hone : (Q ⊓ QH).relIndex C = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp hone) hIC

/-- The chain on pp.965–966: the local centralizer lies in `Q`, centralizes
the generated `V_H`, and normalizes `Uγ`. Its commutator with `Uγ` lies in
their intersection. The earlier local results and 13.8.32(3) are inputs. -/
public theorem final_centralizer_chain
    [Finite G] (H Q QH HC V3 V VH R A1 Uγ Gγ : Subgroup G)
    (hQR : QH ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ QH ≤ centralizer (V3 : Set G))
    (hdual : (QH ⊓ centralizer (V3 : Set G)).relIndex QH = 4)
    (hHCQH : HC ≤ QH) (hHCV3 : HC ≤ centralizer (V3 : Set G))
    (hHHC : H ≤ normalizer (HC : Set G))
    (hQV : Q ≤ centralizer (V : Set G))
    (hVH : VH = conjugateSpanBy V H) (hA1 : A1 ≤ VH)
    (hGγ : Gγ = centralizer (A1 : Set G))
    (hGγUγ : Gγ ≤ normalizer (Uγ : Set G)) (hUγH : Uγ ≤ H) :
    HC ≤ Q ∧ HC ≤ centralizer (VH : Set G) ∧ HC ≤ Gγ ∧
      ⁅HC, Uγ⁆ ≤ HC ⊓ Uγ := by
  have heq := centralizer_eq_core_intersection Q QH V3 R hQR hindex hcent hdual
  have hHCQ : HC ≤ Q := by
    have h := le_inf hHCQH hHCV3
    rw [heq] at h
    exact h.trans inf_le_left
  have hHCVH : HC ≤ centralizer (VH : Set G) := by
    rw [hVH]
    exact centralizes_span H HC V hHHC (hHCQ.trans hQV)
  have hHCGγ : HC ≤ Gγ := by
    rw [hGγ]
    exact hHCVH.trans (centralizer_le hA1)
  refine ⟨hHCQ, hHCVH, hHCGγ, le_inf ?_ ?_⟩
  · exact le_normalizer_iff_commutator_le_left.mp (hUγH.trans hHHC)
  · exact le_normalizer_iff_commutator_le_right.mp (hHCGγ.trans hGγUγ)

/-- The intersection quotient in the final paragraph has order at most two,
using the full order of `Uγ` and its index-two intersection with `Q_H`.
No assertion about a chief-factor count is assumed. -/
public theorem intersection_section_index_le_two
    [Finite G] (U C V Q : Subgroup G) (hVC : V ≤ C) (hCQ : C ≤ Q)
    (hU : Nat.card U = 32) (hstar : Q.relIndex U = 2)
    (hintersection : 8 ≤ Nat.card (U ⊓ V : Subgroup G)) :
    V.relIndex (U ⊓ C) ≤ 2 := by
  have hcardQ := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ Q) U bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hU, hstar] at hcardQ
  have hcardC : Nat.card (U ⊓ C : Subgroup G) ≤ Nat.card (U ⊓ Q : Subgroup G) :=
    Nat.card_le_card_of_injective (inclusion (inf_le_inf_left U hCQ))
      (inclusion_injective _)
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) (U ⊓ C)
    bot_le (inf_le_inf_left U hVC)
  rw [relIndex_bot_left, relIndex_bot_left] at hcard
  have he : V.relIndex (U ⊓ C) = (U ⊓ V).relIndex (U ⊓ C) := by
    rw [← inf_relIndex_right V (U ⊓ C), ← inf_relIndex_right (U ⊓ V) (U ⊓ C)]
    congr 1
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_right.trans inf_le_left) inf_le_left) inf_le_right
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  rw [he]
  nlinarith

/-- The image of the actual intersection in the actual quotient `C/V`
has order at most two. Normality is required only in `C`. -/
public theorem intersection_quotient_image_card_le_two
    [Finite G] (U C V Q : Subgroup G) [(V.subgroupOf C).Normal]
    (hVC : V ≤ C) (hCQ : C ≤ Q)
    (hU : Nat.card U = 32) (hstar : Q.relIndex U = 2)
    (hintersection : 8 ≤ Nat.card (U ⊓ V : Subgroup G)) :
    Nat.card ((U.subgroupOf C).map (QuotientGroup.mk' (V.subgroupOf C))) ≤ 2 := by
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  change (V.comap C.subtype).relIndex (U.subgroupOf C) ≤ 2
  rw [relIndex_comap, subgroupOf_map_subtype]
  exact intersection_section_index_le_two U C V Q hVC hCQ hU hstar hintersection

/-- The preceding bound applies to the commutator image when the two local
subgroups normalize each other, as established by `final_centralizer_chain`. -/
public theorem commutator_quotient_image_card_le_two
    [Finite G] (U C V Q : Subgroup G) [(V.subgroupOf C).Normal]
    (hVC : V ≤ C) (hCQ : C ≤ Q)
    (hU : Nat.card U = 32) (hstar : Q.relIndex U = 2)
    (hintersection : 8 ≤ Nat.card (U ⊓ V : Subgroup G))
    (hcomm : ⁅C, U⁆ ≤ C ⊓ U) :
    Nat.card ((⁅C, U⁆.subgroupOf C).map (QuotientGroup.mk' (V.subgroupOf C))) ≤ 2 := by
  have hle : (⁅C, U⁆.subgroupOf C).map (QuotientGroup.mk' (V.subgroupOf C)) ≤
      (U.subgroupOf C).map (QuotientGroup.mk' (V.subgroupOf C)) :=
    map_mono (subgroupOf_mono C (hcomm.trans inf_le_right))
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)).trans
    (intersection_quotient_image_card_le_two U C V Q hVC hCQ hU hstar hintersection)

end CFSG.Quasithin.Chapter13.Section08.LinearFour
