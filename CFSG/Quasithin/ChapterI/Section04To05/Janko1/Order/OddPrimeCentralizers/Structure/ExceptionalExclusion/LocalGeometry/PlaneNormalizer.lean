module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry.Products
public import Theory.GroupTheory.CubicPlaneNormalizer

/-!
# The literal plane normalizer in the exceptional order-27 configuration

Under the explicit fixed-subgroup order |C_A(X)|=3, the subgroup
Z=N_G(A) intersect N_G(C_A(X)X) is nonabelian of order 27.

First AX is self-normalizing inside N_G(A): the normalizer congruence
allows only orders 81 and 324. The latter would make AX normal, forcing
X to centralize V, contrary to the four-group centralizer order. An element
normalizing both A and Y also normalizes AY=AX, so the literal Z equals
N_AX(Y). The general cubic-extension calculation then gives both conclusions.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225. The fixed-subgroup order is an explicit premise here; its
unconditional producer and final source assembly belong to LocalGeometry.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem extension_self_normalizer (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X)) :
    normalizer (A : Set G) ⊓ normalizer ((A ⊔ X : Subgroup G) : Set G) = A ⊔ X := by
  let N := normalizer (A : Set G)
  let S := A ⊔ X
  let R := N ⊓ normalizer (S : Set G)
  have hXN : X ≤ N := by rw [show N = A ⊔ (V ⊔ X) from hN]; exact le_sup_of_le_right le_sup_right
  have hVN : V ≤ N := by rw [show N = A ⊔ (V ⊔ X) from hN]; exact le_sup_of_le_right le_sup_left
  have hSN : S ≤ N := sup_le A.le_normalizer hXN
  have hSR : S ≤ R := le_inf hSN S.le_normalizer
  have hSc : Nat.card S = 81 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A X hXN
      ((h.exceptional_complement_disjoint A V X e.card hV hXV hN).mono_right le_sup_right), e.card, hX]
  have hNc : Nat.card N = 324 := h.exceptional_normalizer_card A e
  have hmap : (normalizer (S.subgroupOf N : Set N)).map N.subtype = R := by
    rw [← subgroupOf_normalizer_eq hSN, subgroupOf_map_subtype, inf_comm]
  have hRc : Nat.card R = Nat.card (normalizer (S.subgroupOf N : Set N)) := by
    rw [← hmap, card_map_of_injective N.subtype_injective]
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hSc' : Nat.card (S.subgroupOf N) = 3 ^ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv, hSc]
    norm_num
  have hcongr := Sylow.card_normalizer_modEq_card (p := 3) (n := 4) hSc'
  rw [← hRc, hNc] at hcongr
  have hlower := card_le_of_le hSR
  have hupper := card_le_of_le (show R ≤ N from inf_le_left)
  rw [hSc] at hlower
  rw [hNc] at hupper
  have halt : Nat.card R = 81 ∨ Nat.card R = 324 := by
    change Nat.card R % 243 = 324 % 243 at hcongr
    omega
  have hcard : Nat.card R = 81 := by
    rcases halt with hc | hc
    · exact hc
    · have hRN : R = N := eq_of_le_of_card_ge inf_le_left (by rw [hc, hNc])
      have hVS : V ≤ normalizer (S : Set G) := hVN.trans (hRN.symm.le.trans inf_le_right)
      have hd : Disjoint V S := disjoint_of_coprime_natCard (by rw [hV, hSc]; decide)
      have hcomm : ⁅X, V⁆ = ⊥ := by
        apply eq_bot_iff.mpr
        apply hd.le_bot.trans'
        exact le_inf (le_normalizer_iff_commutator_le_right.mp hXV)
          ((commutator_mono (show X ≤ S from le_sup_right) le_rfl).trans
            (le_normalizer_iff_commutator_le_left.mp hVS))
      exact (h.exceptional_actor_not_centralizes_four V X hV hX
        (commutator_eq_bot_iff_le_centralizer.mp hcomm)).elim
  exact (eq_of_le_of_card_ge hSR (by rw [hcard, hSc])).symm

private theorem plane_normalizer_eq_extension_normalizer (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X)) :
    exceptionalPlaneNormalizer A X = (A ⊔ X) ⊓ normalizer (exceptionalPlane A X : Set G) := by
  have hSN : A ⊔ X ≤ normalizer (A : Set G) := by
    rw [hN]
    exact sup_le le_sup_left (le_sup_of_le_right le_sup_right)
  have hAY : A ⊔ exceptionalPlane A X = A ⊔ X := by
    rw [exceptionalPlane, ← sup_assoc, sup_of_le_left (show A ⊓ centralizer (X : Set G) ≤ A from inf_le_left)]
  have hn : exceptionalPlaneNormalizer A X ≤ normalizer ((A ⊔ X : Subgroup G) : Set G) := by
    rw [← hAY]
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
  have hZ : exceptionalPlaneNormalizer A X ≤ A ⊔ X := by
    rw [← extension_self_normalizer h A e V X hV hX hXV hN]
    exact le_inf inf_le_left hn
  exact le_antisymm (le_inf hZ inf_le_right) (inf_le_inf_right _ hSN)
/-- The actual relative plane normalizer has order 27 and is nonabelian.
The only extra premise beyond the exceptional decomposition is the order
of the literal fixed subgroup C_A(X). -/
public theorem exceptional_plane_normalizer_card_nonabelian_of_fixed_card
    (h : Janko1CentralizerData G) (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X))
    (hfixed : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3) :
    Nat.card (exceptionalPlaneNormalizer A X) = 27 ∧
      ¬ IsMulCommutative (exceptionalPlaneNormalizer A X) := by
  rw [plane_normalizer_eq_extension_normalizer h A e V X hV hX hXV hN]
  have hXA : X ≤ normalizer (A : Set G) := by
    rw [hN]
    exact le_sup_of_le_right le_sup_right
  exact cubic_plane_normalizer_card_nonabelian A X e.card hX hXA
    ((h.exceptional_complement_disjoint A V X e.card hV hXV hN).mono_right le_sup_right)
    hfixed

end CFSG.Quasithin.Janko1CentralizerData
