module
public import Theory.GroupTheory.SylowThreeNormalizerSection
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.IndexNormal

/-!
# Frattini counting for the source cubic normalizer

For the actual endpoint orders, AX has index two and is normal. Frattini's
argument gives G=A N_G(X). Coprime subgroup orders identify N_A(X) with
C_A(X), so eight fixed elements give normalizer order48. This is used by
J.4.5 on the literal selected source cubic and its unchanged core.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3):=⟨by decide⟩

theorem cubic_normalizer_supplement_of_orders (A P:Subgroup G) [A.Normal]
    (hG:Nat.card G=12288) (hA:Nat.card A=2048) (hP:Nat.card P=3) :
    A⊔normalizer (P:Set G)=⊤ := by
  have hp:IsPGroup 3 P:=IsPGroup.of_card (show Nat.card P=3^1 from hP)
  have hpi:P.index=4096:=by
    have hh:=P.card_mul_index
    rw [hG,hP] at hh
    omega
  let X:Sylow 3 G:=hp.toSylow (by rw [hpi];decide)
  have ha:IsPGroup 2 A:=IsPGroup.of_card (show Nat.card A=2^11 from hA)
  have hd:Disjoint A P:=IsPGroup.disjoint_of_ne 2 3 (by decide) A P ha hp
  have hn:P≤normalizer (A:Set G):=by rw [A.normalizer_eq_top];exact le_top
  have hB:Nat.card (A⊔P:Subgroup G)=6144:=by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A P hn hd,hA,hP]
  have hi:(A⊔P:Subgroup G).index=2:=by
    have hh:=(A⊔P:Subgroup G).card_mul_index
    rw [hB,hG] at hh
    omega
  let :(A⊔P:Subgroup G).Normal:=normal_of_index_eq_two hi
  have hh:=X.normalizer_sup_eq_top' (show (X:Subgroup G)≤A⊔P from le_sup_right)
  change normalizer (P:Set G)⊔(A⊔P)=⊤ at hh
  rw [sup_left_comm,sup_eq_left.mpr P.le_normalizer] at hh
  exact hh

theorem cubic_normalizer_card_of_fixed_eight (A P:Subgroup G) [A.Normal]
    (hG:Nat.card G=12288) (hA:Nat.card A=2048) (hP:Nat.card P=3)
    (hfix:Nat.card (A⊓centralizer (P:Set G):Subgroup G)=8) :
    Nat.card (normalizer (P:Set G))=48 := by
  have ha:IsPGroup 2 A:=IsPGroup.of_card (show Nat.card A=2^11 from hA)
  have hp:IsPGroup 3 P:=IsPGroup.of_card (show Nat.card P=3^1 from hP)
  have hn:normalizer (P:Set G)≤normalizer (A:Set G):=by rw [A.normalizer_eq_top];exact le_top
  have hAP:P≤normalizer (A:Set G):=by rw [A.normalizer_eq_top];exact le_top
  have hd:Disjoint A P:=IsPGroup.disjoint_of_ne 2 3 (by decide) A P ha hp
  have he:=SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf A P hAP hd
  have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes A (normalizer (P:Set G)) hn
  rw [he,hfix,cubic_normalizer_supplement_of_orders A P hG hA hP,card_top,hA,hG] at hh
  omega
end Subgroup
