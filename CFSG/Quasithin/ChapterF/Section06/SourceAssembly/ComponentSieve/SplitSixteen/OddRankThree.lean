module

public import Theory.GroupTheory.SplitDihedralCenter
public import Theory.SpecificGroups.Classical.SmallSylowOrders
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.SylowModel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective

/-!
# Excluding odd rank-three components under the split Sylow of order sixteen

The actual PSL3 and PSU3 orders are divisible by sixteen. Hence their
Sylow groups, when realized as a quotient of an original subgroup,
already use the entire ambient Sylow order. The literal inclusion and
quotient maps give an isomorphism with C2 times D8. Its noncyclic center
contradicts the genuine rank-three Sylow presentations.

These are the odd rank-three exclusions in Aschbacher--Smith F.6.18(8)--(9),
printed p.310. The conclusions concern the original central quotient K/Z(K).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.ClassicalSmallSylow
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

private theorem central_quotient_sylow_card_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (P : Sylow 2 (K ⧸ center K))
    (hd : 16 ∣ Nat.card (K ⧸ center K)) : Nat.card P = 16 := by
  have hT : Nat.card T = 16 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num
  have hu := sylow_card_section_le T K (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective (center K)) P
  have hl := Nat.le_of_dvd (Nat.card_pos (α := P))
    (P.pow_dvd_card_of_pow_dvd_card (n := 4) hd)
  omega

/-- No literal component central quotient is odd prime PSL3 under C2 times D8. -/
theorem not_pslThree_central_quotient_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 p) : False := by
  have hd : 16 ∣ Nat.card (K ⧸ center K) := by
    obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
    rw [Nat.card_congr j.toEquiv]
    exact sixteen_dvd_psl3_odd (hF ▸ hp)
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  have hc := central_quotient_sylow_card_sixteen T eT K P hd
  exact not_cyclic_sylow_center_of_split_sixteen_section T eT K
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective (center K)) P hc
    (Chapter1.XiEmbedding.InvariantLarge.OddCartan.isPSL_sylow_center_cyclic hp hm P)

/-- The same original-map exclusion for odd prime PSU3. -/
theorem not_psuThree_central_quotient_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 p) : False := by
  have hd : 16 ∣ Nat.card (K ⧸ center K) := by
    obtain ⟨F, _, _, J, hc, hj, ⟨j⟩⟩ := hm
    rw [Nat.card_congr j.toEquiv]
    exact sixteen_dvd_psu3_odd J (Fact.out : p.Prime).one_lt hp hc hj
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  have hc := central_quotient_sylow_card_sixteen T eT K P hd
  exact not_cyclic_sylow_center_of_split_sixteen_section T eT K
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective (center K)) P hc
    (Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition.isPSU_sylow_center_cyclic p hp hm P)

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
