module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ExceptionalNormalizer.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ExceptionalNormalizer.Splitting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ExceptionalNormalizer.LocalFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ExceptionalNormalizer.AutomizerClassification
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The exceptional ambient normalizer of the elementary order-27 complement

The preparatory construction supplies a four-group `V` normalizing `A`.
The kernel of the literal normalizer action is `A`, so its image has order
`|N_G(A)| / 27`. Local fusion proves that this image has order divisible by
four, elementary Sylow two-subgroups, and one internal involution class.
The ternary action classification therefore gives order twelve and normal
Sylow two-subgroups. The image of `V` is one of them, and its inverse image is
`A ⊔ V`, normal in `N_G(A)`. The lifting theorem then constructs an actual
subgroup `X` of order three and proves the full equality
`N_G(A) = A ⊔ (V ⊔ X)`.

The final theorem discharges both action-image premises from the original
local hypotheses and the elementary order-27 branch. Normality is always
relative to the appropriate centralizer or normalizer; the proof does not
use the independent exclusion of this branch. Source: Bender, *Finite groups
with large subgroups* (1974), (4.1), printed p.225, citing Janko (1966),
Lemma 3.1.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- Once the actual automizer has order twelve and normal Sylow two-subgroups,
the source exceptional normalizer follows, including its full equality. -/
public theorem exceptionalOddNormalizer_of_automizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (A : Subgroup G) (a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27)
    (hKcard : Nat.card A.normalizerMonoidHom.range = 12)
    (hKnormal : ∀ P : Sylow 2 A.normalizerMonoidHom.range,
      (P : Subgroup A.normalizerMonoidHom.range).Normal) :
    ExceptionalOddNormalizer A := by
  obtain ⟨V, hVe, hVc, -, hVN, -⟩ :=
    a.exists_normalizing_four_of_card_twentySeven hc p hp hxC hx
  let N := normalizer (A : Set G)
  let K := A.normalizerMonoidHom.range
  let f : N →* K := A.normalizerMonoidHom.rangeRestrict
  let VN := V.subgroupOf N
  let AN := A.subgroupOf N
  have hker : f.ker = AN := by
    rw [MonoidHom.ker_rangeRestrict]
    exact a.normalizer_action_ker_of_elementary_twentySeven he hc
  have hkerCard : Nat.card f.ker = 27 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv, hc]
  have hVNcard : Nat.card VN = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv).trans hVc
  have hVNp : IsPGroup 2 VN := IsPGroup.of_card (n := 2) (by simpa using hVNcard)
  have hinj : Function.Injective (f.comp VN.subtype) :=
    injective_comp_subtype_of_coprime_ker f (by rw [hkerCard]; decide) VN hVNp
  let Vbar := VN.map f
  let e : VN ≃* Vbar := MulEquiv.ofBijective (f.subgroupMap VN)
    ⟨fun u v huv => hinj (congrArg Subtype.val huv), f.subgroupMap_surjective VN⟩
  have hVbar : Nat.card Vbar = 4 := (Nat.card_congr e.toEquiv).symm.trans hVNcard
  obtain ⟨P, hVP⟩ := (hVNp.map f).exists_le_sylow
  have hPcard : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hKcard]
    decide +kernel
  have hPeq : Vbar = (P : Subgroup K) := eq_of_le_of_card_ge hVP (by rw [hVbar, hPcard])
  have hVnormal : Vbar.Normal := hPeq.symm ▸ hKnormal P
  have hpreimage : (AN ⊔ VN).Normal := by
    have hN := hVnormal.comap f
    change ((VN.map f).comap f).Normal at hN
    rw [comap_map_eq, hker, sup_comm VN] at hN
    exact hN
  have hAVnormal : ((A ⊔ V).subgroupOf N).Normal := by
    rw [subgroupOf_sup A.le_normalizer hVN]
    exact hpreimage
  apply exceptionalOddNormalizer_of_order_and_normal_four h A V he hc hVe hVc hVN hAVnormal
  rw [a.normalizer_card_of_elementary_twentySeven he hc, hKcard]

/-- An elementary order-27 odd centralizer complement has the full exceptional
ambient normalizer, with actual subgroups `V` and `X` and `X ≤ N_G(V)`. -/
public theorem exceptionalOddNormalizer_of_elementary
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (A : Subgroup G) (a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27) :
    ExceptionalOddNormalizer A := by
  obtain ⟨hfour, hel, hfuse⟩ :=
    h.exceptional_automizer_local_conditions p hp x hxC hx A a he hc
  obtain ⟨hKcard, hKnormal⟩ :=
    exceptional_automizer_of_local_conditions h p hp x hxC hx A a he hc
      hfour hel hfuse
  exact exceptionalOddNormalizer_of_automizer h p hp x hxC hx A a he hc
    hKcard hKnormal

end CFSG.Quasithin.Janko1CentralizerData
