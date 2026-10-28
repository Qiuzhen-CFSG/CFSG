module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ExceptionalNormalizer.Preparation
public import Theory.GroupAction.TernaryFusedFour

/-!
# Classification of the actual exceptional automizer

For the original odd centralizer complement `A`, apply the determinant and
vector-space reductions to the literal image `A.normalizerMonoidHom.range`.
The resulting subgroup of SL₃(3) is isomorphic to that image and retains the
three local conditions. In particular, fusion remains conjugacy inside the
image, rather than conjugacy in the ambient automorphism group.

The finite matrix classification proves that this image has order twelve
and normal Sylow two-subgroups. These are exactly the remaining premises of
`exceptionalOddNormalizer_of_automizer`. The three local conditions remain
explicit inputs to be supplied by the local normalizer-action fusion argument
in the full exceptional-normalizer assembly.
Source: Bender, *Finite groups with large subgroups* (1974), (4.1), printed
p.225, citing Janko (1966), Lemma 3.1.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- Under the original centralizer hypotheses, the actual normalizer action
image has a faithful SL₃(3) model preserving the local conditions. -/
public theorem exceptional_automizer_specialLinear_model_of_local_conditions
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (p : ℕ) (_hp : p = 3 ∨ p = 5)
    (x : G) (_hxC : x ∈ centralizer ({h.z} : Set G)) (_hx : orderOf x = p)
    (A : Subgroup G) (_a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27)
    (hfour : 4 ∣ Nat.card A.normalizerMonoidHom.range)
    (hel : ∀ P : Sylow 2 A.normalizerMonoidHom.range, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : A.normalizerMonoidHom.range,
      orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    ∃ H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)),
      Nonempty (A.normalizerMonoidHom.range ≃* H) ∧ 4 ∣ Nat.card H ∧
      (∀ P : Sylow 2 H, IsElementaryAbelian 2 P) ∧
      (∀ t : H, orderOf t ≠ 4) ∧
      (∀ t u : H, orderOf t = 2 → orderOf u = 2 → IsConj t u) := by
  let := he
  exact TernaryFusedFour.exists_specialLinear_model A hc
    A.normalizerMonoidHom.range hfour hel hfuse

/-- The three local action conditions give precisely the order and normality
premises needed to construct the full exceptional ambient normalizer. -/
public theorem exceptional_automizer_of_local_conditions
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (p : ℕ) (_hp : p = 3 ∨ p = 5)
    (x : G) (_hxC : x ∈ centralizer ({h.z} : Set G)) (_hx : orderOf x = p)
    (A : Subgroup G) (_a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27)
    (hfour : 4 ∣ Nat.card A.normalizerMonoidHom.range)
    (hel : ∀ P : Sylow 2 A.normalizerMonoidHom.range, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : A.normalizerMonoidHom.range,
      orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    Nat.card A.normalizerMonoidHom.range = 12 ∧
      ∀ P : Sylow 2 A.normalizerMonoidHom.range,
        (P : Subgroup A.normalizerMonoidHom.range).Normal := by
  let := he
  exact TernaryFusedFour.card_and_normal_sylow A hc
    A.normalizerMonoidHom.range hfour hel hfuse

end CFSG.Quasithin.Janko1CentralizerData
