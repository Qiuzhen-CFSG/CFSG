module

public import Stellmacher.Recognition.LyonsU3Four.NormalizerAction
public import Theory.GroupTheory.NormalSylowCoreCentralizer
public import Theory.GroupTheory.CyclicFifteen
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The actual order-fifteen Sylow normalizer quotient

We work with N_G(S)/O_{2'}(N_G(S)) and the canonical embedding of S.
Burnside transfer in the Sylow centralizer identifies S C_N(S) with
S O_{2'}(N), so the embedded S has index fifteen. Schur–Zassenhaus gives
a complement. Groups of order fifteen are cyclic, and the trivial odd
core makes the action of this complement faithful. Transporting the
internal semidirect product along the canonical embedding fixes S
pointwise in the stated equivalence.

Source: Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), Lemma 1(c), pp. 372–373.
-/

namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup

/-- The intrinsic centralizer in the normalizer is the restriction of the
ambient Sylow centralizer. -/
private theorem normalizer_sylow_centralizer {G : Type*} [Group G] (S : Sylow 2 G) :
    centralizer ((S.subtype (S : Subgroup G).le_normalizer) : Set (normalizer (S : Set G))) =
      (centralizer (S : Set G)).subgroupOf (normalizer (S : Set G)) := by
  ext n
  simp only [mem_centralizer_iff, mem_subgroupOf]
  constructor
  · intro hn s hs
    exact congrArg Subtype.val (hn ⟨s, (S : Subgroup G).le_normalizer hs⟩ hs)
  · intro hn s hs
    exact Subtype.ext (hn s hs)

/-- The automizer denominator in the actual normalizer equals the product
of the supplied Sylow subgroup and the actual odd core. -/
public theorem normalizer_automizer_denominator_eq_sup_oddCore
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    ((S : Subgroup G) ⊔ centralizer (S : Set G)).subgroupOf
        (normalizer (S : Set G)) =
      (S : Subgroup G).subgroupOf (normalizer (S : Set G)) ⊔
        pPrimeCore 2 (normalizer (S : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := S.subtype (S : Subgroup G).le_normalizer
  have : (T : Subgroup (normalizer (S : Set G))).Normal :=
    by
      change ((S : Subgroup G).subgroupOf (normalizer (S : Set G))).Normal
      rw [← S.coe_coe]
      infer_instance
  have he := T.sup_centralizer_eq_sup_pPrimeCore_of_normal
  rw [normalizer_sylow_centralizer S] at he
  have hs := subgroupOf_sup (S : Subgroup G).le_normalizer
    (centralizer_le_normalizer ((S : Subgroup G) : Set G))
  simp only [S.coe_coe] at hs
  rw [hs]
  exact he

/-- The canonical Sylow image has precisely the given automizer index. -/
public theorem sylowNormalizerQuotientMap_range_index
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    (sylowNormalizerQuotientMap S).range.index = automizerIndex S := by
  let N := normalizer (S : Set G)
  let O := pPrimeCore 2 N
  let q := QuotientGroup.mk' O
  have hr : (sylowNormalizerQuotientMap S).range =
      ((S : Subgroup G).subgroupOf N).map q := by
    rw [sylowNormalizerQuotientMap, MonoidHom.range_comp,
      inclusion_range]
  rw [hr, index_map, QuotientGroup.ker_mk',
    q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective O), index_top, mul_one]
  rw [← normalizer_automizer_denominator_eq_sup_oddCore S]
  rfl

/-- If the actual automizer index is fifteen, the quotient of the actual
Sylow normalizer by its odd core is a semidirect product with a cyclic
group of order fifteen. Its generator acts on the supplied Sylow with
order exactly fifteen, and the equivalence preserves the canonical Sylow
embedding. The construction does not require simplicity of the ambient group. -/
public theorem exists_orderFifteen_normalizer_equiv {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15) :
    ∃ (β : MulAut S) (α : Multiplicative (ZMod 15) →* MulAut S),
      orderOf β = 15 ∧ α (Multiplicative.ofAdd (1 : ZMod 15)) = β ∧
      ∃ e : (normalizer (S : Set G) ⧸ pPrimeCore 2 (normalizer (S : Set G))) ≃*
        S ⋊[α] Multiplicative (ZMod 15),
        ∀ s : S, e (sylowNormalizerQuotientMap S s) = SemidirectProduct.inl s := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := normalizer (S : Set G)
  let O := pPrimeCore 2 N
  let Q := N ⧸ O
  let q : N →* Q := QuotientGroup.mk' O
  let SN := S.subtype (S : Subgroup G).le_normalizer
  have hSN : (SN : Subgroup N).Normal := by
    change ((S : Subgroup G).subgroupOf (normalizer (S : Set G))).Normal
    rw [← S.coe_coe]
    infer_instance
  let T : Sylow 2 Q := SN.mapSurjective (QuotientGroup.mk'_surjective O)
  let f : S →* Q := sylowNormalizerQuotientMap S
  let P := f.range
  have hPT : P = (T : Subgroup Q) := by
    change (sylowNormalizerQuotientMap S).range =
      ((S : Subgroup G).subgroupOf N).map q
    rw [sylowNormalizerQuotientMap, MonoidHom.range_comp, inclusion_range]
  have hPN : P.Normal := by
    rw [hPT]
    exact Subgroup.Normal.map hSN q (QuotientGroup.mk'_surjective O)
  let eS : S ≃* P := MonoidHom.ofInjective (sylowNormalizerQuotientMap_injective S h)
  have hPi : P.index = 15 := (sylowNormalizerQuotientMap_range_index S).trans h15
  have hcop : (Nat.card P).Coprime P.index := by
    rw [hPT]
    exact T.card_coprime_index
  obtain ⟨B, hB⟩ := exists_right_complement'_of_coprime hcop
  have hBcard : Nat.card B = 15 := hB.symm.index_eq_card.symm.trans hPi
  let : IsCyclic B := isCyclic_of_card_eq_fifteen hBcard
  let c : Multiplicative (ZMod 15) ≃* B :=
    mulEquivOfCyclicCardEq (by simpa using hBcard.symm)
  let γ : B →* MulAut P := P.normalizerMonoidHom.comp
    (inclusion (P.normalizer_eq_top ▸ le_top))
  have hC : centralizer (P : Set Q) ≤ P := by
    have hTN : (T : Subgroup Q).Normal := hPT ▸ hPN
    have hh := T.centralizer_le_sup_pPrimeCore_of_normal
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2, sup_bot_eq] at hh
    rw [← T.coe_coe, ← hPT] at hh
    exact hh
  have hγ : Function.Injective γ := by
    apply γ.ker_eq_bot_iff.mp
    apply bot_unique
    intro b hb
    have hbC : (b : Q) ∈ centralizer (P : Set Q) := by
      have hh : inclusion (P.normalizer_eq_top ▸ le_top) b ∈ P.normalizerMonoidHom.ker := hb
      rwa [normalizerMonoidHom_ker] at hh
    exact Subtype.ext (disjoint_def.mp hB.disjoint (hC hbC) b.property)
  let α : Multiplicative (ZMod 15) →* MulAut S :=
    (MulAut.congr eS.symm).toMonoidHom.comp (γ.comp c.toMonoidHom)
  have hα : Function.Injective α :=
    (MulAut.congr eS.symm).injective.comp (hγ.comp c.injective)
  let β := α (Multiplicative.ofAdd (1 : ZMod 15))
  have hβ : orderOf β = 15 := by
    rw [show β = α (Multiplicative.ofAdd (1 : ZMod 15)) from rfl,
      orderOf_injective α hα, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  let k : P ⋊[γ] B ≃* Q := SemidirectProduct.mulEquivSubgroup hB
  let d : P ⋊[γ] B ≃* S ⋊[α] Multiplicative (ZMod 15) :=
    SemidirectProduct.congr' eS.symm c.symm
  refine ⟨β, α, hβ, rfl, k.symm.trans d, ?_⟩
  intro s
  have hk : k.symm (f s) = SemidirectProduct.inl (eS s) := by
    apply k.injective
    rw [k.apply_symm_apply]
    change f s = (SemidirectProduct.mulEquivSubgroup hB) (SemidirectProduct.inl (eS s))
    rw [SemidirectProduct.mulEquivSubgroup_apply]
    simpa only [SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      OneMemClass.coe_one, mul_one] using (MonoidHom.ofInjective_apply
        (sylowNormalizerQuotientMap_injective S h) (x := s)).symm
  change d (k.symm (f s)) = _
  rw [hk]
  apply SemidirectProduct.ext
  · change ((SemidirectProduct.congr' eS.symm c.symm)
      (SemidirectProduct.inl (eS s))).left = s
    rw [SemidirectProduct.congr'_apply_left, SemidirectProduct.left_inl,
      eS.symm_apply_apply]
  · change ((SemidirectProduct.congr' eS.symm c.symm)
      (SemidirectProduct.inl (eS s))).right = 1
    rw [SemidirectProduct.congr'_apply_right, SemidirectProduct.right_inl, map_one]

end Stellmacher.Recognition.LyonsU3Four
