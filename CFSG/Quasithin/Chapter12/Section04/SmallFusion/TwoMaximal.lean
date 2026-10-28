module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.NormalizerReduction
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Theory.GroupTheory.FourGroupNormalizerIndex

/-!
# The two-member maximum elementary family in 12.4.6

For a self-centralizing elementary four-space V, the common actor image
and fixed-space orders make every nontrivial-image maximum elementary
subgroup equal to A by the genuine B.2.21. The maximum family is {V,A}.
This statement is transported through the literal inclusion R→G. Its
normalizer permutes the pair, contradicting the index three already obtained
in the escaping-normalizer reduction.

The earlier B.4 image/fixed-space calculations and the block-theoretic step
Q=V remain explicit. In particular, this is the final group-theoretic
argument of the first case, not an assertion that its source premises have
already been constructed. No residual or block classification is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 12.4.6, printed p.814, using B.2.21, printed pp.82--83.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative Pointwise
set_option linter.style.haveILetI false
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- B.2.21 and the common image calculation give exactly two maximum elementary subgroups. -/
theorem maxFamily_eq_pair_of_common_image
    (V A : Subgroup G) [IsElementaryAbelian 2 V]
    (q : G →* H) (hker : q.ker = centralizer (V : Set G))
    (hself : centralizer (V : Set G) = V)
    (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (hVcard : Nat.card V = 16)
    (himagecard : Nat.card (A.map q) = 4)
    (hfixedcard : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) = 4)
    (a : G) (ha : a ∈ A)
    (hfix : V ⊓ centralizer (A : Set G) = V ⊓ centralizer ({a} : Set G))
    (hcommon : ∀ B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G),
      ¬ B ≤ V → B.map q = A.map q) :
    elementaryAbelianMaxSubgroups (⊤ : Subgroup G) = {V,A} := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 (V ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hCV : V ⊓ centralizer (A : Set G) ≤ A :=
    maxElementary_contains_elementary_centralizer ⊤ A _ hA le_top inf_le_right
  have hint : A ⊓ V = V ⊓ centralizer (A : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans A.le_centralizer)
    · exact le_inf hCV inf_le_left
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ V) A bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left,
    ← hself, ← hker, relIndex_ker] at hcount
  rw [hker,hself,hint,hfixedcard,himagecard] at hcount
  have hAcard : Nat.card A = 16 := by omega
  have hV : V ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G) :=
    ⟨le_top,inferInstance,fun B hB hBe => (hA.2.2 B hB hBe).trans (by rw [hAcard,hVcard])⟩
  ext B
  constructor
  · intro hB
    by_cases hBV : B ≤ V
    · exact Or.inl (eq_of_le_of_card_ge hBV (hB.2.2 V le_top inferInstance))
    · exact Or.inr (ChapterB.lemma_B_2_21 V A B q hker hself hA hB
        (hcommon B hB hBV).symm a ha hfix)
  · rintro (rfl | rfl)
    · exact hV
    · exact hA

/-- Apply the B.2.21 enumeration inside the literal ambient subgroup R.
The quotient homomorphism is still the map on R, not an unmarked replacement. -/
theorem ambient_maxFamily_eq_pair_of_common_image
    (R : Subgroup G) (V A : Subgroup R) [IsElementaryAbelian 2 V]
    (q : R →* H) (hker : q.ker = centralizer (V : Set R))
    (hself : centralizer (V : Set R) = V)
    (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup R))
    (hVcard : Nat.card V = 16)
    (himagecard : Nat.card (A.map q) = 4)
    (hfixedcard : Nat.card (V ⊓ centralizer (A : Set R) : Subgroup R) = 4)
    (a : R) (ha : a ∈ A)
    (hfix : V ⊓ centralizer (A : Set R) = V ⊓ centralizer ({a} : Set R))
    (hcommon : ∀ B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup R),
      ¬ B ≤ V → B.map q = A.map q) :
    elementaryAbelianMaxSubgroups R = {V.map R.subtype,A.map R.subtype} := by
  have hpair := maxFamily_eq_pair_of_common_image V A q hker hself hA
    hVcard himagecard hfixedcard a ha hfix hcommon
  ext B
  rw [maxFamily_equiv_iff R (MulEquiv.refl R) B, hpair]
  constructor
  · rintro ⟨C,(rfl | rfl),rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨V,Or.inl rfl,rfl⟩
    · exact ⟨A,Or.inr rfl,rfl⟩

/-- A normalizer acting on two maximum elementary subgroups has stabilizer index at most two. -/
theorem normalizer_index_le_two_of_maxFamily_pair
    (R V A : Subgroup G)
    (hV : V ∈ elementaryAbelianMaxSubgroups R)
    (hpair : elementaryAbelianMaxSubgroups R ⊆ {V,A}) :
    (normalizer (V : Set G)).relIndex (normalizer (R : Set G)) ≤ 2 := by
  classical
  let N := normalizer (R : Set G)
  letI : MulAction N (Subgroup G) := MulAction.compHom (Subgroup G)
    (MulAut.conj.comp N.subtype)
  have hs : MulAction.stabilizer N V = (normalizer (V : Set G)).subgroupOf N := by
    ext n
    exact mem_normalizer_iff_map_conj_eq.symm
  have hsub : MulAction.orbit N V ⊆ {V,A} := by
    rintro B ⟨n,rfl⟩
    apply hpair
    have hh := (maxFamily_map_injective_iff (MulAut.conj (n : G)).toMonoidHom
      (MulAut.conj (n : G)).injective R V).mpr hV
    have hn : R.map (MulAut.conj (n : G)).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp n.property
    rwa [hn] at hh
  change ((normalizer (V : Set G)).subgroupOf N).index ≤ 2
  rw [← hs, MulAction.index_stabilizer]
  exact (Set.ncard_le_ncard hsub).trans (by by_cases he : V = A <;> simp [he])

/-- The index-three contradiction in the first branch of 12.4.6, expressed
with the actual maximum elementary family of R. -/
theorem not_index_three_of_maxFamily_pair
    (R V A M : Subgroup G) (hM : M = normalizer (V : Set G))
    (hV : V ∈ elementaryAbelianMaxSubgroups R)
    (hpair : elementaryAbelianMaxSubgroups R ⊆ {V,A}) :
    (M ⊓ normalizer (R : Set G)).relIndex (normalizer (R : Set G)) ≠ 3 := by
  rw [hM,inf_relIndex_right]
  have hh := normalizer_index_le_two_of_maxFamily_pair R V A hV hpair
  omega

/-- The literal subgroup application: B.2.21 supplies the full two-member
family in R, whose normalizer action excludes the index three of 12.4.6. -/
theorem not_index_three_of_common_image
    (R : Subgroup G) (V A : Subgroup R) [IsElementaryAbelian 2 V]
    (q : R →* H) (hker : q.ker = centralizer (V : Set R))
    (hself : centralizer (V : Set R) = V)
    (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup R))
    (hVcard : Nat.card V = 16)
    (himagecard : Nat.card (A.map q) = 4)
    (hfixedcard : Nat.card (V ⊓ centralizer (A : Set R) : Subgroup R) = 4)
    (a : R) (ha : a ∈ A)
    (hfix : V ⊓ centralizer (A : Set R) = V ⊓ centralizer ({a} : Set R))
    (hcommon : ∀ B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup R),
      ¬ B ≤ V → B.map q = A.map q)
    (M : Subgroup G) (hM : M = normalizer (V.map R.subtype : Set G)) :
    (M ⊓ normalizer (R : Set G)).relIndex (normalizer (R : Set G)) ≠ 3 := by
  have hf := ambient_maxFamily_eq_pair_of_common_image R V A q hker hself hA
    hVcard himagecard hfixedcard a ha hfix hcommon
  exact not_index_three_of_maxFamily_pair R (V.map R.subtype) (A.map R.subtype) M hM
    (hf.symm ▸ (show V.map R.subtype ∈ ({V.map R.subtype,A.map R.subtype} : Set (Subgroup G)) from Or.inl rfl))
    (fun B hB => hf ▸ hB)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion
