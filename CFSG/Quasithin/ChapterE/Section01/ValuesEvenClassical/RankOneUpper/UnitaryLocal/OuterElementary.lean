module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal.Construction
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Bounds.Sylow

/-!
# Large elementary subgroups contain Sylows of the outer fixed group

For a self-centralizing normal PSU₃(2^f), the ambient quotient embeds in
its actual outer automorphism group. Semilinear coverage makes the outer
two-rank at most one, so the image of an elementary subgroup A has order
at most two. If A has rank greater than f, its intersection with the
normal PSU₃ therefore has at least 2^f elements.

For an outer involution t in A, commutativity places this intersection
in the literal fixed subgroup C_G(t) ∩ L. Its proved identification with
PSL₂ over the Hermitian fixed field bounds every two-subgroup by 2^f.
A Sylow containing the intersection must consequently equal it. Applying
this containment to `localCandidate_E0` supplies E0 for the original A,
ambient Sylow S, and involution t.

This is the Sylow input to the unitary branch of Aschbacher–Smith E.1.14(1)
(printed p.214), with E0 as in E.1.2 (pp.209–210). The source cites Asc82a,
Lemma 4.7, whose proof was not available for inspection. The argument here
uses the checked semilinear coverage and fixed-group identification;
it does not assert the remaining E2 or E-generation conclusions.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.Converse Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The actual quotient by the normal unitary group has two-rank at most one. -/
theorem outer_quotient_two_rank_le (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) : primeRank 2 (G ⧸ L) ≤ 1 := by
  let : NeZero f := ⟨by omega⟩
  let eM := e.trans (MulEquiv.subgroupCongr (psu3Model_eq_projective f))
  have houter : primeRank 2 (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup (uform f))) ≤ 1 :=
    HermitianForm.EvenTwoRank.outer_two_rank_le_of_coverage (uform f) (uform_form f)
      ((uform f).semilinear_coverage f hf (uform_form f)
        (card_UField f (by omega)) (card_fixed_UField f (by omega)))
  have hL : primeRank 2 (MulAut.Outer L) ≤ 1 := by
    rw [primeRank_equiv 2 (MulAut.outerCongr eM)]
    exact houter
  exact (primeRank_le_of_injective 2 (MulAut.outerAction L)
    (MulAut.outerAction_injective L hC)).trans hL

/-- The image of A under the literal quotient map has order at most two. -/
theorem elementary_outer_image_card_le_two (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) :
    Nat.card (A.map (QuotientGroup.mk' L)) ≤ 2 := by
  let := hA
  have h := (primeRank_le_iff_elementary_card_le (G ⧸ L)).mp
    (outer_quotient_two_rank_le L hf e hC) (A.map (QuotientGroup.mk' L))
    (IsElementaryAbelian.map (QuotientGroup.mk' L))
  simpa only [pow_one] using h

/-- Rank greater than f forces at least 2^f elements into the inner intersection. -/
theorem large_elementary_inner_card (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hr : f < Group.rank A) :
    2 ^ f ≤ Nat.card (A ⊓ L : Subgroup G) := by
  let := hA
  let q : A →* G ⧸ L := (QuotientGroup.mk' L).comp A.subtype
  have hk : q.ker = L.subgroupOf A := by
    ext x
    exact QuotientGroup.eq_one_iff _
  have hp : IsPGroup 2 q.ker := hA.isPGroup.to_subgroup q.ker
  obtain ⟨k, hkcard⟩ := hp.exists_card_eq
  have hc : Nat.card A ≤ 2 ^ (k + 1) := by
    rw [← q.ker.card_mul_index, index_ker, hkcard, pow_succ]
    apply Nat.mul_le_mul_left
    change Nat.card ((QuotientGroup.mk' L).comp A.subtype).range ≤ 2
    rw [MonoidHom.range_comp, range_subtype]
    exact elementary_outer_image_card_le_two L hf e hC A hA
  have hrk := IsElementaryAbelian.rank_le_of_card_le A hc
  have hswap : Nat.card q.ker = Nat.card (A ⊓ L : Subgroup G) := by
    rw [hk, ← inf_subgroupOf_left L A]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A ⊓ L ≤ A)).toEquiv
  rw [← hswap, hkcard]
  exact Nat.pow_le_pow_right (by decide) (by omega)

omit [Finite G] in
/-- The fixed-field PSL₂ identification bounds every two-subgroup of the fixed core. -/
theorem fixedCore_twoGroup_card_le (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) (t : G) (ht : t ∉ L) (ht2 : t ^ 2 = 1)
    (P : Subgroup (fixedCore L t)) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 ^ f := by
  let : NeZero f := ⟨by omega⟩
  let K := FixedBy.subfield (UField f) (uconj f)
  have hcard : Nat.card K = 2 ^ f := card_fixed_UField f (by omega)
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨ec⟩ := fixedCore_equiv L hf e hC t ht ht2
  rw [← hcard]
  exact Theory.PSL2.twoGroup_card_le_field_of_injective hP
    (ec.toMonoidHom.comp P.subtype) (ec.injective.comp P.subtype_injective)

/-- For every outer involution in A, A contains a Sylow of its actual fixed core. -/
theorem exists_sylow_fixedCore_map_le (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hr : f < Group.rank A)
    (t : G) (htA : t ∈ A) (htL : t ∉ L) (ht2 : t ^ 2 = 1) :
    ∃ P : Sylow 2 (fixedCore L t),
      (P : Subgroup (fixedCore L t)).map (fixedCore L t).subtype ≤ A := by
  let := hA
  have hAC : A ≤ centralizer ({t} : Set G) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨t, htA⟩)
  have hle : A ⊓ L ≤ fixedCore L t := inf_le_inf hAC le_rfl
  let B := (A ⊓ L).subgroupOf (fixedCore L t)
  have hBp : IsPGroup 2 B :=
    (hA.isPGroup.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe hle).symm
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  have hBcard : 2 ^ f ≤ Nat.card B := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact large_elementary_inner_card L hf e hC A hA hr
  have heq : B = (P : Subgroup (fixedCore L t)) :=
    eq_of_le_of_card_ge hBP
      ((fixedCore_twoGroup_card_le L hf e hC t htL ht2 _ P.isPGroup').trans hBcard)
  refine ⟨P, ?_⟩
  rw [← heq]
  exact (map_subgroupOf_eq_of_le hle).le.trans inf_le_left


/-- The large-rank hypothesis discharges the Sylow-containment premise in
`localCandidate_E0`, retaining the given ambient S, elementary A, and t. -/
theorem localCandidate_E0_of_large_rank (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) (S : Sylow 2 G)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAS : A ≤ (S : Subgroup G))
    (hr : f < Group.rank A) (hO : pCore 2 G = ⊥)
    (t : G) (htA : t ∈ A) (htL : t ∉ L) (ht2 : t ^ 2 = 1) :
    A ≤ localCandidate L (S : Subgroup G) A t ∧
    tau (S : Subgroup G) A ≤ localCandidate L (S : Subgroup G) A t ∧
    ∃ U : Sylow 2 (localCandidate L (S : Subgroup G) A t),
      (U : Subgroup (localCandidate L (S : Subgroup G) A t)) =
        (S : Subgroup G).subgroupOf (localCandidate L (S : Subgroup G) A t) := by
  obtain ⟨P, hPA⟩ := exists_sylow_fixedCore_map_le L hf e hC A hA hr t htA htL ht2
  exact localCandidate_E0 L S A hA hAS hO htA P hPA

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
