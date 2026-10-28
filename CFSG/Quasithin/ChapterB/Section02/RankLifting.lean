module
public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.ElementaryAbelian.UniqueLift
public import Mathlib.Data.Nat.Log

/-!
# B.2.4 and B.2.21: ranks and unique elementary lifts

Ranks of elementary abelian two-groups are expressed as base-two logarithms
of their orders. The two-rank of S is the logarithm of the existing
`elementaryAbelianMaxOrder S`; the rank of V/C_V(A) is the difference of the
logarithms of the orders of V and C_V(A). Thus the rank-deficit hypothesis
uses exactly the maximum family already used by Stellmacher.

B.2.4 compares A with the elementary subgroup V C_A(V). Exact cardinal
counting proves the bound and forces this replacement to have maximum order
in the equality case. For j = 0 it lies in C_S(V), giving equality of ranks,
inclusion of maximum families, and both Omega-center containments.

B.2.21 uses the full proof continuing onto printed p.83: choose b in B with
the same image as a. Since a, b, and their difference in V square to one,
the difference commutes with a and lies in C_V(A). This puts a in B;
the hypothesis C_V(A) = C_V(a) then forces B into A, and maximum order
gives equality. The elementary lifting calculation is in
`Theory.ElementaryAbelian.UniqueLift`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.2.4 and B.2.21, printed pp.75–76 and 82–83.
-/

namespace CFSG.Quasithin.ChapterB
open Stellmacher
variable {G H : Type*} [Group G] [Group H] [Finite G]

private theorem card_pow_log (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] : Nat.card E = 2 ^ Nat.log 2 (Nat.card E) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  rw [hn, Nat.log_pow Nat.one_lt_two]

private theorem maxOrder_pow_log (S : Subgroup G) :
    elementaryAbelianMaxOrder S = 2 ^ Nat.log 2 (elementaryAbelianMaxOrder S) := by
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  let _ : IsElementaryAbelian 2 A := hA.2.1
  rw [maxOrder_eq_card_of_mem S A hA]
  exact card_pow_log A

private theorem image_pow_log (A : Subgroup G) [IsElementaryAbelian 2 A]
    (q : G →* H) : Nat.card (A.map q) = 2 ^ Nat.log 2 (Nat.card (A.map q)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  let _ : Finite (A.map q) := ((Set.toFinite (A : Set G)).image q).to_subtype
  exact card_pow_log (A.map q)

private theorem image_rank_pos (A : Subgroup G) [IsElementaryAbelian 2 A]
    (q : G →* H) (hq : A.map q ≠ ⊥) : 0 < Nat.log 2 (Nat.card (A.map q)) := by
  let _ : Finite (A.map q) := ((Set.toFinite (A : Set G)).image q).to_subtype
  have hlt := (Subgroup.one_lt_card_iff_ne_bot (A.map q)).mpr hq
  rw [image_pow_log A q] at hlt
  have hh : 2 ^ 0 < 2 ^ Nat.log 2 (Nat.card (A.map q)) := by simpa using hlt
  exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hh

private theorem deficit_card (S A : Subgroup G) [IsElementaryAbelian 2 A]
    (q : G →* H) (hq : A.map q ≠ ⊥) (j : ℕ)
    (hAj : Nat.log 2 (Nat.card A) = Nat.log 2 (elementaryAbelianMaxOrder S) - j) :
    Nat.card A * 2 ^ j = elementaryAbelianMaxOrder S := by
  have hpos := image_rank_pos A q hq
  have hle : Nat.card (A.map q) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd A q)
  have hl := Nat.log_mono_right (b := 2) hle
  have hj : Nat.log 2 (Nat.card A) + j =
      Nat.log 2 (elementaryAbelianMaxOrder S) := by omega
  conv_rhs => rw [maxOrder_pow_log S]
  rw [card_pow_log A, ← pow_add, hj]

/-- B.2.4(1): the image rank is at least the fixed-space codimension minus j.
The nontrivial image also makes the natural-number deficit exact. -/
public theorem lemma_B_2_4_1 (S V A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVS : V ≤ S) (hAS : A ≤ S) (j : ℕ)
    (hAj : Nat.log 2 (Nat.card A) = Nat.log 2 (elementaryAbelianMaxOrder S) - j)
    (q : G →* H) (hker : q.ker = Subgroup.centralizer (V : Set G))
    (hq : A.map q ≠ ⊥) :
    Nat.log 2 (Nat.card V) -
        Nat.log 2 (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) - j ≤
      Nat.log 2 (Nat.card (A.map q)) := by
  have hcard := (maxElementary_card_bound_and_eq S V A hVS hAS j
    (deficit_card S A q hq j hAj) q hker).1
  let _ : IsElementaryAbelian 2 ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    IsElementaryAbelian.of_le inf_le_left
  rw [card_pow_log V, card_pow_log ↥(V ⊓ Subgroup.centralizer (A : Set G)),
    image_pow_log A q, ← pow_add, ← pow_add] at hcard
  have hh := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hcard
  omega

/-- B.2.4(2): equality in the rank bound makes V C_A(V) a maximum elementary subgroup. -/
public theorem lemma_B_2_4_2 (S V A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVS : V ≤ S) (hAS : A ≤ S) (j : ℕ)
    (hAj : Nat.log 2 (Nat.card A) = Nat.log 2 (elementaryAbelianMaxOrder S) - j)
    (q : G →* H) (hker : q.ker = Subgroup.centralizer (V : Set G))
    (hq : A.map q ≠ ⊥)
    (heq : Nat.log 2 (Nat.card V) -
        Nat.log 2 (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) - j =
      Nat.log 2 (Nat.card (A.map q))) :
    V ⊔ (A ⊓ Subgroup.centralizer (V : Set G)) ∈ elementaryAbelianMaxSubgroups S := by
  apply (maxElementary_card_bound_and_eq S V A hVS hAS j
    (deficit_card S A q hq j hAj) q hker).2
  let _ : IsElementaryAbelian 2 ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    IsElementaryAbelian.of_le inf_le_left
  have hpos := image_rank_pos A q hq
  have hadd : Nat.log 2 (Nat.card V) =
      Nat.log 2 (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) +
      Nat.log 2 (Nat.card (A.map q)) + j := by omega
  rw [card_pow_log V, card_pow_log ↥(V ⊓ Subgroup.centralizer (A : Set G)),
    image_pow_log A q, ← pow_add, ← pow_add, hadd]

/-- B.2.4(3): equality for a maximum elementary A gives a maximum replacement,
full two-rank in C_S(V), inclusion of maximum families, and both Omega-center
containments. This conclusion also holds when the image is trivial. -/
public theorem lemma_B_2_4_3 (S V A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVS : V ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* H) (hker : q.ker = Subgroup.centralizer (V : Set G))
    (heq : Nat.log 2 (Nat.card V) -
        Nat.log 2 (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) =
      Nat.log 2 (Nat.card (A.map q))) :
    V ⊔ (A ⊓ Subgroup.centralizer (V : Set G)) ∈ elementaryAbelianMaxSubgroups S ∧
      Nat.log 2 (elementaryAbelianMaxOrder (S ⊓ Subgroup.centralizer (V : Set G))) =
        Nat.log 2 (elementaryAbelianMaxOrder S) ∧
      elementaryAbelianMaxSubgroups (S ⊓ Subgroup.centralizer (V : Set G)) ⊆
        elementaryAbelianMaxSubgroups S ∧
      V ≤ omegaOneCenterAmbient
        (elementaryAbelianMaxJ (S ⊓ Subgroup.centralizer (V : Set G))) ∧
      omegaOneCenterAmbient (elementaryAbelianMaxJ S) ≤
        omegaOneCenterAmbient
          (elementaryAbelianMaxJ (S ⊓ Subgroup.centralizer (V : Set G))) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    IsElementaryAbelian.of_le inf_le_left
  have hle : Nat.log 2 (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) ≤
      Nat.log 2 (Nat.card V) := Nat.log_mono_right
        (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective inf_le_left))
  have hadd : Nat.log 2 (Nat.card V) =
      Nat.log 2 (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) +
      Nat.log 2 (Nat.card (A.map q)) := by omega
  have hB := (maxElementary_card_bound_and_eq S V A hVS hA.1 0
    (by simpa using (maxOrder_eq_card_of_mem S A hA).symm) q hker).2
    (by
      rw [card_pow_log V, card_pow_log ↥(V ⊓ Subgroup.centralizer (A : Set G)),
        image_pow_log A q, pow_zero, mul_one, ← pow_add, hadd])
  have hBC : V ⊔ (A ⊓ Subgroup.centralizer (V : Set G)) ≤
      S ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf hB.1 (sup_le
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance) inf_le_right)
  obtain ⟨hord, hfam, hV, hOmega⟩ :=
    maxElementary_centralizer_maxOrder_and_omegaCenter S V _ hVS hB hBC
  exact ⟨hB, congrArg (Nat.log 2) hord, hfam, hV, hOmega⟩

/-- B.2.21: if V is self-centralizing and one element of A has the same fixed
subgroup in V as A, then A is the unique maximum elementary subgroup with
its quotient image. All maximality premises of the lifting lemma are discharged. -/
public theorem lemma_B_2_21 (V A B : Subgroup G) [IsElementaryAbelian 2 V]
    (q : G →* H) (hker : q.ker = Subgroup.centralizer (V : Set G))
    (hself : Subgroup.centralizer (V : Set G) = V)
    (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (hB : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (himage : A.map q = B.map q) (a : G) (ha : a ∈ A)
    (hfix : V ⊓ Subgroup.centralizer (A : Set G) =
      V ⊓ Subgroup.centralizer ({a} : Set G)) : B = A := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := hB.2.1
  have hf (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G)) :
      V ⊓ Subgroup.centralizer (E : Set G) ≤ E := by
    let _ : IsElementaryAbelian 2 ↥(V ⊓ Subgroup.centralizer (E : Set G)) :=
      IsElementaryAbelian.of_le inf_le_left
    exact maxElementary_contains_elementary_centralizer ⊤ E _ hE le_top inf_le_right
  exact Subgroup.eq_of_le_of_card_ge
    (IsElementaryAbelian.le_of_same_image_of_centralizer_singleton q V A B
      (hker.trans hself) (hf A hA) (hf B hB) himage a ha hfix)
    (hB.2.2 A le_top hA.2.1)

end CFSG.Quasithin.ChapterB
