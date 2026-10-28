module
public import Theory.GroupTheory.NormalFourCentralizer
public import Theory.GroupTheory.PGroup.NormalFour
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Two-rank of involution centralizers

If a finite group has no normal subgroup of index two and contains an
elementary abelian two-subgroup of order at least eight, every involution
lies in such an elementary subgroup. Consequently every involution centralizer
has two-rank at least three. In particular a rank-two involution centralizer
bounds the two-rank of the ambient group and of its Sylow two-subgroups.

Choose a Sylow subgroup containing the given elementary subgroup and a normal
four-group inside that Sylow subgroup. Its centralizer has index at most two,
so Thompson transfer conjugates the chosen involution into the centralizer.
The normal-four extension theorem supplies an elementary eight containing the
conjugate. Conjugating back gives the marked subgroup in the original
involution centralizer.

Source: GLS, *The Classification of the Finite Simple Groups*, volume 2,
Chapter D, Lemma 15.17(i), `refs/KGroup/GLS2/ChapterD.tex`. The contrapositive
and its Sylow form supply the rank reduction in volume 4, Chapter 1,
Lemma 4.10.
-/

open scoped IsMulCommutative

namespace Subgroup

/-- A marked elementary eight in the centralizer of any involution. -/
public theorem exists_elementary_eight_in_involution_centralizer
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (x : G) (hx : orderOf x = 2) :
    ∃ V : Subgroup G, IsElementaryAbelian 2 V ∧ 8 ≤ Nat.card V ∧
      x ∈ V ∧ V ≤ centralizer {x} := by
  obtain ⟨S, hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let ES := E.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 ES := IsElementaryAbelian.subgroupOf hES
  have hEScard : 8 ≤ Nat.card ES := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv]
  obtain ⟨U, hUn, hUe, hU⟩ :=
    S.isPGroup'.exists_normal_four_of_elementary_rank_three ES hEScard
  let : U.Normal := hUn
  let : IsElementaryAbelian 2 U := hUe
  let C := centralizer (U : Set S)
  have hCindex : C.index ≤ 2 := centralizer_index_le_two_of_normal_four S.isPGroup' U hU
  obtain ⟨y, hxy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have hord {a : G} (hxa : IsConj x a) : orderOf a = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxa
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hy : orderOf y = 2 :=
    (orderOf_injective (S : Subgroup G).subtype Subtype.coe_injective y).symm.trans (hord hxy)
  have ht : ∃ t : S, IsConj x (t : G) ∧ t ∈ C := by
    by_cases hyC : y ∈ C
    · exact ⟨y, hxy, hyC⟩
    have hCtwo : C.index = 2 := by
      have hzero := C.index_ne_zero_of_finite
      have hone : C.index ≠ 1 := fun h => hyC (index_eq_one.mp h ▸ mem_top y)
      omega
    obtain ⟨t, hyt, htC⟩ := S.exists_isConj_mem_of_index_two hno C hCtwo y hy
    exact ⟨t, hxy.trans hyt, htC⟩
  obtain ⟨t, hxt, htC⟩ := ht
  have htorder : orderOf t = 2 :=
    (orderOf_injective (S : Subgroup G).subtype Subtype.coe_injective t).symm.trans (hord hxt)
  obtain ⟨W, hWe, hWcard, htW⟩ :=
    exists_elementary_eight_of_mem_centralizer_normal_four S.isPGroup' U hU ES hEScard
      t (by simpa only [htorder] using pow_orderOf_eq_one t) htC
  let : IsElementaryAbelian 2 W := hWe
  obtain ⟨g, hg⟩ := isConj_iff.mp hxt.symm
  let f : S →* G := (MulAut.conj g).toMonoidHom.comp (S : Subgroup G).subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.coe_injective
  let V := W.map f
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map f
  have hxV : x ∈ V := mem_map.mpr ⟨t, htW, hg⟩
  refine ⟨V, inferInstance, ?_, hxV, ?_⟩
  · rwa [card_map_of_injective hf]
  · intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨v, hv⟩ : V) ⟨x, hxV⟩))

end Subgroup

/-- A local rank-two involution centralizer bounds the ambient two-rank. -/
public theorem primeRank_two_le_two_of_involution_centralizer
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (x : G) (hx : orderOf x = 2)
    (hC : primeRank 2 (Subgroup.centralizer {x}) ≤ 2) : primeRank 2 G ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hEe
  let : IsElementaryAbelian 2 E := hEe
  by_contra! hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hn3 : 3 ≤ n := by
    rw [hn] at hE
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hE
    omega
  have hE8 : 8 ≤ Nat.card E := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn3
  obtain ⟨V, hVe, hVcard, _, hVC⟩ :=
    Subgroup.exists_elementary_eight_in_involution_centralizer hno E hE8 x hx
  let : IsElementaryAbelian 2 V := hVe
  let VC := V.subgroupOf (Subgroup.centralizer {x})
  have hVCe : IsElementaryAbelian 2 VC := IsElementaryAbelian.subgroupOf hVC
  have hVCcard := (primeRank_le_iff_elementary_card_le _).mp hC VC hVCe
  have hc : Nat.card VC = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv
  change Nat.card VC ≤ 2 ^ 2 at hVCcard
  omega

/-- GLS2, Chapter D, Lemma 15.17(i). -/
public theorem primeRank_involution_centralizer_ge_three
    {G : Type*} [Group G] [Finite G]
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (hr : 3 ≤ primeRank 2 G) (x : G) (hx : orderOf x = 2) :
    3 ≤ primeRank 2 (Subgroup.centralizer {x}) := by
  by_contra! hc
  have := primeRank_two_le_two_of_involution_centralizer hno x hx (by omega)
  omega

/-- The Sylow rank reduction used in GLS4, Chapter 1, Lemma 4.10. -/
public theorem Sylow.primeRank_two_le_two_of_involution_centralizer
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (x : G) (hx : orderOf x = 2)
    (hC : primeRank 2 (Subgroup.centralizer {x}) ≤ 2) : primeRank 2 S ≤ 2 :=
  by
    apply (primeRank_le_iff_elementary_card_le S).mpr
    intro E hE
    let : IsElementaryAbelian 2 E := hE
    have h := (primeRank_le_iff_elementary_card_le G).mp
      (_root_.primeRank_two_le_two_of_involution_centralizer hno x hx hC)
      (E.map (S : Subgroup G).subtype) (IsElementaryAbelian.map _)
    rwa [Subgroup.card_map_of_injective Subtype.coe_injective] at h
