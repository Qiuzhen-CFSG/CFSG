module

public import Stellmacher.ExceptionalType
public import Theory.GroupTheory.CentralSylowSquare
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.SpecificGroups.CyclicTwoDihedralFourPlanes
public import Stellmacher.Recognition.Sp4TwoSquarePlanes

/-!
# Excluding the local Sp₄(2) type in a simple group

A finite nonsolvable simple group cannot have Stellmacher's local Sp₄(2)
type. The exact local-type definition supplies two C₂ × S₄ subgroups with
an ambient Sylow intersection and a generated join with trivial two-core.
The proof uses neither maximal two-locality nor an ambient generation
assumption, and imposes no additional normalizer condition.

The square-plane theorem extracts two normal elementary four-groups in
S ≃ C₂ × D₈, all of whose elements have ambient square roots. Their
noncommutative join U has index two in S and contains every involution of U
in one of the planes. Small-group geometry supplies a central involution t
of S with no square root in S. Thompson transfer forces t to be conjugate
into U, since simplicity and |S| = 16 exclude normal index-two subgroups.
Consequently t has an ambient square root. Conjugating that root inside
C_G(t) brings it into the supplied Sylow subgroup and preserves t, giving
the contradiction. The nonsolvability parameter is retained in the requested
recognition interface; the local Sylow order already excludes the cyclic
simple cases.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, Chapter 12,
proof of Theorem 3, printed pp. 365–366, and Thompson's Transfer Lemma
12.1.1, pp. 338–339. The square-root lifting lemma replaces the source's
maximality argument when the common subgroup is already ambient Sylow.
The exact local Sp₄(2) configuration is defined after (8.2) in
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open scoped IsMulCommutative

private theorem no_normal_index_two_of_sylow_card
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hSCard : Nat.card S = 16) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa [hbot] using hi
    have hdiv := Subgroup.card_subgroup_dvd_card (S : Subgroup G)
    rw [hSCard, hcard] at hdiv
    norm_num at hdiv
  · simp [htop] at hi

private theorem square_transfer_contradiction
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (U : Subgroup S) (hU : U.index = 2)
    (hsquare : ∀ u : S, u ∈ U → u ^ 2 = 1 → ∃ x : G, x ^ 2 = (u : G))
    (t : S) (htcenter : t ∈ Subgroup.center S) (htorder : orderOf t = 2)
    (htnonsquare : ∀ x : S, x ^ 2 ≠ t) : False := by
  obtain ⟨other, hconj, hother⟩ :=
    S.exists_isConj_mem_of_index_two hno U hU t htorder
  have ht2 : (t : G) ^ 2 = 1 := by
    have ht : t ^ 2 = 1 := by simpa only [htorder] using pow_orderOf_eq_one t
    exact congrArg Subtype.val ht
  have hother2 : other ^ 2 = 1 := by
    apply Subtype.ext
    have hpow := hconj.pow 2
    rw [ht2] at hpow
    exact isConj_one_right.mp hpow
  obtain ⟨x, hx⟩ := hsquare other hother hother2
  have hroot : ∃ y : G, y ^ 2 = (t : G) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj.symm
    refine ⟨c * x * c⁻¹, ?_⟩
    rw [conj_pow, hx, hc]
  obtain ⟨y, hy⟩ := (S.exists_square_iff_of_mem_center t htcenter htorder).mp hroot
  exact htnonsquare y hy

private theorem square_plane_transfer_contradiction
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (e : S ≃* Multiplicative (ZMod 2) × DihedralGroup 4)
    (Q1 Q2 : Subgroup S) [Q1.Normal] [Q2.Normal]
    (hQ1 : IsElementaryAbelian 2 Q1) (hQ2 : IsElementaryAbelian 2 Q2)
    (hcard1 : Nat.card Q1 = 4) (hcard2 : Nat.card Q2 = 4)
    (hnoncomm : ¬ IsMulCommutative (Q1 ⊔ Q2 : Subgroup S))
    (hsquare1 : ∀ q : S, q ∈ Q1 → ∃ x : G, x ^ 2 = (q : G))
    (hsquare2 : ∀ q : S, q ∈ Q2 → ∃ x : G, x ^ 2 = (q : G)) : False := by
  obtain ⟨hindex, hcover, t, htcenter, htorder, _htoutside, htnonsquare⟩ :=
    CyclicTwoDihedralFour.c2d8_two_plane_geometry e Q1 Q2 hQ1 hQ2
      hcard1 hcard2 hnoncomm
  apply square_transfer_contradiction S hno (Q1 ⊔ Q2) hindex _ t htcenter htorder htnonsquare
  intro u hu hu2
  rcases hcover u hu hu2 with h1 | h2
  · exact hsquare1 u h1
  · exact hsquare2 u h2

/-- The source-local Sp₄(2) configuration cannot occur in a finite
nonsolvable simple group. -/
public theorem not_sp4Two_type_of_simple_nonsolvable
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) : ¬ IsOfSp4TwoType G := by
  intro hType
  obtain ⟨S, ⟨e⟩, Q1, Q2, hN1, hN2, hQ1, hQ2, hcard1, hcard2,
    hnoncomm, hsquare1, hsquare2⟩ := sp4Two_square_planes hType
  let _ := hN1
  let _ := hN2
  have hSCard : Nat.card S = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  exact square_plane_transfer_contradiction S
    (no_normal_index_two_of_sylow_card S hSCard) e Q1 Q2 hQ1 hQ2
    hcard1 hcard2 hnoncomm hsquare1 hsquare2

end Stellmacher.Recognition
