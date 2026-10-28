module

public import Theory.ElementaryAbelian.BinaryRankDifference
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The subgroup filtration in the G₂(2)' exclusion

In the last paragraph of Aschbacher–Smith 13.8.27 (printed p.963), put
`A = Uγ`, `D = A ∩ Q_H`, and `E = D ∩ V_H`. The strict layer is `E < D`:
it follows from `V_H ≤ H_C` and `D ≰ H_C`. The other layers are the actual
images of `A` modulo `Q_H` and of `E` modulo `U_H`, followed by `D ∩ U_H`.
Counting these layers gives the strict rank inequality without assuming it.

The model-dependent commutator estimates and noncentrality on `Q_H/H_C`
remain explicit. These lemmas do not identify a G₂ module or assert the
source exclusion. Conjugacy is retained as an equality of embedded
subgroups under an actual ambient inner automorphism.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2
open Representation.BinaryOffender
open scoped IsMulCommutative

variable {J S P : Type*} [Group J] [Group S] [Group P] [Finite J]

private theorem card_eq_pow_rank (A : Subgroup J) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ rank A := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  simp only [rank, hn, Nat.log_pow Nat.one_lt_two]

private theorem rank_add_log_index (A B : Subgroup J)
    [IsElementaryAbelian 2 A] (h : B ≤ A) :
    rank B + Nat.log 2 (B.relIndex A) = rank A := by
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le h
  have hp : Nat.card B * B.relIndex A = Nat.card A := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup J) B A bot_le h
  rw [card_eq_pow_rank B, Subgroup.relIndex_eq_two_pow_quotient_finrank,
    ← pow_add, card_eq_pow_rank A] at hp
  have he := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hp
  rw [Subgroup.log_relIndex_eq_quotient_finrank]
  exact he

private theorem rank_lt_of_lt {A B : Subgroup J} [IsElementaryAbelian 2 B]
    (h : A < B) : rank A < rank B := by
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le h.le
  have hm : rank A ≤ rank B := Nat.log_mono_right (Subgroup.card_le_of_le h.le)
  apply lt_of_le_of_ne hm
  intro he
  apply h.ne
  apply Subgroup.eq_of_le_of_card_ge h.le
  rw [card_eq_pow_rank A, card_eq_pow_rank B, he]

/-- Rank-nullity for a homomorphism on an elementary abelian subgroup.
The kernel is the literal intersection with the ambient kernel. -/
theorem rank_kernel_add_image (f : J →* S) (A : Subgroup J)
    [IsElementaryAbelian 2 A] :
    rank (A ⊓ f.ker) + rank (A.map f) = rank A := by
  have h := rank_add_log_index A (A ⊓ f.ker) inf_le_left
  rw [inf_comm A f.ker, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker] at h
  simpa only [inf_comm f.ker A, rank] using h

/-- The extra layer above `Dγ ∩ V_H` makes the three displayed
contributions strictly smaller than `m(Uγ)`. Both quotient contributions
are images of the specified subgroups under the specified maps. -/
theorem strict_filtration_rank (π : J →* S) (q : J →* P)
    (A V C : Subgroup J) [IsElementaryAbelian 2 A]
    (hUV : q.ker ≤ V) (hVC : V ≤ C) (hDC : ¬ A ⊓ π.ker ≤ C) :
    rank (A.map π) + rank (((A ⊓ π.ker) ⊓ V).map q) +
      rank ((A ⊓ π.ker) ⊓ q.ker) < rank A := by
  let D := A ⊓ π.ker
  let E := D ⊓ V
  let _ : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le inf_le_left
  let _ : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hED : E < D := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    apply hDC
    change D ≤ C
    rw [← he]
    exact inf_le_right.trans hVC
  have hstrict := rank_lt_of_lt hED
  have hA := rank_kernel_add_image π A
  have hE := rank_kernel_add_image q E
  have hker : E ⊓ q.ker = D ⊓ q.ker := by
    dsimp [E]
    rw [inf_assoc, inf_eq_right.mpr hUV]
  rw [hker] at hE
  change rank D + rank (A.map π) = rank A at hA
  change rank (A.map π) + rank (E.map q) + rank (D ⊓ q.ker) < rank A
  omega

omit [Finite J] in
/-- Noncommutation in the actual quotient forces `Dγ ≰ H_C` when
the corresponding commutators lift into `Dγ H_C`. -/
theorem not_le_kernel_of_noncentral_image (f : J →* S) (D X A : Subgroup J)
    (hcomm : ⁅X, A⁆ ≤ D ⊔ f.ker)
    (hnoncentral : ¬ X.map f ≤ Subgroup.centralizer (A.map f : Set S)) :
    ¬ D ≤ f.ker := by
  intro hD
  have hc : ⁅X, A⁆ ≤ f.ker := hcomm.trans (sup_le hD le_rfl)
  have hz : (⁅X, A⁆).map f = ⊥ := by
    apply le_antisymm _ bot_le
    exact (Subgroup.map_le_iff_le_comap).mpr hc
  rw [Subgroup.map_commutator] at hz
  exact hnoncentral (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz)

/-- A quotient of dimension at most seven by a line has binary rank at
most eight. Here the quotient is the actual subgroup quotient `U/Z`. -/
theorem rank_le_eight_of_quotient (U Z : Subgroup J) [IsElementaryAbelian 2 U]
    (hZU : Z ≤ U) (hZ : Nat.card Z = 2)
    (hdim : Module.finrank (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) ≤ 7) :
    rank U ≤ 8 := by
  have hr := rank_add_log_index U Z hZU
  rw [Subgroup.log_relIndex_eq_quotient_finrank] at hr
  have hz : rank Z = 1 := by
    change Nat.log 2 (Nat.card Z) = 1
    rw [hZ]
    simpa only [pow_one] using Nat.log_pow Nat.one_lt_two 1
  omega

/-- Assembly of the filtration with its three independently supplied
model contributions. An actual ambient conjugator compares `Uγ` and
`U_H`; equality of their ranks is proved from it. -/
theorem no_small_conjugate_filtration {G : Type*} [Group G]
    (i : J →* G) (hi : Function.Injective i) (g : G)
    (π : J →* S) (q : J →* P) (A V C : Subgroup J)
    [IsElementaryAbelian 2 A]
    (hconj : A.map i = (q.ker.map i).map (MulAut.conj g).toMonoidHom)
    (hUV : q.ker ≤ V) (hVC : V ≤ C) (hDC : ¬ A ⊓ π.ker ≤ C)
    (hactor : 2 ≤ rank (A.map π))
    (hmiddle : 3 ≤ rank (((A ⊓ π.ker) ⊓ V).map q))
    (hbottom : 3 ≤ rank ((A ⊓ π.ker) ⊓ q.ker))
    (hupper : rank q.ker ≤ 8) : False := by
  have hs := strict_filtration_rank π q A V C hUV hVC hDC
  have he : rank A = rank q.ker := by
    have hc := congrArg rank hconj
    rw [rank_map_conj] at hc
    simpa only [rank, Subgroup.card_map_of_injective hi] using hc
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2
