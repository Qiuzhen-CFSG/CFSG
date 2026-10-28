module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The elementary envelope in Thompson factorization

For a near-maximum elementary subgroup B of S, a two-subgroup Q of S
containing B, and an actor N normalizing Q, construct the literal module
V = Omega1 Z(Omega1(C_Q(<B^N>))). Rank enlargement puts its involution
generators in J1(S), which forces Omega1 Z(J1(S)) into V once it lies in Q.
The module V is normalized by N; counting the elementary join VB shows
that every elementary overgroup A of B fixes a subgroup of index at most two
in V.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153; Aschbacher–Smith,
B.2.2–3 for the Thompson families. The remaining choice of Q, B and N is
kept separate from these explicit constructions.
-/

public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

private theorem enlarged_max (S B D : Subgroup G)
    (hB : B ∈ thompsonFamily S 1) (hDS : D ≤ S)
    [IsElementaryAbelian 2 D] (hDB : D ≤ centralizer (B : Set G)) (hne : ¬ D ≤ B) :
    B ⊔ D ∈ elementaryAbelianMaxSubgroups S := by
  let : IsElementaryAbelian 2 B := hB.2.1
  have he : IsElementaryAbelian 2 (B ⊔ D : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hDB
  have hi : B.relIndex (B ⊔ D) ≠ 1 := fun h =>
    hne (le_sup_right.trans (relIndex_eq_one.mp h))
  have hip : 0 < B.relIndex (B ⊔ D) := Nat.pos_of_ne_zero
    (index_ne_zero_of_finite (H := B.subgroupOf (B ⊔ D)))
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) B (B ⊔ D) bot_le le_sup_left
  simp only [relIndex_bot_left] at hc
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hb : Nat.card B * 2 = Nat.card A := by
    rw [hB.2.2.2,elementaryAbelianMaxSubgroups_card_eq S A hA,maxOrder_eq_two_pow_rank]
    rw [←pow_succ]
    congr 1
    have := hB.2.2.1
    omega
  refine ⟨sup_le hB.1 hDS,he,fun C hCS hCe => (hA.2.2 C hCS hCe).trans ?_⟩
  rw [←hb,←hc]
  exact Nat.mul_le_mul_left _ (by omega)

theorem omega_centralizer_nearMax_le_thompson_one (S B : Subgroup G)
    (hr : 1 < twoRank S) (hB : B ∈ thompsonFamily S 1) :
    omegaOneAmbient (S ⊓ centralizer (B : Set G)) ≤ thompsonJ S 1 := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hp
  by_cases hxb : x ∈ B
  · exact (le_sSup hB) hxb
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hp
  have hm := enlarged_max S B (zpowers x) hB (zpowers_le.mpr hx.1)
    (zpowers_le.mpr hx.2) (fun hh => hxb (hh (mem_zpowers x)))
  have hle : B ⊔ zpowers x ≤ thompsonJ S 0 := by rw [thompsonJ_zero]; exact le_sSup hm
  exact (le_sup_right.trans (hle.trans (lemma_B_2_3_1 S (by omega) hr))) (mem_zpowers x)

/-- The elementary module constructed in GLS G.26.18 contains the original
Thompson omega-center, using the actual conjugates of the chosen hyperplane. -/
theorem thompson_one_le_characteristic_envelope
    (S Q N B : Subgroup G) (hr : 1 < twoRank S)
    (hB : B ∈ thompsonFamily S 1) (hBQ : B ≤ Q) (hQS : Q ≤ S)
    (hNQ : N ≤ normalizer (Q : Set G))
    (hEQ : omegaOneCenterAmbient (thompsonJ S 1) ≤ Q) :
    omegaOneCenterAmbient (thompsonJ S 1) ≤
      omegaOneCenterAmbient (omegaOneAmbient
        (Q ⊓ centralizer (conjugateSpanBy B N : Set G))) := by
  let E := omegaOneCenterAmbient (thompsonJ S 1)
  let D := conjugateSpanBy B N
  let C := omegaOneAmbient (Q ⊓ centralizer (D : Set G))
  have hDJ : D ≤ thompsonJ S 1 := by
    apply (closure_le _).mpr
    rintro x ⟨n,hn,b,hb,rfl⟩
    let : IsElementaryAbelian 2 B := hB.2.1
    have hm : B.map (MulAut.conj n).toMonoidHom ∈ thompsonFamily S 1 := by
      refine ⟨?_,IsElementaryAbelian.map (MulAut.conj n).toMonoidHom,hB.2.2.1,?_⟩
      · exact (map_mono hBQ).trans ((mem_normalizer_iff_map_conj_eq.mp (hNQ hn)).le.trans hQS)
      · rw [card_map_of_injective (MulAut.conj n).injective]
        exact hB.2.2.2
    exact (le_sSup hm) (mem_map_of_mem (MulAut.conj n).toMonoidHom hb)
  have hEC : E ≤ C := by
    intro e he
    have hh := (mem_omegaOneCenterAmbient_iff _ _).mp he
    exact (omegaOneAmbient_le_iff _ C).mp le_rfl e
      ⟨hEQ he,centralizer_le hDJ (mem_centralizer_iff.mpr hh.2.2)⟩ hh.2.1
  have hCJ : C ≤ thompsonJ S 1 :=
    (omegaOneAmbient_mono (inf_le_inf hQS (centralizer_le (le_conjugateSpanBy B N)))).trans
      (omega_centralizer_nearMax_le_thompson_one S B hr hB)
  intro e he
  have hh := (mem_omegaOneCenterAmbient_iff _ _).mp he
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hEC he,hh.2.1,fun c hc => hh.2.2 c (hCJ hc)⟩
end CFSG.Quasithin.ChapterB

namespace CFSG.Quasithin.ChapterB
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]

@[expose] def factorizationEnvelope (Q B N : Subgroup G) : Subgroup G :=
  omegaOneCenterAmbient (omegaOneAmbient (Q ⊓ centralizer (conjugateSpanBy B N : Set G)))

omit [Finite G] in
theorem factorizationEnvelope_le (Q B N : Subgroup G) : factorizationEnvelope Q B N ≤ Q := by
  intro x hx
  exact ((omegaOneAmbient_le _ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)).1

omit [Finite G] in
theorem factorizationEnvelope_centralizes (Q B N : Subgroup G) :
    factorizationEnvelope Q B N ≤ centralizer (B : Set G) := by
  intro x hx
  exact centralizer_le (le_conjugateSpanBy B N)
    (omegaOneAmbient_le _ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1).2

omit [Finite G] in
private theorem normalizes_omega (U : Subgroup G) :
    normalizer (U : Set G) ≤ normalizer (omegaOneAmbient U : Set G) := by
  let : (omega₁ U (p := 2)).Characteristic := omega₁_characteristic U
  exact normalizer_le_normalizer_characteristic_image U (omega₁ U (p := 2))

omit [Finite G] in
private theorem normalizes_omega_center (U : Subgroup G) :
    normalizer (U : Set G) ≤ normalizer (omegaOneCenterAmbient U : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change U.map (MulAut.conj g).toMonoidHom = U at hg
  change (omegaOneCenterAmbient U).map (MulAut.conj g).toMonoidHom = _
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,hg]

omit [Finite G] in
theorem factorizationEnvelope_normalized (Q B N : Subgroup G)
    (hNQ : N ≤ normalizer (Q : Set G)) :
    N ≤ normalizer (factorizationEnvelope Q B N : Set G) :=
  ((le_inf hNQ ((le_normalizer_conjugateSpanBy B N).trans
    (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf).trans
      ((normalizes_omega _).trans (normalizes_omega_center _))

theorem factorizationEnvelope_fixed_index (S Q N B A : Subgroup G)
    (hB : B ∈ thompsonFamily S 1) (hQS : Q ≤ S)
    (hBA : B ≤ A) (hA : IsElementaryAbelian 2 A) :
    (centralizer (A : Set G)).relIndex (factorizationEnvelope Q B N) ≤ 2 := by
  let V := factorizationEnvelope Q B N
  let : IsElementaryAbelian 2 B := hB.2.1
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 V := omegaOneCenterAmbient_elementaryAbelian _
  have he : IsElementaryAbelian 2 (V ⊔ B : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp
      (factorizationEnvelope_centralizes Q B N))
  obtain ⟨E,hE⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hm := hE.2.2 (V ⊔ B) (sup_le ((factorizationEnvelope_le Q B N).trans hQS) hB.1) he
  have hb : Nat.card B * 2 = Nat.card E := by
    rw [hB.2.2.2,elementaryAbelianMaxSubgroups_card_eq S E hE,maxOrder_eq_two_pow_rank,←pow_succ]
    congr 1
    have := hB.2.2.1
    omega
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes V B
    ((le_centralizer_iff.mp (factorizationEnvelope_centralizes Q B N)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (V ⊓ B) V bot_le inf_le_left
  simp only [relIndex_bot_left,inf_relIndex_left] at hi
  have hidx : B.relIndex V ≤ 2 := by
    have hh := calc
      Nat.card V * Nat.card B = Nat.card (V ⊓ B : Subgroup G) * Nat.card (V ⊔ B : Subgroup G) := hp
      _ ≤ Nat.card (V ⊓ B : Subgroup G) * (Nat.card B * 2) := Nat.mul_le_mul_left _ (hb ▸ hm)
    rw [←hi] at hh
    have hc : (Nat.card (V ⊓ B : Subgroup G) * Nat.card B) * B.relIndex V ≤
        (Nat.card (V ⊓ B : Subgroup G) * Nat.card B) * 2 := by nlinarith [hh]
    exact (mul_le_mul_iff_right₀ (Nat.mul_pos Nat.card_pos Nat.card_pos)).mp hc
  have hBC : B ≤ centralizer (A : Set G) := hBA.trans A.le_centralizer
  exact (relIndex_le_of_le_left hBC (B.subgroupOf V).index_ne_zero_of_finite).trans hidx
end CFSG.Quasithin.ChapterB
