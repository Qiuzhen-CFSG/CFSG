module
public import Theory.GroupTheory.AutomorphismSylowNormalizer
public import Mathlib.GroupTheory.Index

/-!
# Normalizers of exchanged subgroups of index at most two

In a product of two Sylow two-subgroups of the same finite group, an
index-at-most-two subgroup with equally sized coordinate projections
projects onto both Sylows. Otherwise both projections have at most half
the Sylow order, contradicting the index bound. An automorphism exchanging
the two coordinates and preserving the subgroup supplies this equality.

If the factor Sylows are self-normalizing, the subgroup's normalizer is
therefore contained in the product Sylow. Together with two-group outer
automorphisms, this makes any subgroup-preserving action a two-group.
Source application: Aschbacher--Smith 10.2.5, printed p.748, retaining the
actual exchanger and literal index bound on R = T₁ ∩ K.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SylowNormalizerAction
variable {Q : Type*} [Group Q] [Finite Q]

private theorem sylow_prod (S : Sylow 2 (Q × Q)) :
    (S : Subgroup (Q × Q)) = ((S : Subgroup _).map (MonoidHom.fst Q Q)).prod
      ((S : Subgroup _).map (MonoidHom.snd Q Q)) := by
  let A := S.mapSurjective (f := MonoidHom.fst Q Q) (fun q => ⟨(q,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd Q Q) (fun q => ⟨(1,q),rfl⟩)
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a,ha⟩ := A.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := B.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+b)
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
    change Nat.card A * Nat.card B = 2^(a+b)
    rw [ha,hb,pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

/-- Equal coordinate sizes and index at most two force both Sylow projections to be full. -/
theorem projections_full (S : Sylow 2 (Q × Q)) (U : Subgroup (Q × Q))
    (hUS : U ≤ (S : Subgroup _)) (hi : U.relIndex (S : Subgroup _) ≤ 2)
    (he : Nat.card (U.map (MonoidHom.fst Q Q)) = Nat.card (U.map (MonoidHom.snd Q Q))) :
    U.map (MonoidHom.fst Q Q) = (S : Subgroup _).map (MonoidHom.fst Q Q) ∧
      U.map (MonoidHom.snd Q Q) = (S : Subgroup _).map (MonoidHom.snd Q Q) := by
  let A := S.mapSurjective (f := MonoidHom.fst Q Q) (fun q => ⟨(q,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd Q Q) (fun q => ⟨(1,q),rfl⟩)
  let V := U.map (MonoidHom.fst Q Q)
  let W := U.map (MonoidHom.snd Q Q)
  have hab : Nat.card A = Nat.card B := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hVA : V ≤ (A : Subgroup Q) := map_mono hUS
  have hWB : W ≤ (B : Subgroup Q) := map_mono hUS
  have hsizeS : Nat.card S = Nat.card A * Nat.card A := by
    rw [sylow_prod S,Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
    exact congrArg (Nat.card A * ·) hab.symm
  have hsizeU : Nat.card U ≤ Nat.card V * Nat.card V := by
    have hh : U ≤ V.prod W := fun x hx => ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩
    have hc := card_le_of_le hh
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,←he] at hc
    exact hc
  have hindex : Nat.card U * U.relIndex (S : Subgroup _) = Nat.card S := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (Q × Q)) U (S : Subgroup _) bot_le hUS
    simpa only [relIndex_bot_left] using hh
  have hlarge : Nat.card A * Nat.card A ≤ 2 * (Nat.card V * Nat.card V) := by
    rw [←hsizeS,←hindex]
    nlinarith
  have hcard : Nat.card V = Nat.card A := by
    by_contra hn
    have hcard' := card_le_of_le hVA
    have hmul : Nat.card V * V.relIndex (A : Subgroup Q) = Nat.card A := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup Q) V (A : Subgroup Q) bot_le hVA
      simpa only [relIndex_bot_left] using hh
    have hj : 2 ≤ V.relIndex (A : Subgroup Q) := by
      have hz : V.relIndex (A : Subgroup Q) ≠ 0 := Subgroup.index_ne_zero_of_finite
      by_contra hl
      have hone : V.relIndex (A : Subgroup Q) = 1 := by omega
      simp only [hone,mul_one] at hmul
      exact hn hmul
    have hv : 0 < Nat.card V := Nat.card_pos
    have htw : 2 * Nat.card V ≤ Nat.card A := by nlinarith
    nlinarith [sq_nonneg (Nat.card A - 2 * Nat.card V : ℤ)]
  change Nat.card V = Nat.card W at he
  constructor
  · exact eq_of_le_of_card_ge hVA hcard.ge
  · exact eq_of_le_of_card_ge hWB (by change Nat.card B ≤ Nat.card W; omega)


omit [Finite Q] in
/-- An actual exchanging automorphism gives equal projection cardinalities. -/
theorem projection_card_eq_of_swapped (U : Subgroup (Q × Q)) (a b : MulAut Q)
    (hs : U.map (a.prodCongr b * (MulEquiv.prodComm : MulAut (Q × Q))).toMonoidHom = U) :
    Nat.card (U.map (MonoidHom.fst Q Q)) = Nat.card (U.map (MonoidHom.snd Q Q)) := by
  have he := congrArg (Subgroup.map (MonoidHom.fst Q Q)) hs
  rw [Subgroup.map_map] at he
  have hh : (MonoidHom.fst Q Q).comp
      (a.prodCongr b * (MulEquiv.prodComm : MulAut (Q × Q))).toMonoidHom =
        a.toMonoidHom.comp (MonoidHom.snd Q Q) := rfl
  rw [hh,←Subgroup.map_map] at he
  rw [←he,card_map_of_injective a.injective]

/-- Self-normalizing factor Sylows bound the normalizer of the original subgroup. -/
theorem normalizer_le_of_projections_full
    (hN : ∀ S : Sylow 2 Q, normalizer (S : Set Q) = (S : Subgroup Q))
    (S : Sylow 2 (Q × Q)) (U : Subgroup (Q × Q))
    (hUS : U ≤ (S : Subgroup _)) (hi : U.relIndex (S : Subgroup _) ≤ 2)
    (he : Nat.card (U.map (MonoidHom.fst Q Q)) = Nat.card (U.map (MonoidHom.snd Q Q))) :
    normalizer (U : Set (Q × Q)) ≤ (S : Subgroup (Q × Q)) := by
  obtain ⟨hfirst,hsecond⟩ := projections_full S U hUS hi he
  intro x hx
  rw [sylow_prod S]
  have ha := le_normalizer_map (MonoidHom.fst Q Q) (mem_map_of_mem _ hx)
  have hb := le_normalizer_map (MonoidHom.snd Q Q) (mem_map_of_mem _ hx)
  rw [hfirst] at ha
  rw [hsecond] at hb
  have hnA : normalizer ((S : Subgroup _).map (MonoidHom.fst Q Q) : Set Q) =
      (S : Subgroup _).map (MonoidHom.fst Q Q) :=
    hN (S.mapSurjective (f := MonoidHom.fst Q Q) (fun q => ⟨(q,1),rfl⟩))
  have hnB : normalizer ((S : Subgroup _).map (MonoidHom.snd Q Q) : Set Q) =
      (S : Subgroup _).map (MonoidHom.snd Q Q) :=
    hN (S.mapSurjective (f := MonoidHom.snd Q Q) (fun q => ⟨(1,q),rfl⟩))
  rw [hnA] at ha
  rw [hnB] at hb
  exact ⟨ha,hb⟩

variable {A : Type*} [Group A]
omit [Finite Q] in
/-- A two-group normalizer and two-group outer group force a two-group action image. -/
theorem action_two_of_normalizer_two
    (U : Subgroup Q) (hN : IsPGroup 2 (normalizer (U : Set Q)))
    (ho : IsPGroup 2 (MulAut.Outer Q)) (f : A →* MulAut Q)
    (hf : ∀ a, U.map (f a).toMonoidHom = U) : IsPGroup 2 f.range := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  rintro ⟨a, b, rfl⟩
  obtain ⟨k,hk⟩ := ho (QuotientGroup.mk' (MulAut.innerSubgroup Q) (f b))
  have hi : (f b) ^ 2 ^ k ∈ MulAut.innerSubgroup Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (MulAut.innerSubgroup Q)) ((f b) ^ 2 ^ k) = 1
    rw [map_pow]
    exact hk
  obtain ⟨x,hx⟩ := hi
  have hxN : x ∈ normalizer (U : Set Q) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hx, ← map_pow]
    exact hf (b ^ 2 ^ k)
  obtain ⟨m,hm⟩ := hN (⟨x,hxN⟩ : normalizer (U : Set Q))
  refine ⟨k+m,?_⟩
  apply Subtype.ext
  change (f b) ^ 2 ^ (k+m) = 1
  rw [pow_add,pow_mul,←hx,←map_pow]
  have hxone : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [hxone,map_one]

end Theory.GroupTheory.SylowNormalizerAction
