module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.SingerExclusion
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.LinearFrame.SpecialLinear
public import Theory.SpecificGroups.SL3.SplitMonomial.EvenThreeCore
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Invariant linear frames for nonabelian odd special-unitary subgroups

Odd order gives solvability of H, and its cyclic normalizing supplement gives
solvability of H⟨t⟩. In the faithful SL₃ realization, Fitting
self-centralization says that absence of a noncentral abelian normal subgroup
forces a nonabelian normal three-subgroup. The characteristic-two three-core
theorem supplies an abelian subgroup normal in the join and not contained in
the scalar center. Singer exclusion and Clifford theory then construct a basis
over the original field whose lines the whole join permutes. The faithful
special-linear realization transports this frame back to the original
special-unitary action, retaining the given involution and all scalar matrices.

The conditional reduction is preserved, and the final theorem discharges its
three-core premise. The fixed-field order and no-Borel hypotheses belong to
the source setup; the nonabelian linear-frame argument needs only the
matrix-field order. Orthogonality remains a separate geometric conclusion.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603; the Fitting reduction is shared
with the solvable case of GLS3, Theorem 6.5.3.
-/

public section
open Matrix BenderSuzuki.MatrixGroups Representation Subgroup
open scoped IsMulCommutative
namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame
variable {E : Type*} [Field E]

/-- The complete reduction to the nonabelian normal three-subgroup case. The
extra premise must produce a noncentral abelian normal subgroup for each such
Q in the actual SL₃ join; it is not supplied by the normalizer order bound.
The final `exists_preserved_linear_frame` below discharges this premise using
the characteristic-two three-core theorem. -/
theorem exists_preserved_linear_frame_of_three_core [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (hna : ¬ IsMulCommutative H) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H)
    (hcore : ∀ Q : Subgroup (SpecialLinearGroup (Fin 3) E),
      Q ≤ H.map (specialLinearEmbedding J) ⊔ zpowers (specialLinearEmbedding J t) →
      (Q.subgroupOf (H.map (specialLinearEmbedding J) ⊔
        zpowers (specialLinearEmbedding J t))).Normal →
      IsPGroup 3 Q → ¬ IsMulCommutative Q →
      SL3.SplitMonomial.HasNoncentralAbelianNormal
        (H.map (specialLinearEmbedding J) ⊔ zpowers (specialLinearEmbedding J t))) :
    ∃ C : GL (Fin 3) E, PreservesLines J (H ⊔ zpowers t) C := by
  let f := specialLinearEmbedding J
  let H' := H.map f
  let t' := f t
  let K := H' ⊔ zpowers t'
  have hf : Function.Injective f := specialLinearEmbedding_injective J
  have hodd' : Odd (Nat.card H') := by
    change Odd (Nat.card (H.map f))
    rwa [card_map_of_injective hf]
  have hna' : ¬ IsMulCommutative H' := by
    intro hcomm
    let : IsMulCommutative H' := hcomm
    apply hna
    refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => hf ?_
    simpa only [map_mul] using
      (setLike_mul_comm (mem_map_of_mem f ha) (mem_map_of_mem f hb))
  have htH' : t' ∈ normalizer H' := H.le_normalizer_map f (mem_map_of_mem f htH)
  let : Group.IsSolvable H' := odd_order_theorem H' hodd'
  have hs : Group.IsSolvable K := Group.isSolvable_sup_of_normalizes H' (zpowers t')
    (zpowers_le.mpr htH')
  have hnK : ¬ IsMulCommutative K := by
    intro hcomm
    let : IsMulCommutative K := hcomm
    apply hna'
    exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (show a ∈ K from (show H' ≤ K from le_sup_left) ha)
        (show b ∈ K from (show H' ≤ K from le_sup_left) hb)
  have hA : SL3.SplitMonomial.HasNoncentralAbelianNormal K := by
    by_contra hno
    obtain ⟨Q, hQK, hQn, hQ, hQna⟩ :=
      SL3.SplitMonomial.exists_nonabelian_normal_three_of_not_hasNoncentralAbelianNormal
        K hs hnK hno
    exact hno (hcore Q hQK hQn hQ hQna)
  apply exists_preserved_linear_frame_of_specialLinear_abelian_normal
    J n hcard H hodd hna t ht
  rwa [specialLinearEmbedding_map_join]

/-- The nonabelian odd subgroup and its given normalizing involution preserve
the projective column lines of a matrix over the original field. This is the
linear-frame construction for GLS4, Chapter 4, Lemma 3.11(a); orthogonality and
the remaining torus conclusions are assembled separately. -/
theorem exists_preserved_linear_frame [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (_hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (_hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (hna : ¬ IsMulCommutative H) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (_hB : SpecialNoBorel J H) :
    ∃ C : GL (Fin 3) E, PreservesLines J (H ⊔ zpowers t) C := by
  let : CharP E 2 := charTwo_of_card n hcard
  have hf := specialLinearEmbedding_injective J
  have hodd' : Odd (Nat.card (H.map (specialLinearEmbedding J))) := by
    rwa [card_map_of_injective hf]
  have ht' : orderOf (specialLinearEmbedding J t) = 2 :=
    (orderOf_injective (specialLinearEmbedding J) hf t).trans ht
  have htH' : specialLinearEmbedding J t ∈ normalizer (H.map (specialLinearEmbedding J)) :=
    H.le_normalizer_map (specialLinearEmbedding J) (mem_map_of_mem (specialLinearEmbedding J) htH)
  apply exists_preserved_linear_frame_of_three_core J n hcard H hodd hna t ht htH
  intro Q hQK hQn hQ hQna
  exact SL3.SplitMonomial.hasNoncentralAbelianNormal_of_odd_involution_normal_three
    (H.map (specialLinearEmbedding J)) hodd' (specialLinearEmbedding J t) ht' htH'
    Q hQK hQn hQ hQna

end UnitaryThree.OddTorusNormalizer.NonabelianFrame
