module

public import Theory.GroupTheory.CentralizerRankMinimum
public import Theory.ElementaryAbelian.Basic

/-!
# C.6.3(2): rank of an escaping elementary abelian conjugate

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.6.3(2), printed pp. 166--167.

The source minimum is `Subgroup.centralizerRankMinimum R U`, the minimum
of the actual ranks of `U/A` with `A ≤ U` and `C_R(U) < C_R(A)`.
If `V = Uˣ` escapes `Q ≥ C_R(U)`, it does not centralize `U`. Thus
`C_R(V) < C_R(C_V(U))`, and the defining minimum bounds the rank of
`V/C_V(U)`. Conjugation by `x ∈ N_G(R)` preserves that minimum.

Only `R` is assumed finite; the ambient group remains arbitrary. All the
premises here are the local inputs used in the source proof of part (2).
-/

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC
open Subgroup

/-- C.6.3(2), with right conjugation `Uˣ = x⁻¹Ux` and the literal quotient
by `C_{Uˣ}(U)`. Finiteness of `U` and `Uˣ` is derived locally from finite `R`. -/
public theorem c6_3_rank_bound
    {G : Type*} [Group G] (R U Q : Subgroup G) [Finite R]
    [IsElementaryAbelian 2 U] (hUR : U ≤ R) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hescape : ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q)
    (hCQ : R ⊓ centralizer (U : Set G) ≤ Q) :
    let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
    let V := U.map (MulAut.conj x⁻¹ : G →* G)
    let : Finite V := Finite.of_equiv U ((MulAut.conj x⁻¹).subgroupMap U).toEquiv
    Group.rank (V ⧸ (centralizer (U : Set G)).subgroupOf V) ≥
      centralizerRankMinimum R U := by
  let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective hUR)
  let V := U.map (MulAut.conj x⁻¹ : G →* G)
  let : Finite V := Finite.of_equiv U ((MulAut.conj x⁻¹).subgroupMap U).toEquiv
  have hVR : V ≤ R := by
    have hh : R.map (MulAut.conj x⁻¹ : G →* G) = R :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
    exact (map_mono hUR).trans_eq hh
  have hnot : ¬ V ≤ centralizer (U : Set G) := by
    intro h
    exact hescape ((le_inf hVR h).trans hCQ)
  have hbound := centralizerRankMinimum_le R V (V ⊓ centralizer (U : Set G))
    inf_le_left (centralizer_lt_centralizer_inf_of_not_le R U V hUR hnot)
  have hsub : (V ⊓ centralizer (U : Set G)).subgroupOf V =
      (centralizer (U : Set G)).subgroupOf V := by
    ext v
    exact and_iff_right v.property
  rw [hsub, centralizerRankMinimum_conj R U hx] at hbound
  exact hbound

end CFSG.Quasithin.ChapterC
