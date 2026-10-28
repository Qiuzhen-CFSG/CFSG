module
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.PGroupCore
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Alternating-six sections under solvable homomorphism kernels

A quasisimple two-core quotient has solvable radical equal to the preimage
of its center. The quotient by this radical is preserved under every
surjection with solvable kernel. Thus an alternating-six section retains
its order divisor 360 and three-rank at least two in the image. The rank
argument uses cyclicity of odd-prime Sylow subgroups at rank one, without
asserting general rank invariance under central quotients.

The application to the original star maps in C.2.7 is in
`CentralSixStarModels`; it retains the triple-cover case of
Aschbacher--Smith 12.3.6, printed p.809.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.Alternating.SixSolvableSection
variable {B D : Type*} [Group B] [Finite B] [Group D] [Finite D]

theorem radical_eq_centralPreimage [IsQuasisimple (B ⧸ pCore 2 B)] :
    solvableRadical B = centralPreimage (pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 B)
  let : Group.IsSolvable q.ker := by
    dsimp only [q]
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
    infer_instance
  rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _)]
  have he : solvableRadical (B ⧸ pCore 2 B) = center (B ⧸ pCore 2 B) :=
    le_antisymm IsQuasisimple.solvableRadical_le_center
      (le_solvableRadical _ inferInstance inferInstance)
  rw [he]
  rfl

noncomputable def imageEquiv
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (f : B →* D) [Group.IsSolvable f.ker] :
    (f.range ⧸ solvableRadical f.range) ≃* alternatingGroup (Fin 6) := by
  have he : f.rangeRestrict.ker = f.ker := by ext x; exact Subtype.ext_iff
  let : Group.IsSolvable f.rangeRestrict.ker := he.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
  exact (solvableRadicalQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective).symm.trans e

omit [Finite B] in
theorem card_dvd
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6)) :
    360 ∣ Nat.card B := by
  have hd := card_dvd_of_surjective (QuotientGroup.mk' (solvableRadical B))
    (QuotientGroup.mk'_surjective _)
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd
  exact hd

theorem rank_ge_two
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6)) :
    2 ≤ primeRank 3 B := by
  by_contra! hr
  let P : Sylow 3 B := Classical.choice inferInstance
  have h := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega))
    (e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical B)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)] at h
  omega

theorem image_card_dvd
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (f : B →* D) [Group.IsSolvable f.ker] : 360 ∣ Nat.card f.range :=
  card_dvd (imageEquiv e f)

theorem image_rank_ge_two
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (f : B →* D) [Group.IsSolvable f.ker] : 2 ≤ primeRank 3 f.range :=
  rank_ge_two (imageEquiv e f)

end Theory.Alternating.SixSolvableSection
