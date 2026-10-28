module
public import Theory.SpecificGroups.Alternating.FiveChiefDegree
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.Commutator.SimpleSubnormal
/-!
# An A₅ moved subgroup survives central quotients

A perfect actor cannot act nontrivially only into a central kernel: the
three-subgroups identity removes such an action. The surviving image of the
original elementary binary subgroup therefore has at least sixteen elements
by the marked A₅ action bound.

Source application: Aschbacher–Smith, proof of 10.2.6, printed p.749.
-/
public section
open Subgroup
namespace alternatingGroup.FiveChiefDegree
variable {G : Type*} [Group G] [Finite G]
/-- A marked A₅ extension acting nontrivially on an elementary binary subgroup
forces two-rank at least four after every central quotient. -/
theorem four_le_twoRank_central_quotient
    (A U N : Subgroup G) [Group.IsPerfect A] [IsElementaryAbelian 2 U] [N.Normal]
    (hp : IsPPerfect 2 A) (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hAU : A ≤ normalizer (U : Set G)) (hne : ⁅U,A⁆ ≠ ⊥)
    (hN : N ≤ center G) : 4 ≤ primeRank 2 (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  let E := U.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hnorm : A.map q ≤ normalizer (E : Set (G ⧸ N)) :=
    (map_mono hAU).trans (U.le_normalizer_map q)
  let a : A →* normalizer (E : Set (G ⧸ N)) :=
    (q.comp A.subtype).codRestrict (normalizer (E : Set (G ⧸ N)))
      (fun x => hnorm (mem_map_of_mem q x.property))
  let f : A →* MulAut E := E.normalizerMonoidHom.comp a
  have hf : f ≠ 1 := by
    intro hf
    have hc : A.map q ≤ centralizer (E : Set (G ⧸ N)) := by
      rintro x ⟨b,hb,rfl⟩ y hy
      have hh := congrArg (fun z : MulAut E => (z ⟨y,hy⟩ : G ⧸ N))
        (DFunLike.congr_fun hf ⟨b,hb⟩)
      change q b * y * (q b)⁻¹ = y at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hz : (⁅U,A⁆ : Subgroup G).map q = ⊥ := by
      rw [map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
    have hcentral : ⁅U,A⁆ ≤ center G := by
      have hh := (map_eq_bot_iff (⁅U,A⁆ : Subgroup G)).mp hz
      rw [QuotientGroup.ker_mk'] at hh
      exact hh.trans hN
    have hzero : ⁅⁅U,A⁆,A⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      exact hcentral.trans (center_le_centralizer (A : Set G))
    exact hne (commutator_eq_bot_of_iterated_eq_bot U A hzero)
  have hcard : 16 ≤ Nat.card E :=
    sixteen_le_card_of_nontrivial_action hp e f hf (IsElementaryAbelian.isPGroup 2 E)
  by_contra! hr
  have hsmall : Nat.card E ≤ 2 ^ 3 :=
    (primeRank_le_iff_elementary_card_le (G ⧸ N)).mp (by omega : primeRank 2 (G ⧸ N) ≤ 3)
      E inferInstance
  norm_num at hsmall
  omega
end alternatingGroup.FiveChiefDegree
