module

public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms


/-!
# Two-ranks of Suzuki groups and their automorphism groups

The central root matrices form an elementary subgroup of order q. Every
square-one element in the standard Sylow subgroup has first root coordinate
zero, so an elementary subgroup has at most q elements. Thus Sz(q) has
two-rank log₂(q). Every square-one automorphism is inner by the proved odd
outer-index theorem, giving the same upper bound for the full automorphism
group. Faithful descent gives this bound for every perfect central cover.

Source: Huppert–Blackburn III, XI.3.1 and XI.3.3; GLS IV, Chapter 4,
Lemma 3.4; Aschbacher–Smith 16.3.9, printed p.1180. In particular the Sz(8)
automorphism bound is three, as also needed in the Rudvalis branch.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups
open PFAppendixIII

private theorem root_coordinates (m : ℕ) (hm : 0 < m) :
    (∀ a b a' b' : BinaryGaloisField (2*m+1),
      SuzukiRootGL m a b * SuzukiRootGL m a' b' =
        SuzukiRootGL m (a+a') (b+b'+a*(iterateFrobeniusEquiv _ 2 (m+1)) a')) := by
  let pi := iterateFrobeniusEquiv (BinaryGaloisField (2*m+1)) 2 (m+1)
  have hp := iterateFrobeniusEquiv_def (BinaryGaloisField (2*m+1)) 2 (m+1)
  exact (External.huppert_blackburn_XI_3_1 m hm pi
    (External.binaryGaloisField_tits_formula_sq m pi hp)).2.2.2.2.2.2.2.2.1

private theorem first_zero (m : ℕ) (x : SuzukiMatrixGroup m)
    (hx : x ^ 2 = 1) (a b : BinaryGaloisField (2*m+1))
    (he : x.val = SuzukiRootGL m a b) : a = 0 := by
  have h := congrArg (fun y : SuzukiMatrixGroup m => y.val (0 : Fin 4) (2 : Fin 4)) hx
  have hab : a * a ^ (2 ^ (m + 1)) = 0 := by
    have heq : b + (a * a ^ (2 ^ (m + 1)) + b) = 0 := by
      simpa [pow_two, he, SuzukiRootGL, SuzukiRootMatrix,
        Matrix.mul_apply, Fin.sum_univ_four, add_assoc] using h
    have hc : b + (a * a ^ (2 ^ (m + 1)) + b) = a * a ^ (2 ^ (m + 1)) := by
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    rwa [hc] at heq
  rcases mul_eq_zero.mp hab with ha | ha
  · exact ha
  · exact eq_zero_of_pow_eq_zero ha

/-- Exact two-rank of the concrete Suzuki matrix group. -/
theorem suzuki_two_rank (m : ℕ) (hm : 0 < m) :
    primeRank 2 (SuzukiMatrixGroup m) = 2*m+1 := by
  let F := BinaryGaloisField (2*m+1)
  have hF : Nat.card F = 2 ^ (2*m+1) := GaloisField.card 2 (2*m+1) (by omega)
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  apply le_antisymm
  · rw [P.primeRank_eq, hP]
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E hE
    let := hE
    have hcoords (x : E) : ∃ b : F, x.val.val.val = SuzukiRootGL m 0 b := by
      obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m x.val.val).mp x.val.property
      have hx : x.val.val ^ 2 = 1 := by
        exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian _ x.property)
      have ha := first_zero m _ hx a b hab
      exact ⟨b, ha ▸ hab⟩
    choose coord hcoord using hcoords
    have hi : Function.Injective coord := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [hcoord x, hcoord y, hxy]
    rw [← hF]
    exact Nat.card_le_card_of_injective coord hi
  · let f : Multiplicative F →* SuzukiMatrixGroup m :=
      { toFun := fun c => ⟨SuzukiRootGL m 0 c.toAdd,
          subset_closure (Or.inl ⟨0, c.toAdd, rfl⟩)⟩
        map_one' := Subtype.ext (External.suzukiRootGL_zero_zero m)
        map_mul' := fun c d => by
          apply Subtype.ext
          symm
          simpa using root_coordinates m hm 0 c.toAdd 0 d.toAdd }
    have hf : Function.Injective f := by
      intro c d h
      have he := congrArg (fun y : SuzukiMatrixGroup m => y.val (0 : Fin 4) (2 : Fin 4)) h
      simpa [f, SuzukiRootGL, SuzukiRootMatrix] using he
    have hp (c : Multiplicative F) : c ^ 2 = 1 := by
      rw [pow_two]
      change Multiplicative.ofAdd (c.toAdd+c.toAdd) = Multiplicative.ofAdd 0
      rw [CharTwo.add_self_eq_zero]
    exact primeRank_ge_of_elementary_embedding hp hF f hf

/-- Automorphism two-rank does not exceed the Suzuki factor rank. -/
theorem suzuki_automorphism_two_rank (m : ℕ) (hm : 0 < m) :
    primeRank 2 (MulAut (SuzukiMatrixGroup m)) ≤ 2*m+1 := by
  let S := SuzukiMatrixGroup m
  have hcenter : center S = ⊥ := by
    have hmodel : IsSimpleBenderGroup S := .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
    let := hmodel.isSimple
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hmodel.not_commutative (fun x y => by
        have hx : x ∈ center S := by rw [h]; trivial
        exact (mem_center_iff.mp hx y).symm))
  let e : S ≃* (MulAut.conj : S →* MulAut S).range :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hcenter)
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  have hle : E ≤ (MulAut.conj : S →* MulAut S).range := by
    intro a ha
    obtain ⟨b, hb⟩ := ZD.suzuki_involutoryAut_inner_and_twoRank m hm a
      (elemPow_eq_one_of_isElementaryAbelian _ ha)
    exact ⟨b, hb.1.symm⟩
  have hEcard := (primeRank_le_iff_elementary_card_le (MulAut.conj : S →* MulAut S).range).mp
    (show primeRank 2 (MulAut.conj : S →* MulAut S).range ≤ 2*m+1 by
      rw [← primeRank_equiv 2 e, suzuki_two_rank m hm])
    (E.subgroupOf _) (IsElementaryAbelian.subgroupOf hle)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hEcard

end BenderSuzuki.MatrixGroups

namespace BenderSuzuki.MatrixGroups

/-- Faithful descent bounds automorphisms of every perfect Suzuki central cover. -/
theorem suzuki_cover_automorphism_two_rank {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {m : ℕ} (hm : 0 < m)
    (e : (L ⧸ center L) ≃* SuzukiMatrixGroup m) :
    primeRank 2 (MulAut L) ≤ 2*m+1 := by
  let f : PerfectCentralCovering.Cover L (SuzukiMatrixGroup m) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (hx.trans e.map_one.symm) }
  have hk : f.toMonoidHom.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  exact (primeRank_le_of_injective 2 (f.autMap hk) (f.autMap_injective hk)).trans
    (suzuki_automorphism_two_rank m hm)

/-- The reusable Sz(8) bound, also needed in the Rudvalis branch. -/
theorem suzuki_eight_automorphism_two_rank :
    primeRank 2 (MulAut (SuzukiMatrixGroup 1)) ≤ 3 :=
  suzuki_automorphism_two_rank 1 (by decide)

end BenderSuzuki.MatrixGroups
