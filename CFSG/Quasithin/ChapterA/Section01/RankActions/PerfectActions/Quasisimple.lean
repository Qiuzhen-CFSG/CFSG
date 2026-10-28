module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.Inputs
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.PrimeRankSylow

/-!
# The quasisimple quotient deduction in A.1.29

A surjection onto SL₂(r), r prime and r > 3, kills the odd core. If the
quotient by that core is quasisimple, its proper normal kernel is central.
The precise prime-field cover-rigidity input makes that induced map injective.
Thus the original kernel is the odd core. Its Sylow two-subgroups are
isomorphic to those of the image, giving two-rank one.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.29(2), printed p.27, using I.1.3. The latter's exact universal input
remains explicit and belongs to the existing Chapter I assembly owner.
-/

open Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterA.RankActions
open Theory.GroupTheory
private theorem rank_of_odd_kernel_SL2
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hp : 2 < p) (f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Surjective f) (hk : Nat.Coprime 2 (Nat.card f.ker)) :
    primeRank 2 A = 1 := by
  let P : Sylow 2 A := Classical.choice inferInstance
  let Q : Sylow 2 SL(2,ZMod p) := Classical.choice inferInstance
  rw [P.primeRank_eq, primeRank_equiv 2 (P.equivOfSurjectiveCoprime f hf hk Q),
    ← Q.primeRank_eq]
  apply SpecialLinearGroup.primeRank_two_eq_one
  intro he
  exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp
    ((ZMod.natCast_eq_zero_iff 2 p).mp he)
end CFSG.Quasithin.ChapterA.RankActions

namespace CFSG.Quasithin.ChapterA.RankActions
open Theory.GroupTheory
universe u
/-- A prime-field SL₂ image of a group with quasisimple odd-core quotient
has exactly the odd core as kernel, using the specified cover rigidity.
The resulting coprime quotient also identifies its two-rank. -/
public theorem oddCore_eq_kernel_of_quasisimple_SL2_image
    (hrigid : PrimeSL2CoverRigidity.{u})
    {A : Type u} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (f : A →* SL(2,ZMod p)) (hf : Function.Surjective f)
    [IsQuasisimple (A ⧸ pPrimeCore 2 A)] :
    pPrimeCore 2 A = f.ker ∧ primeRank 2 A = 1 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp he)
  have hO : pPrimeCore 2 A ≤ f.ker := by
    let : ((pPrimeCore 2 A).map f).Normal :=
      (inferInstance : (pPrimeCore 2 A).Normal).map f hf
    have hd : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 A).map f)) :=
      (pPrimeCore_coprime_card (p := 2) (G := A)).of_dvd_right (card_map_dvd _ f)
    have hle : (pPrimeCore 2 A).map f ≤ pPrimeCore 2 SL(2,ZMod p) :=
      le_sSup ⟨inferInstance, hd⟩
    rw [SpecialLinearGroup.pPrimeCore_two_eq_bot htwo] at hle
    intro x hx
    exact hle (mem_map_of_mem f hx)
  let g := QuotientGroup.lift (pPrimeCore 2 A) f hO
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := hf x
    exact ⟨QuotientGroup.mk' (pPrimeCore 2 A) a, rfl⟩
  have hk : g.ker ≤ center (A ⧸ pPrimeCore 2 A) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top g.ker with hh | hh
    · exact hh
    · have he := MonoidHom.ker_eq_top_iff.mp hh
      obtain ⟨a, ha⟩ := hg (-1)
      have hz : (-1 : SL(2,ZMod p)) = 1 := by rw [← ha, he]; rfl
      have ho := SpecialLinearGroup.orderOf_neg_one_eq_two htwo
      rw [hz, orderOf_one] at ho
      contradiction
  have hi := hrigid p hp (A ⧸ pPrimeCore 2 A) g hg hk
  have heq : pPrimeCore 2 A = f.ker := by
    apply le_antisymm hO
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply hi
    exact hx.trans g.map_one.symm
  refine ⟨heq, rank_of_odd_kernel_SL2 (by omega) f hf ?_⟩
  rw [← heq]
  exact pPrimeCore_coprime_card
end CFSG.Quasithin.ChapterA.RankActions
