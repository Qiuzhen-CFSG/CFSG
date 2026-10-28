module
public import Theory.SpecificGroups.Alternating.SevenFiveCover
public import Theory.SpecificGroups.AlternatingFiveCore
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Recovering the intrinsic two-core quotient from an A₅ image

Let a perfect finite group map onto A₇ with its literal O₂,Z kernel.
A perfect subgroup whose image is A₅ has intrinsic two-core quotient A₅.
After removing the ambient two-core, odd-rank-one transfer makes the
central projection injective on the perfect subgroup. The remaining
kernel is therefore a two-group, and the prime-core quotient comparison
identifies the requested intrinsic quotient.

No splitting of the ambient A₇ central cover is assumed. Source:
Aschbacher–Smith 12.2.7(2), printed p.797, used in 12.3.12, p.811.
The literal application is TerminalComponentProperSeven.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.SevenPerfectSylow

private theorem five_odd_rank (F : Type*) [Group F] [Finite F]
    (e : F ≃* alternatingGroup (Fin 5)) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p F ≤ 1 := by
  rw [primeRank_equiv p e,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 p hp (by
      intro he
      rw [he] at ho
      norm_num at ho)]
  have hthree : 3 ≤ p := by
    have htwo := hp.two_le
    have hne : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
    omega
  exact (Nat.div_le_div_left hthree (by decide)).trans (by decide : 5 / 3 ≤ 1)

theorem core_five_of_image_five
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (f : Y →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hker : f.ker = centralPreimage (pCore 2 Y))
    (B : Subgroup Y) [Group.IsPerfect B]
    (e : B.map f ≃* alternatingGroup (Fin 5)) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  let N := pCore 2 Y
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  let r := QuotientGroup.lift N f (hker.symm ▸ le_centralPreimage N)
  have hr : Function.Surjective r := by
    intro a
    obtain ⟨y,hy⟩ := hf a
    exact ⟨q y,hy⟩
  have hk : r.ker ≤ center (Y ⧸ N) := by
    intro x hx
    obtain ⟨y,rfl⟩ := hq x
    have hy : y ∈ f.ker := hx
    exact (show y ∈ centralPreimage N from hker ▸ hy)
  let C := B.map q
  let : Group.IsPerfect C := Group.IsPerfect.map _
  let c : PerfectCentralCovering.Cover (Y ⧸ N) (alternatingGroup (Fin 7)) :=
    ⟨r,hr,inferInstance,hk⟩
  have hm : C.map r = B.map f := by
    rw [map_map]
    rfl
  let e' : C.map r ≃* alternatingGroup (Fin 5) := (MulEquiv.subgroupCongr hm).trans e
  have hi : Function.Injective (r.subgroupMap C) :=
    c.injective_on_perfect_subgroup (pCore_quotient_pCore_eq_bot 2) C
      (five_odd_rank _ e')
  let eC : C ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.ofBijective (r.subgroupMap C) ⟨hi,r.subgroupMap_surjective C⟩).trans e'
  have hqk : IsPGroup 2 (q.subgroupMap B).ker := by
    let j : (q.subgroupMap B).ker →* N :=
      (B.subtype.comp (q.subgroupMap B).ker.subtype).codRestrict N (fun x => by
        apply (QuotientGroup.eq_one_iff _).mp
        exact congrArg Subtype.val x.property)
    exact pCore_isPGroup.of_injective j (by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : Y)) h)))
  exact ⟨((q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hqk).trans
    ((QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).trans
      ((QuotientGroup.quotientMulEquivOfEq alternatingGroup.five_twoCore_eq_bot).trans
        QuotientGroup.quotientBot))⟩
end Theory.SpecificGroups.Alternating.SevenPerfectSylow
