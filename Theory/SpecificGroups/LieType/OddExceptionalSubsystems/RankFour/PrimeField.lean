module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.Involution
public import Theory.Quasithin.CentralExtensionRankFour

/-!
# The prime-field rank-four centralizer in the actual exceptional quotient

Restrict the faithful four-root chart to its four prime-field coordinates.
Its image centralizes the specified surviving involution. The resulting
injection of an elementary group of order p⁴ applies directly to the
proved rank-four obstruction for odd central covers. All quotient maps
and coroot words are retained; no quotient-quasithinness is used.

Source: Aschbacher–Smith A.2.17, printed p.39; GLS3 §2.6.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.OddRankFour
open Theory.AlgebraicGroup.StandardRootSystem
open TwistedE6.FoldedSubsystem.HigherRealizations
attribute [local instance] Classical.decEq
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

namespace SixNodes
variable (c : SixNodes b) (F : Type*) [Field F] [P.IsIrreducible]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

private theorem two_ne_zero (hp : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlt
    ((CharP.cast_eq_zero_iff F p 2).mp (by simpa using h))

def primeParameters : (Fin 4 → Multiplicative (ZMod p)) →* (Fin 4 → Multiplicative F) where
  toFun a i := Multiplicative.ofAdd ((ZMod.castHom (dvd_refl p) F) (a i).toAdd)
  map_one' := by funext i; simp
  map_mul' a d := by funext i; simp

theorem primeParameters_injective : Function.Injective (primeParameters F p) := by
  intro a d h
  funext i
  apply Multiplicative.toAdd.injective
  exact (ZMod.castHom (dvd_refl p) F).injective (congrArg (fun q => (q i).toAdd) h)

/-- Four prime-field root parameters in the actual involution centralizer. -/
def centralizerEmbedding : (Fin 4 → Multiplicative (ZMod p)) →*
    Subgroup.centralizer ({c.modelInvolution F} : Set (Model P b F)) :=
  ((c.projectiveChart F).comp (primeParameters F p)).codRestrict _ (by
    intro a
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact ((c.involution_chart F (primeParameters F p a)).map (projection P b F)).symm.eq)

theorem centralizerEmbedding_injective (hp : p ≠ 2) :
    Function.Injective (c.centralizerEmbedding F p) := by
  intro a d h
  apply primeParameters_injective F p
  apply c.projectiveChart_injective F (two_ne_zero F p hp)
  exact congrArg Subtype.val h

include c in
theorem exists_elementary_centralizer (hp : p ≠ 2) :
    ∃ z : Model P b F, orderOf z = 2 ∧
      ∃ j : (Fin 4 → Multiplicative (ZMod p)) →* Subgroup.centralizer ({z} : Set (Model P b F)),
        Function.Injective j :=
  ⟨c.modelInvolution F, c.modelInvolution_order F (two_ne_zero F p hp),
    c.centralizerEmbedding F p, c.centralizerEmbedding_injective F p hp⟩

include c in
/-- Literal odd central covers are excluded using the original group and
its actual involution lift, including kernels divisible by the defining prime. -/
theorem not_quasithin_of_central_cover {G : Type*} [Group G] [Finite G]
    (hp : p ≠ 2) (q : G →* Model P b F) (hq : Function.Surjective q)
    (hc : q.ker ≤ Subgroup.center G) (ho : Odd (Nat.card q.ker)) : ¬ IsQuasithin G := by
  let A := Fin 4 → Multiplicative (ZMod p)
  let : IsElementaryAbelian p A :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        intro a
        funext i
        change p • (a i).toAdd = 0
        simp [nsmul_eq_mul]) }
  exact CentralExtension.not_isQuasithin_of_elementary_centralizer q hq hc ho hp
    (c.modelInvolution_order F (two_ne_zero F p hp))
    (c.centralizerEmbedding F p) (c.centralizerEmbedding_injective F p hp)
    (by simp)

end SixNodes
end ExceptionalSplit.OddRankFour
