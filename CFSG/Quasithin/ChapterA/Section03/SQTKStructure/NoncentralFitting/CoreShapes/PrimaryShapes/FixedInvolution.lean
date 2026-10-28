module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.Seeds
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PrimeSL2CoverRigidity
public import Theory.GroupTheory.OddPrimeSectionCentralizers.Involution

/-!
# Cyclic fixed subgroups in the primary Fitting cores

Keep a specified involution outside F(L). Each primary supercritical seed has
literal Frattini-action kernel F(L), so this same involution acts nontrivially
on the whole primary core. The core has odd order and prime rank at most two.
The rank-two involution theorem therefore makes its fixed subgroup cyclic.

This argument treats the elementary and extraspecial seeds together and
retains every homocyclic exponent. It requires neither a new involution nor
an identification of the primary core with its seed. The final source
consumer constructs every seed and discharges prime-field cover rigidity.

Source: Aschbacher–Smith A.1.31(1), printed pp.27–28, and A.3.6,
printed pp.44–45; used in the noncentral odd-core reduction of 9.3.1,
printed p.732.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes

universe u
variable {A : Type u} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

/-- An involution outside the seed's actual action kernel has cyclic fixed
subgroup in the full primary core. The involution is retained literally. -/
theorem PrimarySeed.fixedSubgroup_isCyclic
    (s : PrimarySeed p A) (hr : primeRank p A ≤ 2)
    (t : A) (ht : t ^ 2 = 1) (hnt : t ∉ fittingSubgroup A) :
    IsCyclic (MulAut.conjNormal t : MulAut (pCore p A)).fixedSubgroup := by
  let a : MulAut (pCore p A) := MulAut.conjNormal t
  have ha2 : a ^ 2 = 1 := by
    rw [show a = MulAut.conjNormal t from rfl, ← map_pow, ht, map_one]
  have ha : Function.Involutive a := fun x => DFunLike.congr_fun ha2 x
  apply cyclic_fixedSubgroup_of_involution_rank_le_two pCore_isPGroup s.odd
    ((primeRank_subgroup_le p _).trans hr) a ha
  intro he
  apply hnt
  rw [← s.kernel_eq]
  change quotientAut (frattini s.X)
    (MulAut.characteristic s.X (MulAut.conjNormal t)) = 1
  change MulAut.conjNormal t = 1 at he
  rw [he, map_one, map_one]

variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

/-- In the prime-field SL₂ Fitting-quotient branch, each primary factor has
cyclic centralizer of the original specified involution. All seed and cover
inputs are supplied by the actual SQTK and C-component hypotheses. -/
theorem primary_fixedSubgroup_isCyclic
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L)
    (t : L) (ht : t ^ 2 = 1) (hnt : t ∉ fittingSubgroup L)
    (p : ℕ) [Fact p.Prime] (hd : p ∣ Nat.card (fittingSubgroup L)) :
    IsCyclic (MulAut.conjNormal t : MulAut (pCore p L)).fixedSubgroup := by
  obtain ⟨s⟩ := exists_primarySeed primeSL2CoverRigidity hG hO hL hquot hd
  exact s.fixedSubgroup_isCyclic
    ((hG.subgroup L).stronglyQuasithin p Fact.out s.odd) t ht hnt

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
