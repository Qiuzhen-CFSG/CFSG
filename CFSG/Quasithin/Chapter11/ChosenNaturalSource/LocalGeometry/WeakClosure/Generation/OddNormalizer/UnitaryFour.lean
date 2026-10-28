module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ImageModels
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups

/-!
# Excluding the additional binary unitary-four component row

The actual Hermitian model is transported to standard SU₄, using the
injective projective map in characteristic two. The perfect image of the
original residual normalizes a nontrivial two-subgroup and has odd rank at
least two. The proved point and plane parabolic bounds give odd rank at
most one, excluding every PSU₄(2ⁿ) row without a Sylow-containment premise.

PlacedModels applies this to the selected component in the literal N_G(A).
Source: Aschbacher--Smith 4.4.12, printed pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Theory.SpecificGroups.ClassicalUnitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {Q : Type*} [Group Q] [Finite Q]
include D S

/-- No natural covering residual can lie in an actual binary unitary-four two-local. -/
theorem NaturalCoverImage.not_binary_unitary_four (h : NaturalCoverImage D Q)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU Q 4 (2 ^ n)) : False := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := UnitaryFourFormTransport.charP_two n (by omega) hcard
  obtain ⟨a⟩ := UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J n (by omega) hcard hconj
  let : Finite (UnitaryFourFlag.form F J.conj J.conj_involutive).specialSubgroup :=
    Finite.of_equiv Q (e.trans a).toEquiv
  obtain ⟨X,U,hX,hU,_,hne,hN,_,p,hp,ho,hr⟩ := (h.of_equiv D (e.trans a)).local_data D S
  let := hX
  let : Fact p.Prime := ⟨hp⟩
  have hb := UnitaryFourConverse.PerfectSubgroups.perfect_twoLocal_odd_primeRank_le_one
    J.conj J.conj_involutive n (by omega) hcard hconj ho X.subtype X.subtype_injective
    (normalizer (U : Set (UnitaryFourFlag.form F J.conj J.conj_involutive).specialSubgroup))
    ⟨U,hne,hU.isPGroup,rfl⟩ (by simpa only [range_subtype] using hN)
  omega
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
