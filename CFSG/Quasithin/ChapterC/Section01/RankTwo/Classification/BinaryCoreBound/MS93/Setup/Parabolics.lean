module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Residual

/-!
# Realization of the binary MS93 parabolics

For a specified surjection M → SL₃(2) with kernel O₂(M), choose one conjugated
incident flag whose Borel contains the image of the given two-subgroup R.
The full inverse image of that Borel is an actual Sylow subgroup of M.
The two flag stabilizers satisfy every literal binary WBN clause, and their
lifted source-ordered rank-one residuals generate exactly O²(M).

The projection is fixed throughout. This supplies the independent parabolic
and generator part of `LocalSource`; the characteristic reduction and the
identification O²(M) = L₀ belong to the source setup assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), printed pp.827--828 and 859.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93

variable {M : Type*} [Group M] [Finite M]

/-- Realize the binary source parabolics at a common flag containing the given
 two-subgroup, without changing the specified quotient projection. All WBN
 clauses and the source-ordered residual-generation equality are proved. -/
theorem exists_binary_parabolic_realization (R : Subgroup M) (hR : IsPGroup 2 R)
    (π : M →* SL) (hπ : Function.Surjective π) (hker : π.ker = pCore 2 M) :
    ∃ (g : SL) (S : Sylow 2 M),
      R ≤ (modelBorel g).comap π ∧
      (S : Subgroup M) = (modelBorel g).comap π ∧
      BinaryWeakBN g ∧
      rankOne (parabolic π g false) ⊔ rankOne (parabolic π g true) = pResidual 2 M := by
  have hk : IsPGroup 2 π.ker := by
    rw [hker]
    exact pCore_isPGroup
  obtain ⟨g, hg⟩ := exists_flag_of_two_subgroup R hR π
  exact ⟨g, liftedBorelSylow π hπ hk g, hg, coe_liftedBorelSylow π hπ hk g,
    binaryWeakBN g, rankOne_parabolic_generation π hπ hk g⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
