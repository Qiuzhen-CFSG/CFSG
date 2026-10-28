module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
public import Theory.SpecificGroups.Tits.AutomorphismTwoRank.FourthPower
public import Theory.Representation.Tits.FrobeniusDegree

/-!
# Excluding the Tits component using its five-local subgroup

On the exact source component, the fourth-power rank estimate gives m ≤ 10,
so the source action has degree at most 22. Its faithful restriction transported
to the actual Parrott carrier has degree at least 24 by the certified 5²:24
configuration. This proves the endpoint exclusion without the separate
degree-26 irreducible catalogue or any additional model premise.

Source: Aschbacher–Smith G.9.3, printed p.356 (PDF p.367).
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
open Subgroup Theory.GroupTheory
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The genuine Tits endpoint is excluded under exactly the original source
component hypothesis and the actual group isomorphism. -/
theorem not_tits_of_source_component
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* Tits.ParrottGroup) : False := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hr : m ≤ primeRank 2 (MulAut L) := by
    apply h.toSetup.rank_le_automorphisms
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hmodel := Tits.AutomorphismTwoRank.FourthPower.automorphism_two_rank_le_ten
  have hd := degree_ge_of_model h e
    (fun σ _ hσ => Representation.TitsFrobeniusDegree.finrank_ge_twenty_four σ hσ)
  have hu := h.degree_le
  omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
