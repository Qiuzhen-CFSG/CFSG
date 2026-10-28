module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer

/-!
# Proper Hall--Janko Sylow overgroups have order prime to seven

The exhaustive full-Sylow cover consists of the literal local subgroups of
orders 1920 and 1152. Neither order has a factor seven. Conjugating an
arbitrary Sylow to the fixed marking retains the original overgroup and
proves the same divisibility obstruction for it.
Source: Aschbacher--Smith A.3.12(16), pp.47--48, used in 12.5.3, p.818.
ATLAS attribution and finite certificates are retained by the imported modules.
-/
public noncomputable section
open Subgroup
namespace Sporadic.LeechRelated.J2.SylowOvergroups

/-- Seven does not divide the order of any proper full-Sylow overgroup. -/
theorem proper_overgroup_not_seven_dvd
    (S : Sylow 2 Sporadic.LeechRelated.J2.Carrier)
    (D : Subgroup Sporadic.LeechRelated.J2.Carrier)
    (hSD : (S : Subgroup _) ≤ D) (hD : D ≠ ⊤) : ¬ 7 ∣ Nat.card D := by
  let S₀ := Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.sylow
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Sporadic.LeechRelated.J2.Carrier S S₀
  let c := MulAut.conj g
  have hS : (S : Subgroup _).map c.toMonoidHom =
      Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.s := congrArg Sylow.toSubgroup hg
  have hDc : D.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hD
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  intro hd
  have hd' : 7 ∣ Nat.card (D.map c.toMonoidHom) := by
    rwa [card_map_of_injective c.injective]
  rcases Sporadic.LeechRelated.J2.SylowOvergroups.proper_overgroup_le
      (D.map c.toMonoidHom) (hS ▸ map_mono hSD) hDc with hl | hl
  · have hh := hd'.trans (card_dvd_of_le hl)
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁] at hh
    norm_num at hh
  · have hh := hd'.trans (card_dvd_of_le hl)
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_p₂] at hh
    norm_num at hh

end Sporadic.LeechRelated.J2.SylowOvergroups
