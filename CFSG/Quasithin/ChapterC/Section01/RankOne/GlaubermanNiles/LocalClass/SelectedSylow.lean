module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.CubicResidual
public import Stellmacher.SL2FrattiniUniqueMaximal
public import Stellmacher.UniqueMaximalContainingMap

/-!
# The selected Sylow subgroup defines a minimal parabolic

A nested SL₂(2) Frattini quotient gives a unique maximal subgroup over
the specified Sylow subgroup. Normality of that Sylow would make it the
two-core, contradicting the even order of the final quotient and its odd
Sylow index. Thus the original Sylow satisfies Definition B.6.1.

Source: Aschbacher--Smith C.1.26, printed p.132.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H]

/-- Minimal parabolicity uses the original selected Sylow. -/
theorem minimalParabolic_of_nested_sl2 (P : Sylow 2 H)
    (hf : IsSL2Two ((H ⧸ pCore 2 H) ⧸ frattini (H ⧸ pCore 2 H))) :
    ChapterB.IsMinimalParabolicOver P ⊤ := by
  have hu := uniqueMaximalContaining_top_iff (P : Subgroup H) |>.mp
    (isUniqueMaximalContaining_of_sl2Two_frattini P hf)
  apply ChapterB.isMinimalParabolicOver_top_iff P |>.mpr
  refine ⟨?_,?_⟩
  · obtain ⟨M,hM,hPM,huniq⟩ := hu
    exact ⟨M,⟨hM,hPM⟩,fun N hN => huniq N hN.1 hN.2⟩
  · intro hn
    let : (P : Subgroup H).Normal := hn
    have he : pCore 2 H = P := le_antisymm
      (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨hn,P.isPGroup'⟩)
    have hd := (frattini (H ⧸ pCore 2 H)).card_quotient_dvd_card
    rw [SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hf] at hd
    have h2 : 2 ∣ Nat.card (H ⧸ pCore 2 H) := (by decide : 2 ∣ 6).trans hd
    have hi : Nat.card (H ⧸ pCore 2 H) = (P : Subgroup H).index := by
      rw [←index_eq_card,he]
    exact P.not_dvd_index (hi ▸ h2)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
