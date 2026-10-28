module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.FourGroupAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.RestrictedAxes
public import CFSG.Quasithin.ChapterA.Section01.Elementary.FourGroupSource
public import Theory.GroupAction.KleinFourResidualSpan

/-!
# Kernel and residual generation for the original four-group in 14.7.70

The original vertex centralizers give the exact A.1.14 core pair on E.
Its completed kernel formula identifies O₂(Y_E) with C_{Y_E}(E) and the
product of the two fixed cores, with the literal ambient subgroups retained.
The source QT hypothesis supplies the three-rank bound on C_G(E).
Finally the full action makes the two-residual move the original point;
its actual conjugate span is therefore E, as required in 14.7.70.

Only the genuine earlier 14.5.21 equality, action descent and marked reciprocal
actor remain explicit. Their existing source owners retain their discharge.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.14, p.23,
and the proof of 14.7.70, p.1074.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

namespace Preliminary
variable (h : Preliminary d c)
include h

/-- Full A.1.14 on the actual Y_E and E of the critical pair. -/
theorem YE_kernel_and_centralizer_rank (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    (YE c).pCoreIn 2 = YE c ⊓ centralizer (E c : Set G) ∧
    (∀ x : G, x ∈ (YE c).pCoreIn 2 ↔
      ∃ b ∈ F.H.pCoreIn 2 ⊓ centralizer (E c : Set G),
        ∃ bα ∈ c.Qα ⊓ centralizer (E c : Set G), b * bα = x) ∧
    primeRank 3 (centralizer (E c : Set G)) ≤ 1 := by
  obtain ⟨v₁, v₂, hp, hc₁, hc₂, hgen⟩ := h.E_source_core_pair s h21 a ha t ht hmark
  obtain ⟨_, _, hk, hprod⟩ := ChapterA.lemma_A_1_14_1 hp
  refine ⟨by simpa only [hgen] using hk, ?_, ?_⟩
  · simpa only [hgen, FourGroupCorePair.pointKernel, hc₁, hc₂] using hprod
  · exact ChapterA.lemma_A_1_14_4 hp d.counterexample.qtke.quasithin

/-- The point-orbit under O²(Y_E) spans the original four-group, completing
the residual-generation conclusion in the pairing-action family. -/
theorem E_eq_residual_span (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    E c = conjugateSpanBy (F.Vi 1) (Y c) := by
  let := h.E_isKleinFour
  have hfull := (h.YE_full_action_and_normality s h21 a ha t ht hmark).1
  have hz : d.z ∈ E c := mem_sup_left (d.point ▸ mem_zpowers d.z)
  rw [d.point]
  exact (conjugateSpanBy_point_twoResidual_eq_fourGroup (E c) (YE c)
    (h.YE_normalizes h21.le) hfull d.z hz d.z_ne_one).symm

/-- The complete restricted-pairing and local four-group action family for
14.7.70. The actual earlier-source equality and reciprocal actor are retained;
no core-axis, full-action, normality or residual-span conclusion is assumed. -/
theorem pairing_action_source (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    CoreAxes c ∧
    Function.Surjective ((E c).normalizerMonoidHom.comp
      (inclusion (h.YE_normalizes h21.le))) ∧
    ((YE c).subgroupOf (normalizer (E c : Set G))).Normal ∧
    normalizer (E c : Set G) = YE c ⊔ centralizer (E c : Set G) ∧
    E c = conjugateSpanBy (F.Vi 1) (Y c) := by
  obtain ⟨hf, hn, hm⟩ := h.YE_full_action_and_normality s h21 a ha t ht hmark
  exact ⟨restricted_axes d c h s h21 a ha t ht hmark, hf, hn, hm,
    h.E_eq_residual_span s h21 a ha t ht hmark⟩

end Preliminary
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
