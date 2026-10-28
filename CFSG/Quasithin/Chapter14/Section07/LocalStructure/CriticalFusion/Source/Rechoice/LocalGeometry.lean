module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections

/-!
# Conditional local-geometry consumers for 14.7.70

The opening application proves the nontrivial D-commutator, its equality to
Zα, and containment of Zα and V₁ in the actual commutator. The low-rank
application proves all point, intersection and conjugacy clauses for one
prepared critical pair, using the fixed-line calculation on the original
module. Its earlier conjugacy implication is exactly 14.7.3(4).

The preparation must still construct the single permitted L₁T-rechoice,
prove the original commutator-image and spanning calculations, and supply
the careful choice modulo U₀. The rank-three action and normalization branch
also remains required. These are intermediate obligations of this task;
these conditional theorems are not a proof of the completed 14.7.70.
Final 14.7.70 assembly remains qt-14-07-critical-rechoice.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.3(4), p.1043; proof of 14.7.70, pp.1073–1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Application of the displacement calculation to both sides of the
same critical pair. F.9.13(6), the actual rank-selection codimension bound,
and the reciprocal Uα/Zα action are the explicit source inputs.
Remark 14.7.39 reverses the hypotheses; no ambient swapping element is assumed. -/
theorem opening_commutators (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent)
    (h : F.H) (hmem : (h : G) ∈ c.Uα)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (hcodim : Module.finrank (ZMod 2) (tilde d (F.U ⊓ c.Qα)) + 1 ≥
      Module.finrank (ZMod 2) W)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    {Wα : Type*} [AddCommGroup Wα] [Module (ZMod 2) Wα]
    (ρα : Representation (ZMod 2) (conjugate F.H c.conjugator) Wα)
    (a : BinaryConjugationSection (conjugate F.H c.conjugator) c.Uα c.Zα ρα)
    (y : conjugate F.H c.conjugator) (hy : (y : G) ∈ F.U)
    (hdispα : Module.finrank (ZMod 2) (ρα y - LinearMap.id).range = 2)
    (hcodimα : Module.finrank (ZMod 2) (a.imageSpace (c.Uα ⊓ F.H.pCoreIn 2)) + 1 ≥
      Module.finrank (ZMod 2) Wα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1) :
    ⁅F.U ⊓ c.Qα, c.Uα⁆ ≠ ⊥ ∧ ⁅F.U ⊓ c.Qα, c.Uα⁆ = c.Zα ∧
      ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ = F.Vi 1 ∧ c.Zα ≤ Fcomm c ∧ F.Vi 1 ≤ Fcomm c ∧ Fcomm c ≤ F.U := by
  have hn := D_commutator_ne_bot d c s h hmem t ht hh hcodim
  obtain ⟨he, hZ⟩ := D_commutator_eq_Zα c hn hF9
  obtain ⟨_, heα, hpoint⟩ := reciprocal_commutator_eq_point c ρα a y hy hdispα hcodimα hF9α
  exact ⟨hn, he, heα, hZ, hpoint, Fcomm_le_U d c earlier⟩

/-- All low-rank clauses for one prepared critical pair. The remaining
preparation must construct this pair by permitted rechoice and prove its
commutator image and spanning calculation. No such construction is claimed
by this conditional consumer. -/
theorem low_rank_branch (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (separation : d.ModuleSeparation) (s : d.ActionDescent)
    (h : F.H) (hmem : (h : G) ∈ c.Uα) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t))
    (hc : ∀ x : actorT (F := F), Commute (d.qH (x : F.H)) (d.qH h))
    (hF : tilde d (Fcomm c) = (d.action h - LinearMap.id).range)
    (h65 : SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
      tilde d V ⊔ d.projection.toLinearMap.ker)
    (hupper : ∀ a : SL2FourNatural.F, alternatingActor d.naturalQuotient
      (SL2FourNatural.upper a) ∈ (actorT (F := F)).map d.qH)
    (hspan : tilde d (Fcomm c) ⊔ tilde d V =
      SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)))
    (hmutual : F.U ≤ normalizer (c.Uα : Set G))
    (hrank : primeRank 2 d.U₀ ≤ 2) (hZF : c.Zα ≤ Fcomm c)
    (hchoice : c.Zα ≤ F.Vi 2 ⊔ d.U₀)
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l) :
    c.Zα ≤ F.Vi 2 ∧ F.U ⊓ c.Uα = d.U₀ ⊔ V ∧
      F.U ⊓ c.Uα = Fcomm c ⊔ V ∧ F.U ⊓ c.Uα = Fcomm c ⊔ d.U₀ ∧
      c.b = 3 ∧ ∃ l ∈ L, c.Uα = conjugate F.U l := by
  have hZ := selected_point_le_plane d c earlier separation s h t ht hh hc hF h65 hupper hrank hZF hchoice
  obtain ⟨hb, l, hl, he⟩ := earlier_conjugacy c (hZ.trans (F.le_seed 2))
  obtain ⟨h₁, h₂, h₃⟩ := intersection_equalities d c earlier s h hmem t ht hh hF h65 hspan hmutual l hl he
  exact ⟨hZ, h₁, h₂, h₃, hb, l, hl, he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry
