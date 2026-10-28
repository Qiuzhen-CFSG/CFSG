module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ThreeExtensions
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.SingularExtensions

/-!
# Weak closure and small-generation overgroups in the original fixed-free branch

The actual A₂ calculation supplies three distinct extensions over an
index-eight subgroup. Its original-actor pullback discharges the remaining
premise of the polar-space argument, so W₁ centralizes V and w(G,V)>1.
Together with r(G,V)≥3 and the chosen module's local uniqueness, E.3.35
then contains every generation-one or solvable overgroup of T in M.

All earlier geometric hypotheses remain explicit, with the original V,
Sylow subgroup, central line and normalizer preserved.

Source: Aschbacher--Smith, 12.6.28(4)--29, printed pp.834--835.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)

include hz hTV hTz hbound hTI hns in
/-- Source12.6.28(4), with the A₂ and polar calculations discharged on the
same full original module. -/
theorem SourceHypothesis.original_weakClosure_one_centralizes :
    ChapterE.indexedWeakClosure V T 1 ≤ centralizer (V : Set G) ∧
      1 < ChapterE.globalW V T := by
  apply S.original_weakClosure_one_of_three_extensions D hZ z hz hTV hTz hbound hTI hns
  intro A hAN hA hnon hr
  let : IsElementaryAbelian 2 A := hA
  exact S.original_three_extensions D hZ hTV A hAN hnon hr

include hz hTV hTz hbound hTI hns in
/-- Source12.6.29 for an actual overgroup of T whose E-generation parameter
is one. Positive attainment follows from the equality to one. -/
theorem SourceHypothesis.original_generation_one_overgroup_le
    {J : Subgroup G} (hTJ : (T : Subgroup G) ≤ J)
    (hn : ChapterE.generationParameter J = 1) : J ≤ M L := by
  apply ChapterE.SourceContainment.le_of_generationParameter_pos
    ⟨S.chosen.ne_bot,S.chosen.le_sylow,hTV⟩ (T.subtype hTJ)
  · have ho : componentOrbit V (T : Subgroup G) = V :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
        (le_componentOrbit V T)
    simpa only [ho,M] using S.chosen.doubledOrbit_centralizer_unique S.source
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S.chosen.normal_subgroup_normalizer_le S.source.toHypothesis1221
        (S.chosen.le_component.trans le_sup_left) S.chosen.ne_bot
        (sup_le S.chosen.normalizes hTV)))
  · simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ T)
  · rw [hn]; decide
  · rw [hn]
    exact lt_min
      (S.original_weakClosure_one_centralizes D hZ z hz hTV hTz hbound hTI hns).2
      (lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3)
        (S.fixed_free_intersections_of_control D hTV hTI hZ hns).2)

include hz hTV hTz hbound hTI hns in
/-- The solvable clause of source12.6.29, with the actual relative Sylow
subgroup and original C_T(V) uniqueness premise. -/
theorem SourceHypothesis.original_solvable_overgroup_le
    {J : Subgroup G} [Group.IsSolvable J] (hTJ : (T : Subgroup G) ≤ J) : J ≤ M L := by
  apply ChapterE.SourceContainment.le_of_solvable
    ⟨S.chosen.ne_bot,S.chosen.le_sylow,hTV⟩ (T.subtype hTJ)
  · have ho : componentOrbit V (T : Subgroup G) = V :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
        (le_componentOrbit V T)
    simpa only [ho,M] using S.chosen.doubledOrbit_centralizer_unique S.source
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S.chosen.normal_subgroup_normalizer_le S.source.toHypothesis1221
        (S.chosen.le_component.trans le_sup_left) S.chosen.ne_bot
        (sup_le S.chosen.normalizes hTV)))
  · simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ T)
  · exact lt_min
      (S.original_weakClosure_one_centralizes D hZ z hz hTV hTz hbound hTI hns).2
      (lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3)
        (S.fixed_free_intersections_of_control D hTV hTI hZ hns).2)

end CFSG.Quasithin.Chapter12.Section06
