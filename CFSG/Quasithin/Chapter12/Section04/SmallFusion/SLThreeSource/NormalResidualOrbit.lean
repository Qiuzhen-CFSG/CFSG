module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Geometry
public import Theory.GroupTheory.PResidual.NormalCubicLines
public import Theory.GroupAction.FourPointOrbit
public import Theory.GroupTheory.TwoLocalUniquenessControl.NormalSubgroups

/-!
# The normal-residual orbit in the moving-L₁ branch of 12.4.6

The source's unrestricted four-member family is insufficient: even A₄ × A₄
has more than four such subgroups. We use the normal two-perfect cubic
residuals, which correspond to the four lines of the literal quotient X/O₂(X).
The actual element of T fixing the X₁ line and inverting the L₁ line leaves
only those two members invariant. The orbit of L₁ has length three, so its
complement is fixed. Relative normality in XLT and characteristic-two
uniqueness then contradict the escaping normalizer.

This conditional source consumer discharges the counting, invariant-member,
orbit and uniqueness steps. Construction of X, X₁, their normality and the
marked action remains with the moving-residual source construction. Neither
the four-member count nor the desired normalizer conclusion is a premise.
The older FourResidualGeometry and its assembly are preserved.

Source: Aschbacher–Smith, 12.4.6, printed p.814, using C.1.10.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Source inputs for the repaired normal-residual argument. Every image
and action is on the literal quotient of the actual ambient subgroup X. -/
structure NormalResidualGeometry {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (d : LocalGeometry D) where
  X : Subgroup G
  X₁ : Subgroup G
  normalizes_X : normalizer (d.R : Set G) ≤ normalizer (X : Set G)
  elementary : IsElementaryAbelian 3 (X ⧸ pCore 2 X)
  quotient_card : Nat.card (X ⧸ pCore 2 X) = 9
  line_mem : d.L₁ ∈ normalCubicResiduals X
  fixed_mem : X₁ ∈ normalCubicResiduals X
  distinct_images : normalCubicResidualImage X d.L₁ ≠ normalCubicResidualImage X X₁
  actor : T
  inverts_line : ∀ z ∈ normalCubicResidualImage X d.L₁,
    normalCubicQuotientAction X ⟨actor, normalizes_X (d.sylow_normalizes actor.property)⟩ z = z⁻¹
  fixes_line : ∀ z ∈ normalCubicResidualImage X X₁,
    normalCubicQuotientAction X ⟨actor, normalizes_X (d.sylow_normalizes actor.property)⟩ z = z
  characteristic_two : HasCharacteristicTwo (X ⊔ (L ⊔ (T : Subgroup G)) : Subgroup G)
  residual_normal : (X₁.subgroupOf (X ⊔ (L ⊔ (T : Subgroup G)))).Normal
  residual_nontrivial : X₁ ≠ ⊥

namespace NormalResidualGeometry
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  {d : LocalGeometry D}

/-- The marked actor leaves only the two source residuals invariant. -/
theorem fixed_members (f : NormalResidualGeometry d) (Y : Subgroup G)
    (hY : Y ∈ normalCubicResiduals f.X)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) : Y = d.L₁ ∨ Y = f.X₁ := by
  let := f.elementary
  exact (normalCubicResidual_eq_marked f.X f.X₁ d.L₁ Y f.quotient_card
    f.fixed_mem f.line_mem hY (Ne.symm f.distinct_images)
    ⟨f.actor, f.normalizes_X (d.sylow_normalizes f.actor.property)⟩
    f.fixes_line f.inverts_line (hTY f.actor.property)).symm

end NormalResidualGeometry

namespace LocalGeometry
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

/-- Stabilizer divisibility supplies the length-three orbit; the complement
argument identifies its fixed member with the original X₁. -/
theorem normalizes_fourth_normal_residual (f : NormalResidualGeometry d)
    (hNE : normalizer (d.R : Set G) ≤ normalizer (d.E : Set G))
    (hindex : (normalizer (L : Set G) ⊓ normalizer (d.R : Set G)).relIndex
      (normalizer (d.R : Set G)) = 3)
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    normalizer (d.R : Set G) ≤ normalizer (f.X₁ : Set G) := by
  let := f.elementary
  let N := normalizer (d.R : Set G)
  let : MulAction N (Subgroup G) := MulAction.compHom (Subgroup G)
    (MulAut.conj.comp N.subtype)
  have hdiv : (normalizer (d.L₁ : Set G)).relIndex N ∣ 3 := by
    rw [← hindex]
    exact relIndex_dvd_of_le_left N (d.intersection_normalizes_lineResidual hNE)
  have hi : (normalizer (d.L₁ : Set G)).relIndex N = 3 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv).resolve_left
      (fun he => hmoves (relIndex_eq_one.mp he))
  have hs : MulAction.stabilizer N d.L₁ = (normalizer (d.L₁ : Set G)).subgroupOf N := by
    ext n
    exact mem_normalizer_iff_map_conj_eq.symm
  have ho : (MulAction.orbit N d.L₁).ncard = 3 := by
    rw [relIndex, ← hs, MulAction.index_stabilizer] at hi
    exact hi
  have hfixed := MulAction.fixed_of_four_point_orbit
    ((T : Subgroup G).subgroupOf N) (normalCubicResiduals f.X)
    (normalCubicResiduals_ncard f.X f.quotient_card)
    (fun n Y hY => normalCubicResiduals_conjugate f.X Y n (f.normalizes_X n.property) hY)
    d.L₁ f.X₁ f.line_mem ho (by
      intro Y hY hTY
      apply f.fixed_members Y hY
      intro t ht
      apply mem_normalizer_iff_map_conj_eq.mpr
      exact hTY ⟨⟨t, d.sylow_normalizes ht⟩, ht⟩)
  intro n hn
  exact mem_normalizer_iff_map_conj_eq.mpr (hfixed ⟨n, hn⟩)

/-- The complete final contradiction in the moving-L₁ case, conditional
on the actual source groups, their quotient action and relative overgroup. -/
theorem false_of_moving_normal_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (f : NormalResidualGeometry d) : False := by
  obtain ⟨_, _, _, hNE, hi⟩ := d.escape_geometry h structural marked hmodel hne hescape
  have hn := d.normalizes_fourth_normal_residual f hNE hi hmoves
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
      (structural G T L h).1
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      f.X ⊔ (L ⊔ (T : Subgroup G)) ≤ N →
      N = normalizer (L : Set G) := by
    intro N hN hON
    simpa only [he] using hu.normalizer_unique N hN (le_sup_right.trans hON)
  let := f.residual_normal
  have hX₁ : f.X₁ ≤ f.X ⊔ (L ⊔ (T : Subgroup G)) := f.fixed_mem.1.trans le_sup_left
  have hcontrol := normalizer_le_of_characteristic_two_unique
    f.characteristic_two huniq hX₁ f.residual_nontrivial
    (le_normalizer_of_normal_subgroupOf hX₁)
  exact hescape (hn.trans hcontrol)

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
