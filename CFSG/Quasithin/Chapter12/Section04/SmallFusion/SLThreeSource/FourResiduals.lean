module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Geometry
public import Theory.GroupAction.FourPointOrbit
public import Theory.GroupTheory.TwoLocalUniquenessControl.NormalSubgroups
public import Theory.GroupTheory.PResidual.Defs

/-!
# The four residuals in the moving-L₁ branch of 12.4.6

The family consists of the actual two-perfect subgroups Y of X with
|Y/O₂(Y)|=3. Normalizing X permutes this family. The index-three calculation
forces the orbit of L₁ to have length three; the remaining member is fixed.
Its T-invariance identifies it as X₁. Relative normality of X₁ in the
characteristic-two overgroup XLT and source uniqueness then give the final
normalizer contradiction.

The construction of X, X₁, the four residuals and their T-invariant members
is still an explicit source input. No global Sylow or fusion assertion is
among these premises.

Source: Aschbacher–Smith, the second escaping-normalizer case of 12.4.6,
printed p.814, using C.1.10.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal family called Y in the source; O²(Y)=Y is two-perfectness. -/
def cubicResiduals (X : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≤ X ∧ IsPPerfect 2 Y ∧ Nat.card (Y ⧸ pCore 2 Y) = 3}

omit [Finite G] in
theorem cubicResiduals_conjugate (X Y : Subgroup G) (g : G)
    (hg : g ∈ normalizer (X : Set G)) (hY : Y ∈ cubicResiduals X) :
    Y.map (MulAut.conj g).toMonoidHom ∈ cubicResiduals X := by
  let e := Y.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨?_, hY.2.1.of_surjective e.toMonoidHom e.surjective, ?_⟩
  · exact (map_mono hY.1).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)
  · exact (Nat.card_congr
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hY.2.2

/-- The outstanding residual construction in the moving-L₁ branch. The
overgroup is XLT in the source; all normality is relative to that overgroup. -/
structure FourResidualGeometry {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (d : LocalGeometry D) where
  X : Subgroup G
  X₁ : Subgroup G
  normalizes_X : normalizer (d.R : Set G) ≤ normalizer (X : Set G)
  four : (cubicResiduals X).ncard = 4
  line_mem : d.L₁ ∈ cubicResiduals X
  fixed_members : ∀ Y ∈ cubicResiduals X,
    (T : Subgroup G) ≤ normalizer (Y : Set G) → Y = d.L₁ ∨ Y = X₁
  characteristic_two : HasCharacteristicTwo (X ⊔ (L ⊔ (T : Subgroup G)) : Subgroup G)
  residual_le : X₁ ≤ X
  residual_normal : (X₁.subgroupOf (X ⊔ (L ⊔ (T : Subgroup G)))).Normal
  residual_nontrivial : X₁ ≠ ⊥

namespace LocalGeometry
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

omit [Finite G] in
/-- Stabilizer divisibility supplies the length-three orbit; the complement
argument identifies its fixed member with the original X₁. -/
theorem normalizes_fourth_residual (f : FourResidualGeometry d)
    (hNE : normalizer (d.R : Set G) ≤ normalizer (d.E : Set G))
    (hindex : (normalizer (L : Set G) ⊓ normalizer (d.R : Set G)).relIndex
      (normalizer (d.R : Set G)) = 3)
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    normalizer (d.R : Set G) ≤ normalizer (f.X₁ : Set G) := by
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
    ((T : Subgroup G).subgroupOf N) (cubicResiduals f.X) f.four
    (fun n Y hY => cubicResiduals_conjugate f.X Y n (f.normalizes_X n.property) hY)
    d.L₁ f.X₁ f.line_mem ho (by
      intro Y hY hTY
      apply f.fixed_members Y hY
      intro t ht
      apply mem_normalizer_iff_map_conj_eq.mpr
      exact hTY ⟨⟨t, d.sylow_normalizes ht⟩, ht⟩)
  intro n hn
  exact mem_normalizer_iff_map_conj_eq.mpr (hfixed ⟨n, hn⟩)

/-- The complete final contradiction in the moving-L₁ case, conditional
only on construction of the four residuals and their relative overgroup. -/
theorem false_of_moving_lineResidual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (f : FourResidualGeometry d) : False := by
  obtain ⟨_, _, _, hNE, hi⟩ := d.escape_geometry h structural marked hmodel hne hescape
  have hn := d.normalizes_fourth_residual f hNE hi hmoves
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
  have hX₁ : f.X₁ ≤ f.X ⊔ (L ⊔ (T : Subgroup G)) := f.residual_le.trans le_sup_left
  have hcontrol := normalizer_le_of_characteristic_two_unique
    f.characteristic_two huniq hX₁ f.residual_nontrivial
    (le_normalizer_of_normal_subgroupOf hX₁)
  exact hescape (hn.trans hcontrol)

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
