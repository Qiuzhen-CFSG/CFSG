module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import Theory.GroupTheory.CyclicQuotientEmbedding
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The source quotient and the representation quotient

E.2.2 takes `J = core_H(M ∩ H)` and classifies images in `H/J`.
The representation in 15.3.65 instead has actor `H/O₂(H)`. The map between
these quotients sends the actual image of `M ∩ O²(H)` onto its source image.
A model torus in the latter gives an injective homomorphism from the field
units into the former by the finite cyclic lifting argument. This is enough
for the order divisor and oddness; it does not assert a section of the map.

The final two lemmas isolate the additional three-group kernel restriction
that would justify identifying the quotients. They do not supply that
restriction from a family name or confuse it with E.2.2's centrality clause.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215–216, and 15.3.65, printed p.1152.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
open Subgroup ChapterE
variable {G : Type*} [Group G]

/-- The normal core of the actual overlap, internal to H. -/
abbrev sourceKernel (H M : Subgroup G) : Subgroup H := (M.subgroupOf H).normalCore

/-- Image of an ambient subgroup in the source quotient H/J. -/
def sourceImage (H M L : Subgroup G) : Subgroup (H ⧸ sourceKernel H M) :=
  (L.subgroupOf H).map (QuotientGroup.mk' (sourceKernel H M))

/-- Image of M₀ = M ∩ O²(H), in H/J rather than H/O₂(H). -/
noncomputable def sourceBorelImage (H M : Subgroup G) :
    Subgroup (H ⧸ sourceKernel H M) := sourceImage H M (M ⊓ residual H)

/-- The natural comparison, requiring the genuine two-core containment. -/
def actorToSource {H M : Subgroup G} (hcore : pCore 2 H ≤ sourceKernel H M) :
    (H ⧸ pCore 2 H) →* (H ⧸ sourceKernel H M) :=
  QuotientGroup.map _ _ (MonoidHom.id H) hcore

theorem actorToSource_image {H M L : Subgroup G}
    (hcore : pCore 2 H ≤ sourceKernel H M) :
    (actorImage H L).map (actorToSource hcore) = sourceImage H M L := by
  rw [actorImage, sourceImage, map_map]
  congr 1

/-- The induced surjection on the literal Borel images. -/
noncomputable def borelToSource {H M : Subgroup G} (hcore : pCore 2 H ≤ sourceKernel H M) :
    borelImage H M →* sourceBorelImage H M :=
  ((actorToSource hcore).comp (borelImage H M).subtype).codRestrict _ (by
    intro b
    change actorToSource hcore b ∈ sourceImage H M (M ⊓ residual H)
    rw [← actorToSource_image hcore]
    exact mem_map_of_mem _ b.property)

theorem borelToSource_surjective {H M : Subgroup G}
    (hcore : pCore 2 H ≤ sourceKernel H M) : Function.Surjective (borelToSource hcore) := by
  rintro ⟨x, hx⟩
  change x ∈ sourceImage H M (M ⊓ residual H) at hx
  rw [← actorToSource_image hcore] at hx
  obtain ⟨b, hb, hbx⟩ := hx
  exact ⟨⟨b, hb⟩, Subtype.ext hbx⟩

theorem sourceImage_mono {H M L K : Subgroup G} (h : L ≤ K) :
    sourceImage H M L ≤ sourceImage H M K :=
  map_mono (comap_mono h)

theorem card_sourceImage_dvd {H M L : Subgroup G} (hLH : L ≤ H) :
    Nat.card (sourceImage H M L) ∣ Nat.card L := by
  have h := (L.subgroupOf H).card_map_dvd (QuotientGroup.mk' (sourceKernel H M))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv] at h

/-- A torus in the source quotient gives an actual injection into M₀*.
No assertion that the central quotient splits is used. -/
theorem lift_source_torus [Finite G]
    {F : Type*} [Field F] [Finite F] {H M : Subgroup G}
    (hcore : pCore 2 H ≤ sourceKernel H M)
    (i : Fˣ →* sourceBorelImage H M) (hi : Function.Injective i) :
    ∃ j : Fˣ →* borelImage H M, Function.Injective j :=
  Theory.GroupTheory.cyclic_injective_of_surjective
    (borelToSource hcore) (borelToSource_surjective hcore) i hi

/-- A source Borel identification on the component, embedded in the residual. -/
theorem lift_component_borel_torus [Finite G]
    {F X : Type*} [Field F] [Finite F] [Group X]
    {H M K : Subgroup G} (B : Subgroup X)
    (hcore : pCore 2 H ≤ sourceKernel H M) (hKR : K ≤ residual H)
    (e : sourceImage H M (M ⊓ K) ≃* B)
    (i : Fˣ →* B) (hi : Function.Injective i) :
    ∃ j : Fˣ →* borelImage H M, Function.Injective j := by
  let inc : sourceImage H M (M ⊓ K) →* sourceBorelImage H M :=
    inclusion (sourceImage_mono (inf_le_inf_left M hKR))
  have hinc : Function.Injective inc := inclusion_injective _
  exact lift_source_torus hcore (inc.comp (e.symm.toMonoidHom.comp i))
    (hinc.comp (e.symm.injective.comp hi))

/-- The no-three input is used only after constructing the injection. -/
theorem odd_of_source_torus [Finite G]
    {F : Type*} [Field F] [Finite F] {H M : Subgroup G} {f : ℕ}
    (hcore : pCore 2 H ≤ sourceKernel H M)
    (hF : Nat.card F = 2 ^ f)
    (i : Fˣ →* sourceBorelImage H M) (hi : Function.Injective i)
    (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G)) : Odd f := by
  obtain ⟨j, hj⟩ := lift_source_torus hcore i hi
  exact odd_field_exponent_of_borel_torus hF j hj hthree

/-- Restrict a genuine component model equivalence to its named Borel. -/
noncomputable def componentBorelEquiv
    {X : Type*} [Group X] {H M K : Subgroup G} (B : Subgroup X)
    (e : sourceImage H M K ≃* X)
    (hB : ((sourceImage H M (M ⊓ K)).subgroupOf (sourceImage H M K)).map
      e.toMonoidHom = B) : sourceImage H M (M ⊓ K) ≃* B :=
  (subgroupOfEquivOfLe (sourceImage_mono (H := H) (M := M) (inf_le_right (a := M) (b := K)))).symm.trans
    ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hB))

/-- If the remaining kernel is a three-group, the source no-three hypothesis
kills it. The three-group assertion is a separate cover calculation. -/
theorem sourceKernel_image_eq_bot_of_three [Finite G]
    {H M : Subgroup G}
    (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G))
    (hJ : IsPGroup 3 ((sourceKernel H M).map (QuotientGroup.mk' (pCore 2 H)))) :
    (sourceKernel H M).map (QuotientGroup.mk' (pCore 2 H)) = ⊥ := by
  rcases hJ.card_eq_or_dvd with hcard | hcard
  · exact card_eq_one.mp hcard
  · apply False.elim
    apply hthree
    have hle : (sourceKernel H M).map (QuotientGroup.mk' (pCore 2 H)) ≤
        actorImage H (M ⊓ H) := by
      apply map_mono
      intro x hx
      exact ⟨(M.subgroupOf H).normalCore_le hx, x.property⟩
    exact hcard.trans ((card_dvd_of_le hle).trans (card_actorImage_dvd inf_le_right))

/-- Equality of the two kernels requires, and here uses, the cover restriction. -/
theorem sourceKernel_eq_twoCore_of_three [Finite G]
    {H M : Subgroup G} (hcore : pCore 2 H ≤ sourceKernel H M)
    (hthree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G))
    (hJ : IsPGroup 3 ((sourceKernel H M).map (QuotientGroup.mk' (pCore 2 H)))) :
    sourceKernel H M = pCore 2 H := by
  apply le_antisymm _ hcore
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  have hm := mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hx
  rw [sourceKernel_image_eq_bot_of_three hthree hJ] at hm
  exact hm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
