module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic

/-!
# Cardinalities of the three edge ranges

For the literal pointwise edge fixer F, its A₅ identification makes F
disjoint from the central cubic subgroup X. The X-orbit of Y consequently
has three points. The stabilizers of Y in L = C_G(X) and M = N_G(X)
are both F, giving orbits of orders 18 and 36. Membership in a smaller
orbit is detected by membership of a transporter in its acting subgroup.
Thus the two remaining ranges are disjoint differences, of orders 15 and 18.

The final construction embeds F into the actual quotient A₆ using
`CentralizerCalculation.coverMap`, retaining its kernel X and its ambient
inclusion. These results do not identify intersections of distinct A₅
subgroups, or assert transitivity of F ⊔ X on the two remaining ranges.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6, pp.263–264.
-/

@[expose] public section

open Subgroup MulAction
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
open PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G]

theorem actor_le_localCentralizer (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    actor D Y ≤ localCentralizer D :=
  sup_le (fixer_le_localCentralizer D Y hF) (X_le_C D)

/-- The central cubic kernel meets the centerless edge fixer trivially. -/
theorem fixer_disjoint_X (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Disjoint (fixer D Y) D.X := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  rintro x ⟨hf, hx⟩
  have hz : (⟨x, hf⟩ : fixer D Y) ∈ center (fixer D Y) := by
    apply mem_center_iff.mpr
    intro f
    exact Subtype.ext (fixer_le_localCentralizer D Y hF f.property x hx).symm
  have he := (centerCongr hF.some ⟨⟨x, hf⟩, hz⟩).property
  change hF.some ⟨x, hf⟩ ∈ center (alternatingGroup (Fin 5)) at he
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  exact congrArg Subtype.val (hF.some.map_eq_one_iff.mp he)

/-- Restriction to any subgroup between F and M preserves the literal fixer. -/
noncomputable def overgroupStabilizerEquiv (D : Seed G) (Y : D.Vertex)
    (H : Subgroup G) (hFH : fixer D Y ≤ H) (hHM : H ≤ localNormalizer D) :
    stabilizer H Y ≃* fixer D Y := by
  have he : stabilizer H Y = (fixer D Y).subgroupOf H := by
    ext h
    change (h : G) • Y = Y ↔
      (h : G) • D.base = D.base ∧ (h : G) • Y = Y
    rw [normalizer_fixes_base D ⟨h, hHM h.property⟩]
    simp only [true_and]
  exact (MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe hFH)

private theorem inv_mul_mem_fixer_of_smul_eq (D : Seed G) (Y : D.Vertex)
    {g h : G} (hg : g ∈ localNormalizer D) (hh : h ∈ localNormalizer D)
    (he : g • Y = h • Y) : g⁻¹ * h ∈ fixer D Y := by
  refine ⟨normalizer_fixes_base D
    ⟨g⁻¹ * h, (localNormalizer D).mul_mem ((localNormalizer D).inv_mem hg) hh⟩, ?_⟩
  change (g⁻¹ * h) • Y = Y
  rw [mul_smul, ← he, inv_smul_smul]

/-- The actual transporter detects the orbit of an overgroup of the fixer. -/
theorem smul_mem_overgroup_orbit_iff (D : Seed G) (Y : D.Vertex)
    (H : Subgroup G) (hFH : fixer D Y ≤ H) (hHM : H ≤ localNormalizer D)
    {g : G} (hg : g ∈ localNormalizer D) :
    g • Y ∈ orbit H Y ↔ g ∈ H := by
  constructor
  · rintro ⟨h, hh⟩
    have hf := inv_mul_mem_fixer_of_smul_eq D Y (hHM h.property) hg hh
    have hm := H.mul_mem h.property (hFH hf)
    simpa only [mul_inv_cancel_left] using hm
  · intro h
    exact ⟨⟨g, h⟩, rfl⟩

/-- In particular, FX is precisely the range of transporters to the endpoint orbit. -/
theorem smul_mem_endpointOrbit_iff (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    {g : G} (hg : g ∈ localNormalizer D) :
    g • Y ∈ endpointOrbit D Y ↔ g ∈ actor D Y := by
  rw [← actor_orbit_eq_endpointOrbit D Y hF]
  exact smul_mem_overgroup_orbit_iff D Y (actor D Y) le_sup_left
    ((actor_le_localCentralizer D Y hF).trans (C_le_M D)) hg

/-- The endpoint orbit has exactly three vertices, with no assumed orbit length. -/
theorem endpointOrbit_card (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Nat.card (endpointOrbit D Y) = 3 := by
  have hs : stabilizer D.X Y = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    exact (disjoint_iff.mp (fixer_disjoint_X D Y hF)).le
      ⟨⟨normalizer_fixes_base D ⟨x, D.X.le_normalizer x.property⟩, hx⟩, x.property⟩
  have hc := Nat.card_congr (orbitProdStabilizerEquivGroup D.X Y)
  rw [Nat.card_prod, hs, card_bot, mul_one, D.card_X] at hc
  exact hc

/-- The source inner range is an actual difference of orbits. -/
theorem innerSet_eq_sdiff (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    innerSet D Y = orbit (localCentralizer D) Y \ endpointOrbit D Y := by
  ext U
  constructor
  · rintro ⟨g, hg, hga, rfl⟩
    exact ⟨⟨⟨g, hg⟩, rfl⟩, fun h =>
      hga ((smul_mem_endpointOrbit_iff D Y hF (C_le_M D hg)).mp h)⟩
  · rintro ⟨⟨g, rfl⟩, h⟩
    exact ⟨g, g.property, fun hg =>
      h ((smul_mem_endpointOrbit_iff D Y hF (C_le_M D g.property)).mpr hg), rfl⟩

/-- The source outer range is the other half of the normalizer orbit. -/
theorem outerSet_eq_sdiff (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    outerSet D Y = orbit (localNormalizer D) Y \ orbit (localCentralizer D) Y := by
  ext U
  constructor
  · rintro ⟨g, hg, hgl, rfl⟩
    exact ⟨⟨⟨g, hg⟩, rfl⟩, fun h => hgl
      ((smul_mem_overgroup_orbit_iff D Y (localCentralizer D)
        (fixer_le_localCentralizer D Y hF) (C_le_M D) hg).mp h)⟩
  · rintro ⟨⟨g, rfl⟩, h⟩
    exact ⟨g, g.property, fun hg => h ⟨⟨g, hg⟩, rfl⟩, rfl⟩

private theorem endpoint_subset_centralizer_orbit (D : Seed G) (Y : D.Vertex) :
    endpointOrbit D Y ⊆ orbit (localCentralizer D) Y := by
  rintro U ⟨x, rfl⟩
  exact ⟨⟨x, X_le_C D x.property⟩, rfl⟩

private theorem centralizer_orbit_subset_normalizer_orbit (D : Seed G) (Y : D.Vertex) :
    orbit (localCentralizer D) Y ⊆ orbit (localNormalizer D) Y := by
  rintro U ⟨g, rfl⟩
  exact ⟨⟨g, C_le_M D g.property⟩, rfl⟩

/-- All three literal transporter ranges are pairwise disjoint. -/
theorem ranges_disjoint (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Disjoint (endpointOrbit D Y) (innerSet D Y) ∧
    Disjoint (endpointOrbit D Y) (outerSet D Y) ∧
    Disjoint (innerSet D Y) (outerSet D Y) := by
  rw [innerSet_eq_sdiff D Y hF, outerSet_eq_sdiff D Y hF]
  exact ⟨Set.disjoint_sdiff_right, Set.disjoint_sdiff_right.mono_left
    (endpoint_subset_centralizer_orbit D Y),
    Set.disjoint_sdiff_right.mono_left Set.sdiff_subset⟩

private theorem overgroup_orbit_card_mul (D : Seed G) (Y : D.Vertex)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (H : Subgroup G) (hFH : fixer D Y ≤ H) (hHM : H ≤ localNormalizer D) :
    Nat.card (orbit H Y) * 60 = Nat.card H := by
  have h := Nat.card_congr (orbitProdStabilizerEquivGroup H Y)
  rw [Nat.card_prod,
    Nat.card_congr (overgroupStabilizerEquiv D Y H hFH hHM).toEquiv,
    Nat.card_congr hF.some.toEquiv, nat_card_alternatingGroup] at h
  norm_num at h
  exact h

theorem centralizer_orbit_card (D : Seed G) (H : CentralizerCalculation D)
    (Y : D.Vertex) (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Nat.card (orbit (localCentralizer D) Y) = 18 := by
  have h := overgroup_orbit_card_mul D Y hF (localCentralizer D)
    (fixer_le_localCentralizer D Y hF) (C_le_M D)
  rw [H.centralizer_card] at h
  omega

theorem normalizer_orbit_card (D : Seed G) (H : CentralizerCalculation D)
    (Y : D.Vertex) (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Nat.card (orbit (localNormalizer D) Y) = 36 := by
  have h := overgroup_orbit_card_mul D Y hF (localNormalizer D)
    ((fixer_le_localCentralizer D Y hF).trans (C_le_M D)) le_rfl
  rw [H.normalizer_card] at h
  omega

theorem innerSet_card (D : Seed G) (H : CentralizerCalculation D)
    (Y : D.Vertex) (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Nat.card (innerSet D Y) = 15 := by
  rw [innerSet_eq_sdiff D Y hF, Nat.card_coe_set_eq,
    Set.ncard_sdiff (endpoint_subset_centralizer_orbit D Y),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    centralizer_orbit_card D H Y hF, endpointOrbit_card D Y hF]

theorem outerSet_card (D : Seed G) (H : CentralizerCalculation D)
    (Y : D.Vertex) (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Nat.card (outerSet D Y) = 18 := by
  rw [outerSet_eq_sdiff D Y hF, Nat.card_coe_set_eq,
    Set.ncard_sdiff (centralizer_orbit_subset_normalizer_orbit D Y),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    normalizer_orbit_card D H Y hF, centralizer_orbit_card D H Y hF]

/-- The edge fixer enters A₆ through the published cover map and its actual inclusion. -/
noncomputable def coverFixerMap (D : Seed G) (H : CentralizerCalculation D)
    (Y : D.Vertex) (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    fixer D Y →* alternatingGroup (Fin 6) :=
  H.coverMap.comp (inclusion (fixer_le_localCentralizer D Y hF))

theorem coverFixerMap_injective (D : Seed G) (H : CentralizerCalculation D)
    (Y : D.Vertex) (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    Function.Injective (coverFixerMap D H Y hF) := by
  apply (coverFixerMap D H Y hF).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro f hf
  have hx : inclusion (fixer_le_localCentralizer D Y hF) f ∈ H.coverMap.ker := hf
  rw [H.coverMap_ker] at hx
  apply Subtype.ext
  exact (disjoint_iff.mp (fixer_disjoint_X D Y hF)).le ⟨f.property, hx⟩

/-- The subgroup used in the quotient calculation is genuinely A₅. -/
noncomputable def coverFixerRangeEquiv (D : Seed G) (H : CentralizerCalculation D)
    (Y : D.Vertex) (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5))) :
    (coverFixerMap D H Y hF).range ≃* alternatingGroup (Fin 5) :=
  (MonoidHom.ofInjective (coverFixerMap_injective D H Y hF)).symm.trans hF.some

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
