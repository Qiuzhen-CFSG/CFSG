module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Transport

/-!
# The original V-line identified by its action

The literal V/V₁ image has order four and meets the original K-fixed kernel
trivially, by 14.7.2(1). The earlier R₁ action fixes this image. A literal L₁
actor with nontrivial split-diagonal image has injective displacement on it;
finite dimension makes this displacement onto. The universal coordinate
formula then identifies the original image with the cubic-marked line.
This proves both equalities in 14.7.65 and the marked identity in 14.7.69(a).

`CriticalChart.LocalActors` retains precisely the earlier local action and
actor-image inputs, owned by qt-14-03 and qt-14-07. It does not assume the
V-line identification. The inverse image theorem retains the original U₀V.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.3.3(6), 14.7.2(1), and 14.7.65/69, printed pp.1069–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Representation.OneCohomology
open Chapter12.Section08 Representation.SL2FourNatural Matrix.SpecialLinearGroup
open MarkedPartitions SL2FourCentralCover
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The original coordinate homomorphism restricted to V. -/
def seedCoordinates : V →* Multiplicative W :=
  d.conjugationSection.coordinates.comp (Subgroup.inclusion (V_le_U F))

/-- The image is the original V/V₁, as a binary subspace of the original W. -/
def seedSpace : Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2 d.seedCoordinates.range.toAddSubgroup

theorem mem_seedSpace (w : W) : w ∈ d.seedSpace ↔
    ∃ v : V, (d.seedCoordinates v).toAdd = w := Iff.rfl

theorem seedCoordinates_ker : d.seedCoordinates.ker = (F.Vi 1).subgroupOf V := by
  ext v
  change d.conjugationSection.coordinates ⟨v, V_le_U F v.property⟩ = 1 ↔ (v : G) ∈ F.Vi 1
  exact d.conjugationSection.coordinates_eq_one_iff _

theorem seedSpace_card : Nat.card d.seedSpace = 4 := by
  have h := card_eq_card_quotient_mul_card_subgroup d.seedCoordinates.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange d.seedCoordinates).toEquiv] at h
  have hk : Nat.card d.seedCoordinates.ker = 2 := by
    rw [d.seedCoordinates_ker, Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    simpa using F.card 1 (by decide)
  have hV : Nat.card V = 8 := by simpa only [F.last, Nat.reducePow] using F.card 3 (by decide)
  rw [hk, hV] at h
  change 8 = Nat.card d.seedSpace * 2 at h
  omega

theorem seedSpace_finrank : Module.finrank (ZMod 2) d.seedSpace = 2 := by
  let := d.finite_section
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := d.seedSpace)
  rw [d.seedSpace_card, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h.symm

theorem seedSpace_disjoint (sep : d.ModuleSeparation) :
    Disjoint d.seedSpace d.projection.toLinearMap.ker := by
  apply Submodule.disjoint_def.mpr
  intro w hw hk
  obtain ⟨v, rfl⟩ := (d.mem_seedSpace w).mp hw
  have hv := (d.seed_projection_zero_iff sep ⟨v, V_le_U F v.property⟩ v.property).mp hk
  exact (d.conjugationSection.coordinates_eq_one_iff _).mpr hv

theorem seedSpace_invariant (l : F.H) (hl : (l : G) ∈ F.Li L 1) (w : W)
    (hw : w ∈ d.seedSpace) : d.action l w ∈ d.seedSpace := by
  obtain ⟨v, rfl⟩ := (d.mem_seedSpace w).mp hw
  have hv : (l : G) * v * (l : G)⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (d.natural.chosen.normalizes ((F.Li_le L 1 hl).1)) v).mp v.property
  refine (d.mem_seedSpace _).mpr ⟨⟨_, hv⟩, ?_⟩
  exact d.conjugationSection.equivariant l ⟨v, V_le_U F v.property⟩

omit [Finite G] in
/-- The literal L₁ residual lies in the literal K residual. -/
theorem local_residual_le_K : F.Li L 1 ≤ K F := by
  intro x hx
  change x ∈ (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype at hx
  obtain ⟨n, hn, rfl⟩ := hx
  let f : (L ⊓ F.H : Subgroup G) →* F.H := inclusion inf_le_right
  exact mem_map.mpr ⟨f n, map_pResidual_le 2 f (mem_map.mpr ⟨n, hn, rfl⟩), rfl⟩

/-- The original L₁ commutator space of a section subspace. -/
def localMoved (A : Submodule (ZMod 2) W) : Submodule (ZMod 2) W :=
  ⨆ l : (F.Li L 1).subgroupOf F.H,
    ((d.action l.val - LinearMap.id).comp A.subtype).range

namespace CriticalChart
variable {d} {hc : d.SectionCentralizer} {c : CriticalPath (L := L) F}
  (b : d.CriticalChart hc c)

/-- The preceding local action implications, with their literal actors.
The R₁ action on V/V₁ and the L₁ image are earlier 14.3.3(6)/14.7 facts;
their producers are qt-14-03 and qt-14-07. Neither field identifies a V-line. -/
structure LocalActors : Prop where
  seed_fixed : ∀ r : F.H, (r : G) ∈ F.Ri L 1 → ∀ v : V,
    d.action r (d.seedCoordinates v).toAdd = (d.seedCoordinates v).toAdd
  cubic : ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧ ∃ a : SL2FourNatural.F,
    ∃ ha : a ≠ 0, a ≠ 1 ∧ d.qH l = alternatingActor d.naturalQuotient
      (b.conjugator * diag2 a ha * b.conjugator⁻¹)

theorem seedSpace_le_fixed (earlier : c.EarlierImages) (localActors : b.LocalActors) :
    d.seedSpace ≤ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) := by
  intro w hw h
  obtain ⟨v, rfl⟩ := (d.mem_seedSpace w).mp hw
  exact localActors.seed_fixed h.val (earlier.placement h.property) v

/-- A split cubic acts on the marked plane by the actual coordinate scaling. -/
theorem cubic_displacement (l : F.H) (a : SL2FourNatural.F) (ha : a ≠ 0)
    (hl : d.qH l = alternatingActor d.naturalQuotient
      (b.conjugator * diag2 a ha * b.conjugator⁻¹)) (r x : SL2FourNatural.F) :
    d.action l (b.cover (MarkedPartitions.point r x)) - b.cover (MarkedPartitions.point r x) =
      b.cover (MarkedPartitions.point 0 ((a - 1) * x)) := by
  rw [b.actor_cover l (diag2 a ha) hl, ← map_sub, diagonal_displacement_point]

/-- The cubic displacement is onto the original V/V₁. Its kernel is zero by
the original separation theorem, so no V-line identification is assumed. -/
theorem cubic_seed_range (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (l : F.H) (hl : (l : G) ∈ F.Li L 1)
    (a : SL2FourNatural.F) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (he : d.qH l = alternatingActor d.naturalQuotient
      (b.conjugator * diag2 a ha * b.conjugator⁻¹)) :
    ((d.action l - LinearMap.id).comp d.seedSpace.subtype).range = d.seedSpace := by
  let := d.finite_section
  let f : d.seedSpace →ₗ[ZMod 2] d.seedSpace :=
    ((d.action l - LinearMap.id).comp d.seedSpace.subtype).codRestrict d.seedSpace
      (fun w => d.seedSpace.sub_mem (d.seedSpace_invariant l hl w w.property) w.property)
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    have hz : d.action l w - w = 0 := congrArg Subtype.val hw
    obtain ⟨r, x, hx⟩ := (b.mem_fixed_iff_point (w : W)).mp
      (b.seedSpace_le_fixed earlier localActors w.property)
    have hx0 : x = 0 := by
      rw [← hx, b.cubic_displacement l a ha he] at hz
      have hproj := congrArg b.naturalCoordinates hz
      rw [b.naturalCoordinates_cover, point_projection, map_zero] at hproj
      have heq : (a - 1) * x = 0 := congrFun hproj 0
      exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr ha1)
    apply Subtype.ext
    apply Submodule.disjoint_def.mp (d.seedSpace_disjoint sep) _ w.property
    rw [← b.naturalCoordinates_ker]
    change b.naturalCoordinates w = 0
    rw [← hx, b.naturalCoordinates_cover, point_projection, hx0]
    funext i
    fin_cases i <;> rfl
  have hs := LinearMap.surjective_of_injective hi
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact (f w).property
  · intro w hw
    obtain ⟨v, hv⟩ := hs ⟨w, hw⟩
    exact ⟨v, congrArg Subtype.val hv⟩

/-- The original V/V₁ is the cubic-marked line of the universal cover.
The proof uses the actual L₁ actor and its action, in addition to dimension. -/
theorem seedSpace_eq_marked (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) :
    d.seedSpace = (b.cover.comp markedPointMap).range := by
  let := d.finite_section
  obtain ⟨l, hl, a, ha, ha1, he⟩ := localActors.cubic
  have hgen := b.cubic_seed_range earlier sep localActors l hl a ha ha1 he
  have hle : d.seedSpace ≤ (b.cover.comp markedPointMap).range := by
    intro w hw
    obtain ⟨v, hv⟩ := hgen.symm ▸ hw
    obtain ⟨r, x, hx⟩ := (b.mem_fixed_iff_point (v : W)).mp
      (b.seedSpace_le_fixed earlier localActors v.property)
    refine ⟨(a - 1) * x, ?_⟩
    change b.cover (MarkedPartitions.point 0 ((a - 1) * x)) = w
    rw [← b.cubic_displacement l a ha he, hx]
    exact hv
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [d.seedSpace_finrank, markedPointMap_finrank b.cover b.naturalCoordinates b.naturalCoordinates_cover]

/-- The central coordinate image is exactly the original K-fixed kernel. -/
theorem mem_kernel_iff_point (w : W) : w ∈ d.projection.toLinearMap.ker ↔
    ∃ r : SL2FourNatural.F, b.cover (MarkedPartitions.point r 0) = w := by
  rw [← b.naturalCoordinates_ker]
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := b.onto w
    change b.naturalCoordinates (b.cover v) = 0 at hw
    rw [b.naturalCoordinates_cover] at hw
    have he : v = MarkedPartitions.point (coordinates v).1 0 := by
      apply coordinates.injective
      rw [point_coordinates]
      apply Prod.ext
      · rfl
      · change SL2FourCentralCover.projection v = _
        rw [hw]
        funext i
        fin_cases i <;> rfl
    exact ⟨_, congrArg b.cover he.symm⟩
  · rintro ⟨r, rfl⟩
    change b.naturalCoordinates (b.cover (MarkedPartitions.point r 0)) = 0
    rw [b.naturalCoordinates_cover, point_projection]
    funext i
    fin_cases i <;> rfl

/-- The first equality in 14.7.65, on the original section and with its
original seed, now follows from the action marking. -/
theorem fixed_eq_seed_sup_kernel (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) :
    BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) =
      d.seedSpace ⊔ d.projection.toLinearMap.ker := by
  apply le_antisymm
  · intro w hw
    obtain ⟨r, x, rfl⟩ := (b.mem_fixed_iff_point w).mp hw
    apply Submodule.mem_sup.mpr
    refine ⟨b.cover (MarkedPartitions.point 0 x), ?_,
      b.cover (MarkedPartitions.point r 0), (b.mem_kernel_iff_point _).mpr ⟨r, rfl⟩, ?_⟩
    · rw [b.seedSpace_eq_marked earlier sep localActors]
      exact ⟨x, rfl⟩
    · rw [← map_add, point_add, zero_add, add_zero]
  · apply sup_le (b.seedSpace_le_fixed earlier localActors)
    intro w hw
    obtain ⟨r, rfl⟩ := (b.mem_kernel_iff_point _).mp hw
    exact (b.mem_fixed_iff_point _).mpr ⟨r, 0, rfl⟩

/-- The full module identity (a), with the seed identified by its L₁-action. -/
theorem lemma_14_7_69_a (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) :
    b.moved = BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) ∧
    BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) =
      d.seedSpace ⊔ d.projection.toLinearMap.ker :=
  ⟨b.moved_eq_fixed, b.fixed_eq_seed_sup_kernel earlier sep localActors⟩

/-- The second equality in 14.7.65, for the entire original L₁. -/
theorem fixed_localMoved_eq_seed (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) :
    d.localMoved (BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) = d.seedSpace := by
  have hfix := b.fixed_eq_seed_sup_kernel earlier sep localActors
  apply le_antisymm
  · apply iSup_le
    intro l
    rintro _ ⟨w, rfl⟩
    have hw : (w : W) ∈ d.seedSpace ⊔ d.projection.toLinearMap.ker := by
      rw [← hfix]; exact w.property
    obtain ⟨v, hv, z, hz, he⟩ := Submodule.mem_sup.mp hw
    have hzfix : d.action l.val z = z := by
      rw [d.fixed_kernel] at hz
      exact hz ⟨l.val, local_residual_le_K l.property⟩
    change d.action l.val w - w ∈ d.seedSpace
    rw [← he, map_add, hzfix]
    have heq : d.action l.val v + z - (v + z) = d.action l.val v - v := by abel
    rw [heq]
    exact d.seedSpace.sub_mem (d.seedSpace_invariant l.val l.property v hv) hv
  · obtain ⟨l, hl, a, ha, ha1, he⟩ := localActors.cubic
    have hgen := b.cubic_seed_range earlier sep localActors l hl a ha ha1 he
    intro w hw
    obtain ⟨v, hv⟩ := hgen.symm ▸ hw
    apply Submodule.mem_iSup_of_mem (⟨l, hl⟩ : (F.Li L 1).subgroupOf F.H)
    exact ⟨⟨v, b.seedSpace_le_fixed earlier localActors v.property⟩, hv⟩

end CriticalChart
/-- The original subgroup U₀V is the preimage of the two marked section images. -/
theorem mem_U₀_sup_seed (u : F.U) : (u : G) ∈ d.U₀ ⊔ V ↔
    (d.conjugationSection.coordinates u).toAdd ∈ d.seedSpace ⊔ d.projection.toLinearMap.ker := by
  let C := d.seedSpace ⊔ d.projection.toLinearMap.ker
  let J : Subgroup F.U := C.toAddSubgroup.toSubgroup.comap d.conjugationSection.coordinates
  have h0 : d.U₀ ≤ J.map F.U.subtype := by
    intro x hx
    refine ⟨⟨x, d.U₀_le_U hx⟩, ?_, rfl⟩
    exact (le_sup_right : d.projection.toLinearMap.ker ≤ C) ((d.mem_U₀ _).mp hx)
  have hV : V ≤ J.map F.U.subtype := by
    intro x hx
    refine ⟨⟨x, V_le_U F hx⟩, ?_, rfl⟩
    apply (le_sup_left : d.seedSpace ≤ C)
    exact (d.mem_seedSpace _).mpr ⟨⟨x, hx⟩, rfl⟩
  constructor
  · intro hu
    obtain ⟨v, hv, he⟩ := (sup_le h0 hV) hu
    have he' : v = u := Subtype.ext he
    subst v
    exact hv
  · intro hu
    obtain ⟨w, hw, z, hz, he⟩ := Submodule.mem_sup.mp hu
    obtain ⟨v, hv⟩ := (d.mem_seedSpace _).mp hw
    obtain ⟨k, hk⟩ := d.conjugationSection.onto (Multiplicative.ofAdd z)
    have hk0 : (k : G) ∈ d.U₀ := (d.mem_U₀ k).mpr (by rw [hk]; exact hz)
    let vU : F.U := ⟨v, V_le_U F v.property⟩
    have hc : d.conjugationSection.coordinates (vU * k) = d.conjugationSection.coordinates u := by
      apply Multiplicative.toAdd.injective
      rw [map_mul]
      change (d.seedCoordinates v).toAdd + (d.conjugationSection.coordinates k).toAdd = _
      rw [hv, hk]
      exact he
    have hker : ((vU * k)⁻¹ * u : F.U) ∈ d.conjugationSection.coordinates.ker := by
      change d.conjugationSection.coordinates ((vU * k)⁻¹ * u) = 1
      rw [map_mul, map_inv, hc, inv_mul_cancel]
    have hp : (((vU * k)⁻¹ * u : F.U) : G) ∈ F.Vi 1 := by
      rwa [d.conjugationSection.kernel_eq] at hker
    have hs := (d.U₀ ⊔ V).mul_mem
      ((d.U₀ ⊔ V).mul_mem (mem_sup_right v.property) (mem_sup_left hk0))
      (mem_sup_left (d.point_le_U₀ hp))
    change (v : G) * (k : G) * (((v : G) * (k : G))⁻¹ * (u : G)) ∈ d.U₀ ⊔ V at hs
    simpa only [mul_inv_cancel_left] using hs

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
