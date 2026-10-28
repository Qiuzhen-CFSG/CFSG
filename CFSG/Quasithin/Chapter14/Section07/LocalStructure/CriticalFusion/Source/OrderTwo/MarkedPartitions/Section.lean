module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ModuleTransport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Seed
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Original-section calculations for Lemma 14.7.69

In the contradiction branch Uα*=Q*, `Data.exists_criticalChart` constructs
actual Sylow coordinates on the same W and the same natural projection.
The source V/V₁ is identified by its literal L₁ cubic action in `Seed`.
Here the fixed and moved spaces are identified with the image of U₀V under
the original section map. Four distinct displacements of a vector outside
U₀V give the literal ambient commutator lower bound. These are exactly the
three module inputs consumed by `CriticalIntersections.ModuleCalculations`;
that sibling is deliberately not imported.

The marked five-line and proper-quotient partitions, their disjointness and
fixed-space cardinality are on this same section. Lifting these partitions
to E=U∩Uα, using the independent E×V₁=U₀V identity and the literal commutator
set, remains an ambient step; none of these results asserts its fusion
exclusion or the final order-two conclusion.

Earlier inputs are `SectionCentralizer` (qt-14-05), `ModuleSeparation` and
`EarlierImages` (qt-14-07), and the precise local actor implications in
`CriticalChart.LocalActors` (qt-14-03 and qt-14-07). They do not assume the
marked line or any desired intersection identity.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.65 and 14.7.69(a)–(c), printed pp.1070, 1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Representation.OneCohomology
open Chapter12.Section08 Representation.SL2FourNatural Matrix.SpecialLinearGroup
open MarkedPartitions SL2FourCentralCover
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- An actual ambient commutator, included in U by the original normalization. -/
def commutatorInU (h : F.H) (u : F.U) : F.U :=
  (⟨(h : G) * u * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) u).mp u.property⟩ : F.U) * u⁻¹

theorem commutatorInU_val (h : F.H) (u : F.U) : (d.commutatorInU h u : G) = ⁅(h : G), (u : G)⁆ := rfl

theorem commutatorInU_coordinates (h : F.H) (u : F.U) :
    (d.conjugationSection.coordinates (d.commutatorInU h u)).toAdd =
      d.action h (d.conjugationSection.coordinates u).toAdd -
        (d.conjugationSection.coordinates u).toAdd := by
  rw [commutatorInU, map_mul, map_inv]
  change (d.conjugationSection.coordinates _).toAdd +
    -(d.conjugationSection.coordinates u).toAdd = _
  rw [d.conjugationSection.equivariant, sub_eq_add_neg]

/-- The section image of U₀V uses its literal subgroup and original quotient map. -/
theorem imageSpace_U₀_sup_seed : d.conjugationSection.imageSpace (d.U₀ ⊔ V) =
    d.seedSpace ⊔ d.projection.toLinearMap.ker := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
    exact (d.mem_U₀_sup_seed u).mp hu
  · intro hw
    obtain ⟨u, hu⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
    apply (d.conjugationSection.mem_imageSpace_iff _ _).mpr
    refine ⟨u, (d.mem_U₀_sup_seed u).mpr ?_, hu⟩
    rw [hu]
    exact hw

namespace CriticalChart
variable {d} {hc : d.SectionCentralizer} {c : CriticalPath (L := L) F}
  (b : d.CriticalChart hc c)
include b

theorem imageSpace_commutator (earlier : c.EarlierImages) :
    d.conjugationSection.imageSpace ⁅F.U, c.Uα⁆ = b.moved := by
  let J : Subgroup F.U := b.moved.toAddSubgroup.toSubgroup.comap d.conjugationSection.coordinates
  have hcomm : ⁅c.Uα, F.U⁆ ≤ J.map F.U.subtype := by
    apply commutator_le.mpr
    intro x hx u hu
    let h : F.H := ⟨x, c.Uα_le_H earlier hx⟩
    let v : F.U := ⟨u, hu⟩
    refine ⟨d.commutatorInU h v, ?_, rfl⟩
    change (d.conjugationSection.coordinates (d.commutatorInU h v)).toAdd ∈ b.moved
    rw [d.commutatorInU_coordinates]
    apply Submodule.mem_iSup_of_mem (⟨h, hx⟩ : c.Uα.subgroupOf F.H)
    exact ⟨(d.conjugationSection.coordinates v).toAdd, rfl⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
    rw [commutator_comm] at hu
    obtain ⟨v, hv, he⟩ := hcomm hu
    have hvu : v = u := Subtype.ext he
    subst v
    exact hv
  · apply iSup_le
    intro h
    exact d.conjugationSection.displacement_range_le_imageSpace_of_commutator_le
      c.Uα ⁅F.U, c.Uα⁆ (le_of_eq (commutator_comm _ _)) h.val h.property

/-- The invariants for the actual inclusion Uα→H have the same section image.
This is the exact fixed-space premise consumed by CriticalIntersections. -/
theorem invariants_eq_image (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hAH : c.Uα ≤ F.H) :
    Representation.invariants (d.action.comp (Subgroup.inclusion hAH)) =
      d.conjugationSection.imageSpace (d.U₀ ⊔ V) := by
  rw [d.imageSpace_U₀_sup_seed, ← b.fixed_eq_seed_sup_kernel earlier sep localActors]
  ext w
  constructor
  · intro hw h
    exact hw ⟨h.val, h.property⟩
  · intro hw h
    exact hw ⟨⟨h, hAH h.property⟩, h.property⟩

/-- Four distinct displacements of an original vector outside U₀V lie in
the literal commutator subgroup [⟨u⟩,Uα]. This is the bound after (c). -/
theorem displacement_card_lower (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (u : F.U) (hu : (u : G) ∉ d.U₀ ⊔ V) :
    4 ≤ Nat.card (⁅zpowers (u : G), c.Uα⁆ : Subgroup G) := by
  classical
  obtain ⟨v, hv⟩ := b.onto (d.conjugationSection.coordinates u).toAdd
  have hy : (coordinates v).2 1 ≠ 0 := by
    intro hz
    have hfix : (d.conjugationSection.coordinates u).toAdd ∈
        BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) := by
      rw [← hv, b.mem_fixed_iff, b.naturalCoordinates_cover]
      exact hz
    rw [b.fixed_eq_seed_sup_kernel earlier sep localActors] at hfix
    exact hu ((d.mem_U₀_sup_seed u).mpr hfix)
  choose h hh he using b.upper_lift
  let f : SL2FourNatural.F → (⁅zpowers (u : G), c.Uα⁆ : Subgroup G) := fun t =>
    ⟨d.commutatorInU (h t) u, by
      rw [d.commutatorInU_val, commutator_comm]
      exact commutator_mem_commutator (hh t) (mem_zpowers (u : G))⟩
  have hi : Function.Injective f := by
    intro t s hts
    have hval : d.commutatorInU (h t) u = d.commutatorInU (h s) u :=
      Subtype.ext (congrArg (fun z : (⁅zpowers (u : G), c.Uα⁆ : Subgroup G) => (z : G)) hts)
    have hcoord := congrArg (fun z : F.U => (d.conjugationSection.coordinates z).toAdd) hval
    rw [d.commutatorInU_coordinates, d.commutatorInU_coordinates, ← hv,
      b.actor_cover (h t) (upper t) (he t), b.actor_cover (h s) (upper s) (he s),
      ← map_sub, ← map_sub, displacement_point, displacement_point] at hcoord
    exact vector_displacements_injective b.cover b.naturalCoordinates b.naturalCoordinates_cover
      _ hy hcoord
  have hcard := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_eq_fintype_card (α := SL2FourNatural.F), card_field] using hcard

/-- Exact original-map outputs consumed in 14.7.69(b)–(e), without assuming
an intersection identity or the order-two conclusion. -/
theorem original_module_calculations (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hAH : c.Uα ≤ F.H) :
    d.conjugationSection.imageSpace ⁅F.U, c.Uα⁆ = d.conjugationSection.imageSpace (d.U₀ ⊔ V) ∧
    Representation.invariants (d.action.comp (Subgroup.inclusion hAH)) =
      d.conjugationSection.imageSpace (d.U₀ ⊔ V) ∧
    ∀ x ∈ F.U, x ∉ d.U₀ ⊔ V → 4 ≤ Nat.card (⁅zpowers x, c.Uα⁆ : Subgroup G) := by
  refine ⟨?_, b.invariants_eq_image earlier sep localActors hAH, ?_⟩
  · rw [b.imageSpace_commutator earlier, b.moved_eq_fixed,
      b.fixed_eq_seed_sup_kernel earlier sep localActors, d.imageSpace_U₀_sup_seed]
  · intro x hx hn
    exact b.displacement_card_lower earlier sep localActors ⟨x, hx⟩ hn


/-- Every nonidentity critical actor has the common critical fixed space. -/
theorem actor_fixed_iff (h : F.H) (hh : (h : G) ∈ c.Uα)
    (hn : (h : G) ∉ F.H.pCoreIn 2) (w : W) :
    d.action h w = w ↔ b.naturalCoordinates w 1 = 0 := by
  obtain ⟨t, ht, he⟩ := b.actor_parameter_ne_zero h hh hn
  obtain ⟨v, rfl⟩ := b.onto w
  rw [b.actor_cover h (upper t) he, b.naturalCoordinates_cover]
  constructor
  · intro hv
    have hproj := congrArg b.naturalCoordinates hv
    rw [b.naturalCoordinates_cover, b.naturalCoordinates_cover,
      SL2FourCentralCover.projection.isIntertwining] at hproj
    change SL2FourNatural.action (upper t) (SL2FourCentralCover.projection v) = _ at hproj
    rw [upper_action] at hproj
    have hmul : t * SL2FourCentralCover.projection v 1 = 0 := by
      simpa using congrFun hproj 0
    exact (mul_eq_zero.mp hmul).resolve_left ht
  · intro hv
    rw [(SL2FourCentralCover.upper_fixed_iff t ht v).mpr hv]

/-- Rank two for the original actor, without an involutory ambient lift assumption. -/
theorem actor_displacement_finrank (h : F.H) (hh : (h : G) ∈ c.Uα)
    (hn : (h : G) ∉ F.H.pCoreIn 2) :
    Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2 := by
  let := d.finite_section
  let f : W →ₗ[ZMod 2] SL2FourNatural.F := (LinearMap.proj (1 : Fin 2) : SL2FourNatural.V →ₗ[ZMod 2] SL2FourNatural.F).comp b.naturalCoordinates
  have hk : (d.action h - LinearMap.id).ker = f.ker := by
    ext w
    change d.action h w - w = 0 ↔ b.naturalCoordinates w 1 = 0
    rw [sub_eq_zero, b.actor_fixed_iff h hh hn]
  have hs : Function.Surjective f := by
    intro a
    refine ⟨b.cover (coordinates.symm (0, ![0, a])), ?_⟩
    change b.naturalCoordinates (b.cover _) 1 = a
    rw [b.naturalCoordinates_cover]
    change (coordinates (coordinates.symm (0, ![0, a]))).2 1 = a
    simp
  have hd := (d.action h - LinearMap.id).finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  rw [hk] at hd
  rw [LinearMap.range_eq_top.mpr hs, finrank_top,
    SL2NaturalH1.field_finrank 2 (by rw [Nat.card_eq_fintype_card, card_field]; rfl)] at hf
  exact Nat.add_right_cancel (hd.trans hf.symm)

/-- A nonidentity critical actor fixes no binary hyperplane of the original W. -/
theorem actor_no_fixed_hyperplane (h : F.H) (hh : (h : G) ∈ c.Uα)
    (hn : (h : G) ∉ F.H.pCoreIn 2) (A : Submodule (ZMod 2) W)
    (hA : Module.finrank (ZMod 2) A + 1 = Module.finrank (ZMod 2) W) :
    ¬ ∀ w ∈ A, d.action h w = w := by
  let := d.finite_section
  intro hf
  have hle : A ≤ (d.action h - LinearMap.id).ker := by
    intro w hw
    exact sub_eq_zero.mpr (hf w hw)
  have hd := Submodule.finrank_mono hle
  have hr := (d.action h - LinearMap.id).finrank_range_add_finrank_ker
  rw [b.actor_displacement_finrank h hh hn] at hr
  omega

/-- A critical actor's original displacement image meets the original central kernel trivially. -/
theorem actor_displacement_disjoint (h : F.H) (hh : (h : G) ∈ c.Uα)
    (hn : (h : G) ∉ F.H.pCoreIn 2) :
    Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker := by
  obtain ⟨t, ht, he⟩ := b.actor_parameter_ne_zero h hh hn
  apply Submodule.disjoint_def.mpr
  intro w hw hk
  obtain ⟨v, rfl⟩ := hw
  obtain ⟨u, rfl⟩ := b.onto v
  change d.action h (b.cover u) - b.cover u = 0
  change d.action h (b.cover u) - b.cover u ∈ d.projection.toLinearMap.ker at hk
  rw [b.actor_cover h (upper t) he, ← map_sub, displacement_point] at hk ⊢
  obtain ⟨r, hr⟩ := (b.mem_kernel_iff_point _).mp hk
  have hx := point_image_eq_coordinates b.cover b.naturalCoordinates b.naturalCoordinates_cover hr
  have hy : (coordinates u).2 1 = 0 :=
    (mul_eq_zero.mp hx.symm).resolve_left ht
  rw [hy, mul_zero, mul_zero, point_zero, map_zero]

/-- The original displacement complements the central kernel inside the original
critical fixed space; the fixed-plane dimension uses the proved seed marking. -/
theorem actor_displacement_complement (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (h : F.H) (hh : (h : G) ∈ c.Uα)
    (hn : (h : G) ∉ F.H.pCoreIn 2) :
    BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) =
      (d.action h - LinearMap.id).range ⊔ d.projection.toLinearMap.ker := by
  let := d.finite_section
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · rw [← b.moved_eq_fixed]
      exact le_iSup (fun a : c.Uα.subgroupOf F.H => (d.action a.val - LinearMap.id).range) ⟨h, hh⟩
    · rw [b.fixed_eq_seed_sup_kernel earlier sep localActors]
      exact le_sup_right
  · have hd := (d.action h - LinearMap.id).range.finrank_sup_add_finrank_inf_eq
      d.projection.toLinearMap.ker
    rw [(b.actor_displacement_disjoint h hh hn).eq_bot, finrank_bot, add_zero,
      b.actor_displacement_finrank h hh hn] at hd
    have hf := d.seedSpace.finrank_sup_add_finrank_inf_eq d.projection.toLinearMap.ker
    rw [(d.seedSpace_disjoint sep).eq_bot, finrank_bot, add_zero, d.seedSpace_finrank] at hf
    rw [b.fixed_eq_seed_sup_kernel earlier sep localActors]
    exact hd.trans hf.symm

/-- The rank-three partition with the two original, rather than unmarked, images. -/
theorem rank_three_marked_partition (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (w : W)
    (hw : w ∈ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) :
    w ∈ d.projection.toLinearMap.ker ∨ w ∈ d.seedSpace ∨
      ∃ t y : SL2FourNatural.F, t ≠ 0 ∧ y ≠ 0 ∧
        b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) = w := by
  rcases b.rank_three_partition w hw with h0 | hV | h1
  · exact Or.inl ((b.mem_kernel_iff_point w).mpr h0)
  · right; left
    rw [b.seedSpace_eq_marked earlier sep localActors]
    exact hV
  · exact Or.inr (Or.inr h1)

/-- In the rank-two case only the original central image and the displacements remain. -/
theorem rank_two_marked_partition (hcard : Nat.card d.U₀ = 4) (w : W)
    (hw : w ∈ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) :
    w ∈ d.projection.toLinearMap.ker ∨
      ∃ t y : SL2FourNatural.F, t ≠ 0 ∧ y ≠ 0 ∧
        b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) = w := by
  rcases b.rank_two_partition hcard w hw with h0 | h1
  · exact Or.inl ((b.mem_kernel_iff_point w).mpr h0)
  · exact Or.inr h1

/-- The single commutators avoid the original central image in both cases. -/
theorem single_not_kernel (t y : SL2FourNatural.F) (ht : t ≠ 0) (hy : y ≠ 0) :
    b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) ∉ d.projection.toLinearMap.ker := by
  intro h
  obtain ⟨r, hr⟩ := (b.mem_kernel_iff_point _).mp h
  exact displacement_not_central_image b.cover b.naturalCoordinates b.naturalCoordinates_cover
    t y ht hy r hr.symm

/-- In the rank-three case they also avoid the actual V/V₁ image. -/
theorem single_not_seed (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (hcard : Nat.card d.U₀ = 8)
    (t y : SL2FourNatural.F) (ht : t ≠ 0) (hy : y ≠ 0) :
    b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) ∉ d.seedSpace := by
  intro h
  rw [b.seedSpace_eq_marked earlier sep localActors] at h
  obtain ⟨x, hx⟩ := h
  exact displacement_not_marked_image b.cover (b.cover_injective_of_card_eight hcard)
    t y ht hy x hx.symm

/-- In the rank-three case, distinct nonzero parameters give distinct points;
this supplies the three separate displacement lines in the source partition. -/
theorem single_parameters_unique (hcard : Nat.card d.U₀ = 8)
    {t y s z : SL2FourNatural.F} (ht : t ≠ 0) (hy : y ≠ 0) (hs : s ≠ 0)
    (he : b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) =
      b.cover (MarkedPartitions.point (s ^ 2 * z) (s * z))) : t = s ∧ y = z :=
  displacement_parameters_injective ht hy hs ((b.cover_injective_of_card_eight hcard) he)

/-- The fixed section has order sixteen or eight in the two relevant cases.
This cardinality is measured on the same W, with the original U₀. -/
theorem card_fixed (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) :
    Nat.card (BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) =
      2 * Nat.card d.U₀ := by
  let := d.finite_section
  have hd := d.seedSpace.finrank_sup_add_finrank_inf_eq d.projection.toLinearMap.ker
  rw [(d.seedSpace_disjoint sep).eq_bot, finrank_bot, add_zero, d.seedSpace_finrank] at hd
  rw [b.fixed_eq_seed_sup_kernel earlier sep localActors,
    Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card, hd, pow_add, d.card_U₀]
  ring

end CriticalChart
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
