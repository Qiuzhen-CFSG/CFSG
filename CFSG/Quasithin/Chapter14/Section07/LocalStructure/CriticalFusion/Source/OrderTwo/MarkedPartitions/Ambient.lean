module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Section

/-!
# Ambient partitions in the contradiction branch of 14.7.69

The original coordinate homomorphism restricts to an isomorphism from
E = U ∩ Uα to the original critical fixed space: injectivity uses E ∩ V₁ = 1,
and surjectivity uses E V₁ = U₀ V. These two complement identities are the
independent output of CriticalIntersections. The reciprocal placement
U ≤ H^g supplies the second normalization needed for ambient commutators.

The literal single-commutator set corresponds exactly to the nonzero
displacements (t²y, ty, 0). The two ambient partitions have orders
(16, 4, 4, 9) and (8, 2, 6), respectively. The three order-four displacement
lines are distinct and meet trivially in the rank-three case only.

All coordinates, actors, marked subgroups, and the right conjugator are those
of the original source data. Earlier inputs remain with their source owners;
this module does not assert the final fusion exclusions or 14.7.69 itself.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.69(f) and the following two partitions, printed pp.1072–1073.
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
namespace Data.CriticalChart
variable {d : Data T L V F W} {hc : d.SectionCentralizer}
  {c : CriticalPath (L := L) F} (b : d.CriticalChart hc c)

/-- The literal common subgroup in the source partition. -/
def ambientE (_b : d.CriticalChart hc c) : Subgroup G := F.U ⊓ c.Uα

/-- Its distinguished central part. -/
def ambientE₀ : Subgroup G := b.ambientE ⊓ d.U₀

/-- Its distinguished V-part. -/
def ambientEV : Subgroup G := b.ambientE ⊓ V

/-- The literal set of nonzero single commutators in the source. -/
def ambientE₁ (_b : d.CriticalChart hc c) : Set G := {z | ∃ x ∈ c.Uα, x ∉ F.H.pCoreIn 2 ∧
  ∃ y ∈ F.U, y ∉ d.U₀ ⊔ V ∧ ⁅x, y⁆ = z}

/-- The complement identity supplied independently by CriticalIntersections. -/
structure AmbientComplement : Prop where
  inf_eq_bot : b.ambientE ⊓ F.Vi 1 = ⊥
  sup_eq : b.ambientE ⊔ F.Vi 1 = d.U₀ ⊔ V

/-- Restriction of the original coordinate homomorphism, without changing W. -/
def ambientCoordinates : b.ambientE →* Multiplicative W :=
  d.conjugationSection.coordinates.comp (Subgroup.inclusion inf_le_left)

theorem ambientCoordinates_injective (h : b.AmbientComplement) :
    Function.Injective b.ambientCoordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hk : (x : G) ∈ F.Vi 1 :=
    (d.conjugationSection.coordinates_eq_one_iff _).mp hx
  have hz : (x : G) ∈ b.ambientE ⊓ F.Vi 1 := ⟨x.property, hk⟩
  rw [h.inf_eq_bot] at hz
  exact Subtype.ext (mem_bot.mp hz)

private theorem ambient_image_eq (h : b.AmbientComplement) :
    ((d.U₀ ⊔ V).subgroupOf F.U).map d.conjugationSection.coordinates =
      (b.ambientE.subgroupOf F.U).map d.conjugationSection.coordinates := by
  rw [← h.sup_eq, subgroupOf_sup (show b.ambientE ≤ F.U from inf_le_left) d.conjugationSection.kernel_le, Subgroup.map_sup]
  have hz : ((F.Vi 1).subgroupOf F.U).map d.conjugationSection.coordinates = ⊥ := by
    rw [← d.conjugationSection.kernel_eq]
    exact Subgroup.map_ker_self _
  rw [hz, sup_bot_eq]

theorem ambientCoordinates_mem_fixed (h : b.AmbientComplement)
    (earlier : c.EarlierImages) (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (x : b.ambientE) :
    (b.ambientCoordinates x).toAdd ∈
      BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) := by
  rw [b.fixed_eq_seed_sup_kernel earlier sep localActors]
  apply (d.mem_U₀_sup_seed _).mp
  exact h.sup_eq ▸ mem_sup_left x.property

/-- The original coordinate map, with its range restricted to the actual fixed space. -/
def ambientFixedCoordinates (h : b.AmbientComplement)
    (earlier : c.EarlierImages) (sep : d.ModuleSeparation) (localActors : b.LocalActors) :
    b.ambientE →* Multiplicative
      (BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) where
  toFun x := Multiplicative.ofAdd
    ⟨(b.ambientCoordinates x).toAdd, b.ambientCoordinates_mem_fixed h earlier sep localActors x⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd b.ambientCoordinates.map_one
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (b.ambientCoordinates.map_mul x y)

theorem ambientFixedCoordinates_bijective (h : b.AmbientComplement)
    (earlier : c.EarlierImages) (sep : d.ModuleSeparation) (localActors : b.LocalActors) :
    Function.Bijective (b.ambientFixedCoordinates h earlier sep localActors) := by
  constructor
  · intro x y he
    apply b.ambientCoordinates_injective h
    exact congrArg (fun z => Multiplicative.ofAdd (z.toAdd : W)) he
  · intro w
    obtain ⟨u, hu⟩ := d.conjugationSection.onto (Multiplicative.ofAdd (w.toAdd : W))
    have hu0 : (u : G) ∈ d.U₀ ⊔ V := by
      apply (d.mem_U₀_sup_seed u).mpr
      rw [hu, ← b.fixed_eq_seed_sup_kernel earlier sep localActors]
      exact w.toAdd.property
    have hm : d.conjugationSection.coordinates u ∈
        ((d.U₀ ⊔ V).subgroupOf F.U).map d.conjugationSection.coordinates :=
      mem_map_of_mem _ hu0
    rw [b.ambient_image_eq h] at hm
    obtain ⟨v, hv, he⟩ := hm
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (he.trans hu)

/-- The complement lifts the original critical fixed space isomorphically to E. -/
def ambientEquiv (h : b.AmbientComplement)
    (earlier : c.EarlierImages) (sep : d.ModuleSeparation) (localActors : b.LocalActors) :
    b.ambientE ≃* Multiplicative
      (BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) :=
  MulEquiv.ofBijective (b.ambientFixedCoordinates h earlier sep localActors)
    (b.ambientFixedCoordinates_bijective h earlier sep localActors)

theorem ambientCoordinates_mem_kernel (x : b.ambientE) :
    (b.ambientCoordinates x).toAdd ∈ d.projection.toLinearMap.ker ↔ (x : G) ∈ b.ambientE₀ := by
  exact (d.mem_U₀ ⟨x, x.property.1⟩).symm.trans
    ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

theorem ambientCoordinates_mem_seed (x : b.ambientE) :
    (b.ambientCoordinates x).toAdd ∈ d.seedSpace ↔ (x : G) ∈ b.ambientEV := by
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := (d.mem_seedSpace _).mp hx
    let xU : F.U := ⟨x, x.property.1⟩
    let vU : F.U := ⟨v, V_le_U F v.property⟩
    have he : d.conjugationSection.coordinates vU = d.conjugationSection.coordinates xU :=
      Multiplicative.toAdd.injective hv
    have hk : ((xU / vU : F.U) : G) ∈ F.Vi 1 := by
      apply (d.conjugationSection.coordinates_eq_one_iff _).mp
      rw [map_div, he, div_self']
    refine ⟨x.property, ?_⟩
    have hm := V.mul_mem (F.le_seed 1 hk) v.property
    change ((x : G) / (v : G)) * (v : G) ∈ V at hm
    change (x : G) ∈ V
    simpa only [div_mul_cancel] using hm
  · intro hx
    exact (d.mem_seedSpace _).mpr ⟨⟨x, hx.2⟩, rfl⟩


/-- Both literal normalizations put every relevant commutator in E. -/
theorem ambient_commutator_mem (earlier : c.EarlierImages)
    (hUH : F.U ≤ conjugate F.H c.conjugator) {x y : G}
    (hx : x ∈ c.Uα) (hy : y ∈ F.U) : ⁅x, y⁆ ∈ b.ambientE := by
  have hAn : c.Uα ≤ normalizer (F.U : Set G) :=
    (c.Uα_le_H earlier).trans d.conjugationSection.normalized
  have hUn : F.U ≤ normalizer (c.Uα : Set G) :=
    hUH.trans ((map_mono d.conjugationSection.normalized).trans (le_normalizer_map _))
  have hm : ⁅x, y⁆ ∈ ⁅c.Uα, F.U⁆ := commutator_mem_commutator hx hy
  exact ⟨le_normalizer_iff_commutator_le_right.mp hAn hm,
    le_normalizer_iff_commutator_le_left.mp hUn hm⟩

theorem ambientE₁_subset (earlier : c.EarlierImages)
    (hUH : F.U ≤ conjugate F.H c.conjugator) : b.ambientE₁ ⊆ b.ambientE := by
  rintro z ⟨x, hx, _, y, hy, _, rfl⟩
  exact b.ambient_commutator_mem earlier hUH hx hy

private theorem upper_actor_not_core (a : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (he : d.qH a = alternatingActor d.naturalQuotient
      (b.conjugator * upper t * b.conjugator⁻¹)) : (a : G) ∉ F.H.pCoreIn 2 := by
  intro ha
  have ha' : a ∈ d.qH.ker := by rw [d.qH_ker]; exact ha
  have hz : b.conjugator * upper t * b.conjugator⁻¹ = 1 := by
    apply d.alternatingActor_injective
    rw [← he, map_one]
    exact ha'
  have hu : upper t = 1 := by
    apply (MulAut.conj b.conjugator).injective
    simpa only [map_one, MulAut.conj_apply] using hz
  exact ht (by simpa [upper] using congrArg (fun s : SL => s.1 0 1) hu)

private theorem outside_fixed_iff (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors) (u : F.U) :
    (u : G) ∉ d.U₀ ⊔ V ↔
      b.naturalCoordinates (d.conjugationSection.coordinates u).toAdd 1 ≠ 0 := by
  rw [d.mem_U₀_sup_seed, ← b.fixed_eq_seed_sup_kernel earlier sep localActors,
    b.mem_fixed_iff]

/-- The literal set of single commutators is exactly the set of nonzero
coordinate displacements, with the original ambient map and both parameters. -/
theorem ambientE₁_iff (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (z : b.ambientE) :
    (z : G) ∈ b.ambientE₁ ↔ ∃ t y : SL2FourNatural.F, t ≠ 0 ∧ y ≠ 0 ∧
      b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) =
        (b.ambientCoordinates z).toAdd := by
  constructor
  · rintro ⟨x, hx, hn, y, hy, hyn, he⟩
    let a : F.H := ⟨x, c.Uα_le_H earlier hx⟩
    let u : F.U := ⟨y, hy⟩
    obtain ⟨t, ht, ha⟩ := b.actor_parameter_ne_zero a hx hn
    obtain ⟨v, hv⟩ := b.onto (d.conjugationSection.coordinates u).toAdd
    have hvn : (coordinates v).2 1 ≠ 0 := by
      have hvn := (b.outside_fixed_iff earlier sep localActors u).mp hyn
      rwa [← hv, b.naturalCoordinates_cover] at hvn
    refine ⟨t, (coordinates v).2 1, ht, hvn, ?_⟩
    have hz : d.commutatorInU a u = (⟨z, z.property.1⟩ : F.U) := Subtype.ext he
    change _ = (d.conjugationSection.coordinates (⟨z, z.property.1⟩ : F.U)).toAdd
    rw [← hz, d.commutatorInU_coordinates, ← hv, b.actor_cover a (upper t) ha,
      ← map_sub, displacement_point]
  · rintro ⟨t, y, ht, hy, hz⟩
    obtain ⟨a, ha, he⟩ := b.upper_lift t
    have han := b.upper_actor_not_core a t ht he
    let v := coordinates.symm (0, ![0, y])
    obtain ⟨u, hu⟩ := d.conjugationSection.onto (Multiplicative.ofAdd (b.cover v))
    have huadd : (d.conjugationSection.coordinates u).toAdd = b.cover v :=
      congrArg Multiplicative.toAdd hu
    have hun : (u : G) ∉ d.U₀ ⊔ V := by
      apply (b.outside_fixed_iff earlier sep localActors u).mpr
      rw [huadd, b.naturalCoordinates_cover]
      change (coordinates v).2 1 ≠ 0
      simpa [v] using hy
    have hmem := b.ambient_commutator_mem earlier hUH ha u.property
    have hcval : ((⟨⁅(a : G), (u : G)⁆, hmem⟩ : b.ambientE) : G) = z := by
      apply congrArg Subtype.val
      apply b.ambientCoordinates_injective h
      apply Multiplicative.toAdd.injective
      change (d.conjugationSection.coordinates (d.commutatorInU a u)).toAdd = _
      rw [d.commutatorInU_coordinates, huadd, b.actor_cover a (upper t) he, ← map_sub,
        displacement_point]
      simpa [v] using hz
    exact ⟨a, ha, han, u, u.property, hun, hcval⟩

/-- Nonzero single commutators are disjoint from the literal central part. -/
theorem ambientE₁_disjoint_central (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) :
    Disjoint b.ambientE₁ (b.ambientE₀ : Set G) := by
  apply Set.disjoint_left.mpr
  intro z hz hz0
  let e : b.ambientE := ⟨z, hz0.1⟩
  obtain ⟨t, y, ht, hy, he⟩ := (b.ambientE₁_iff h earlier sep localActors hUH e).mp hz
  apply b.single_not_kernel t y ht hy
  rw [he]
  exact (b.ambientCoordinates_mem_kernel e).mpr hz0

/-- In particular the source's single-commutator set omits the identity. -/
theorem one_not_mem_ambientE₁ (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) : (1 : G) ∉ b.ambientE₁ := by
  intro hz
  exact Set.disjoint_left.mp (b.ambientE₁_disjoint_central h earlier sep localActors hUH)
    hz b.ambientE₀.one_mem

/-- The two distinguished ambient subgroups meet at the identity only. -/
theorem ambient_central_inf_seed (h : b.AmbientComplement) (sep : d.ModuleSeparation) :
    b.ambientE₀ ⊓ b.ambientEV = ⊥ := by
  apply bot_unique
  intro z hz
  let e : b.ambientE := ⟨z, hz.1.1⟩
  have hk := (b.ambientCoordinates_mem_kernel e).mpr hz.1
  have hs := (b.ambientCoordinates_mem_seed e).mpr hz.2
  have he := Submodule.disjoint_def.mp (d.seedSpace_disjoint sep) _ hs hk
  have hzero : e = 1 := b.ambientCoordinates_injective h
    ((Multiplicative.toAdd.injective he).trans b.ambientCoordinates.map_one.symm)
  exact congrArg Subtype.val hzero

/-- Before the central quotient the single commutators also avoid E ∩ V. -/
theorem ambientE₁_disjoint_seed (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (hcard : Nat.card d.U₀ = 8) :
    Disjoint b.ambientE₁ (b.ambientEV : Set G) := by
  apply Set.disjoint_left.mpr
  intro z hz hzV
  let e : b.ambientE := ⟨z, hzV.1⟩
  obtain ⟨t, y, ht, hy, he⟩ := (b.ambientE₁_iff h earlier sep localActors hUH e).mp hz
  apply b.single_not_seed earlier sep localActors hcard t y ht hy
  rw [he]
  exact (b.ambientCoordinates_mem_seed e).mpr hzV

/-- The rank-three source partition on the literal ambient intersection. -/
theorem ambient_rank_three_partition (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) :
    (b.ambientE : Set G) = (b.ambientE₀ : Set G) ∪ (b.ambientEV : Set G) ∪ b.ambientE₁ := by
  ext z
  constructor
  · intro hz
    let e : b.ambientE := ⟨z, hz⟩
    rcases b.rank_three_marked_partition earlier sep localActors (b.ambientCoordinates e).toAdd
      (b.ambientCoordinates_mem_fixed h earlier sep localActors e) with hk | hs | h1
    · exact Or.inl (Or.inl ((b.ambientCoordinates_mem_kernel e).mp hk))
    · exact Or.inl (Or.inr ((b.ambientCoordinates_mem_seed e).mp hs))
    · exact Or.inr ((b.ambientE₁_iff h earlier sep localActors hUH e).mpr h1)
  · rintro ((hz | hz) | hz)
    · exact hz.1
    · exact hz.1
    · exact b.ambientE₁_subset earlier hUH hz

/-- After the one-dimensional central quotient the source has two parts. -/
theorem ambient_rank_two_partition (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (hcard : Nat.card d.U₀ = 4) :
    (b.ambientE : Set G) = (b.ambientE₀ : Set G) ∪ b.ambientE₁ := by
  ext z
  constructor
  · intro hz
    let e : b.ambientE := ⟨z, hz⟩
    rcases b.rank_two_marked_partition hcard (b.ambientCoordinates e).toAdd
      (b.ambientCoordinates_mem_fixed h earlier sep localActors e) with hk | h1
    · exact Or.inl ((b.ambientCoordinates_mem_kernel e).mp hk)
    · exact Or.inr ((b.ambientE₁_iff h earlier sep localActors hUH e).mpr h1)
  · rintro (hz | hz)
    · exact hz.1
    · exact b.ambientE₁_subset earlier hUH hz


private def ambientPartEquiv (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (A : Subgroup G) (hA : A ≤ b.ambientE) (P : Submodule (ZMod 2) W)
    (hP : P ≤ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H))
    (hm : ∀ x : b.ambientE, (b.ambientCoordinates x).toAdd ∈ P ↔ (x : G) ∈ A) :
    A ≃ P := by
  let f : A → P := fun x =>
    ⟨(b.ambientCoordinates ⟨x, hA x.property⟩).toAdd, (hm _).mpr x.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y he
    apply Subtype.ext
    have he' := b.ambientCoordinates_injective h
      (Multiplicative.toAdd.injective (congrArg Subtype.val he))
    exact congrArg (fun z : b.ambientE => (z : G)) he'
  · intro w
    obtain ⟨e, he⟩ := (b.ambientFixedCoordinates_bijective h earlier sep localActors).2
      (Multiplicative.ofAdd ⟨w, hP w.property⟩)
    have he' : (b.ambientCoordinates e).toAdd = w :=
      congrArg (fun z => (z.toAdd : W)) he
    have heA : (e : G) ∈ A := (hm e).mp (he' ▸ w.property)
    exact ⟨⟨e, heA⟩, Subtype.ext he'⟩

/-- E has the cardinality of the original fixed space. -/
theorem card_ambientE (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors) :
    Nat.card b.ambientE = 2 * Nat.card d.U₀ := by
  calc
    Nat.card b.ambientE = Nat.card (Multiplicative
        (BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H))) :=
      Nat.card_congr (b.ambientEquiv h earlier sep localActors).toEquiv
    _ = 2 * Nat.card d.U₀ := b.card_fixed earlier sep localActors

/-- The ambient central part has exactly half the order of U₀. -/
theorem twice_card_ambientE₀ (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors) :
    2 * Nat.card b.ambientE₀ = Nat.card d.U₀ := by
  let := d.finite_section
  have hP : d.projection.toLinearMap.ker ≤
      BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) := by
    rw [b.fixed_eq_seed_sup_kernel earlier sep localActors]
    exact le_sup_right
  rw [Nat.card_congr (b.ambientPartEquiv h earlier sep localActors b.ambientE₀
    inf_le_left d.projection.toLinearMap.ker hP b.ambientCoordinates_mem_kernel),
    d.card_U₀, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card]

/-- The ambient V-part is an actual four-group in either branch. -/
theorem card_ambientEV (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors) :
    Nat.card b.ambientEV = 4 := by
  rw [Nat.card_congr (b.ambientPartEquiv h earlier sep localActors b.ambientEV
    inf_le_left d.seedSpace (b.seedSpace_le_fixed earlier localActors)
    b.ambientCoordinates_mem_seed), d.seedSpace_card]

/-- The counts in the five-line source partition: 16, 4, 4, and 9. -/
theorem ambient_rank_three_cards (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (hcard : Nat.card d.U₀ = 8) :
    Nat.card b.ambientE = 16 ∧ Nat.card b.ambientE₀ = 4 ∧
      Nat.card b.ambientEV = 4 ∧ Nat.card b.ambientE₁ = 9 := by
  have hE : Nat.card b.ambientE = 16 := by rw [b.card_ambientE h earlier sep localActors, hcard]
  have h0 : Nat.card b.ambientE₀ = 4 := by
    have hh := b.twice_card_ambientE₀ h earlier sep localActors
    omega
  have hV := b.card_ambientEV h earlier sep localActors
  refine ⟨hE, h0, hV, ?_⟩
  have hi : (b.ambientE₀ : Set G) ∩ (b.ambientEV : Set G) = {1} := by
    change ((b.ambientE₀ ⊓ b.ambientEV : Subgroup G) : Set G) = _
    rw [b.ambient_central_inf_seed h sep]
    rfl
  have hd : Disjoint ((b.ambientE₀ : Set G) ∪ (b.ambientEV : Set G)) b.ambientE₁ := by
    exact disjoint_sup_left.mpr
      ⟨(b.ambientE₁_disjoint_central h earlier sep localActors hUH).symm,
       (b.ambientE₁_disjoint_seed h earlier sep localActors hUH hcard).symm⟩
  have hparts := Set.ncard_union_add_ncard_inter (b.ambientE₀ : Set G) (b.ambientEV : Set G)
  have htotal := Set.ncard_union_eq hd
  rw [← b.ambient_rank_three_partition h earlier sep localActors hUH] at htotal
  rw [hi, Set.ncard_singleton] at hparts
  change Nat.card b.ambientE = _ + Nat.card b.ambientE₁ at htotal
  change _ + 1 = Nat.card b.ambientE₀ + Nat.card b.ambientEV at hparts
  omega

/-- The counts after the central quotient: 8, 2, and 6. No disjointness
between separate displacement planes is asserted in this branch. -/
theorem ambient_rank_two_cards (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (hcard : Nat.card d.U₀ = 4) :
    Nat.card b.ambientE = 8 ∧ Nat.card b.ambientE₀ = 2 ∧ Nat.card b.ambientE₁ = 6 := by
  have hE : Nat.card b.ambientE = 8 := by rw [b.card_ambientE h earlier sep localActors, hcard]
  have h0 : Nat.card b.ambientE₀ = 2 := by
    have hh := b.twice_card_ambientE₀ h earlier sep localActors
    omega
  refine ⟨hE, h0, ?_⟩
  have ht := Set.ncard_union_eq
    (b.ambientE₁_disjoint_central h earlier sep localActors hUH).symm
  rw [← b.ambient_rank_two_partition h earlier sep localActors hUH hcard] at ht
  change Nat.card b.ambientE = Nat.card b.ambientE₀ + Nat.card b.ambientE₁ at ht
  omega


/-- The universal single-displacement line, retaining its upper parameter. -/
def ambientDisplacementMap (t : SL2FourNatural.F) : SL2FourNatural.F →ₗ[ZMod 2] W :=
  b.cover.comp (({
    toFun := fun y => MarkedPartitions.point (t ^ 2 * y) (t * y)
    map_add' := by
      intro y z
      rw [mul_add, mul_add, ← point_add]
    map_smul' := by
      intro a y
      apply coordinates.injective
      rw [point_coordinates, map_smul, point_coordinates]
      apply Prod.ext
      · change t ^ 2 * (a * y) = a * (t ^ 2 * y)
        ring
      · funext i
        fin_cases i <;> simp [mul_left_comm]
  } : SL2FourNatural.F →ₗ[SL2FourNatural.F] Space).restrictScalars (ZMod 2))

/-- A displacement line lifted by the original coordinate map to the actual E. -/
def ambientLine (t : SL2FourNatural.F) : Subgroup G :=
  (((b.ambientDisplacementMap t).range.toAddSubgroup.toSubgroup.comap
    b.ambientCoordinates).map b.ambientE.subtype)

theorem ambientLine_le (t : SL2FourNatural.F) : b.ambientLine t ≤ b.ambientE := by
  rintro z ⟨e, _, rfl⟩
  exact e.property

/-- Exact pointwise coordinates for each lifted line. -/
theorem mem_ambientLine (t : SL2FourNatural.F) (e : b.ambientE) :
    (e : G) ∈ b.ambientLine t ↔ ∃ y : SL2FourNatural.F,
      b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) =
        (b.ambientCoordinates e).toAdd := by
  constructor
  · rintro ⟨z, hz, he⟩
    have hze : z = e := Subtype.ext he
    subst z
    exact hz
  · intro he
    exact ⟨e, he, rfl⟩

private theorem ambientDisplacementMap_le_fixed (t : SL2FourNatural.F) :
    (b.ambientDisplacementMap t).range ≤
      BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) := by
  rintro w ⟨y, rfl⟩
  exact (b.mem_fixed_iff_point _).mpr ⟨t ^ 2 * y, t * y, rfl⟩

private theorem ambientDisplacementMap_injective (t : SL2FourNatural.F) (ht : t ≠ 0) :
    Function.Injective (b.ambientDisplacementMap t) := by
  intro y z he
  exact mul_left_cancel₀ ht
    (point_image_eq_coordinates b.cover b.naturalCoordinates b.naturalCoordinates_cover he)

/-- Every nonzero upper parameter gives an ambient subgroup of order four. -/
theorem card_ambientLine (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (t : SL2FourNatural.F) (ht : t ≠ 0) : Nat.card (b.ambientLine t) = 4 := by
  rw [Nat.card_congr (b.ambientPartEquiv h earlier sep localActors (b.ambientLine t)
    (b.ambientLine_le t) (b.ambientDisplacementMap t).range
    (b.ambientDisplacementMap_le_fixed t) (fun e => (b.mem_ambientLine t e).symm))]
  rw [← Nat.card_congr (LinearEquiv.ofInjective (b.ambientDisplacementMap t)
    (b.ambientDisplacementMap_injective t ht)).toEquiv,
    Nat.card_eq_fintype_card, card_field]

/-- In rank three distinct upper parameters give lines meeting only at the identity. -/
theorem ambientLine_inf (h : b.AmbientComplement) (hcard : Nat.card d.U₀ = 8)
    {t s : SL2FourNatural.F} (ht : t ≠ 0) (hs : s ≠ 0) (hts : t ≠ s) :
    b.ambientLine t ⊓ b.ambientLine s = ⊥ := by
  apply bot_unique
  intro z hz
  let e : b.ambientE := ⟨z, b.ambientLine_le t hz.1⟩
  obtain ⟨y, hy⟩ := (b.mem_ambientLine t e).mp hz.1
  obtain ⟨w, hw⟩ := (b.mem_ambientLine s e).mp hz.2
  by_cases hy0 : y = 0
  · have hq : b.ambientCoordinates e = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hy0, mul_zero, mul_zero, point_zero, map_zero] at hy
      exact hy.symm
    have he : e = 1 := b.ambientCoordinates_injective h (hq.trans b.ambientCoordinates.map_one.symm)
    exact congrArg Subtype.val he
  · exact (hts (b.single_parameters_unique hcard ht hy0 hs (hy.trans hw.symm)).1).elim

/-- The three nonzero parameters give three distinct ambient order-four lines. -/
theorem ambientLine_injective (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors) (hcard : Nat.card d.U₀ = 8) :
    Function.Injective (fun t : {t : SL2FourNatural.F // t ≠ 0} => b.ambientLine t) := by
  intro t s he
  change b.ambientLine (t : SL2FourNatural.F) = b.ambientLine (s : SL2FourNatural.F) at he
  apply Subtype.ext
  by_contra hts
  have hz := b.ambientLine_inf h hcard t.property s.property hts
  rw [he, inf_idem] at hz
  have hs := b.card_ambientLine h earlier sep localActors s s.property
  rw [hz] at hs
  simp at hs

/-- The line parameter set has order three. -/
theorem ambientLine_parameter_card : Nat.card {t : SL2FourNatural.F // t ≠ 0} = 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_field]

/-- The literal commutator set is the union of the nonidentity parts of the
three displacement lines. This coverage is also valid after the quotient. -/
theorem ambientE₁_eq_line_union (h : b.AmbientComplement) (earlier : c.EarlierImages)
    (sep : d.ModuleSeparation) (localActors : b.LocalActors)
    (hUH : F.U ≤ conjugate F.H c.conjugator) :
    b.ambientE₁ = ⋃ t : {t : SL2FourNatural.F // t ≠ 0},
      ((b.ambientLine t : Set G) \ {1}) := by
  ext z
  constructor
  · intro hz
    let e : b.ambientE := ⟨z, b.ambientE₁_subset earlier hUH hz⟩
    obtain ⟨t, y, ht, hy, he⟩ := (b.ambientE₁_iff h earlier sep localActors hUH e).mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨⟨t, ht⟩, (b.mem_ambientLine t e).mpr ⟨y, he⟩, ?_⟩
    intro hz1
    have hz1' : z = 1 := hz1
    exact b.one_not_mem_ambientE₁ h earlier sep localActors hUH (hz1' ▸ hz)
  · intro hz
    obtain ⟨t, ht, hn⟩ := Set.mem_iUnion.mp hz
    let e : b.ambientE := ⟨z, b.ambientLine_le t ht⟩
    obtain ⟨y, hy⟩ := (b.mem_ambientLine t e).mp ht
    apply (b.ambientE₁_iff h earlier sep localActors hUH e).mpr
    refine ⟨t, y, t.property, ?_, hy⟩
    intro hy0
    have hq : b.ambientCoordinates e = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hy0, mul_zero, mul_zero, point_zero, map_zero] at hy
      exact hy.symm
    have he : e = 1 := b.ambientCoordinates_injective h (hq.trans b.ambientCoordinates.map_one.symm)
    exact hn (congrArg Subtype.val he)

/-- Nonidentity parts of distinct displacement lines are disjoint in rank three. -/
theorem ambientLine_nonzero_disjoint (h : b.AmbientComplement) (hcard : Nat.card d.U₀ = 8)
    {t s : SL2FourNatural.F} (ht : t ≠ 0) (hs : s ≠ 0) (hts : t ≠ s) :
    Disjoint ((b.ambientLine t : Set G) \ {1}) ((b.ambientLine s : Set G) \ {1}) := by
  apply Set.disjoint_left.mpr
  intro z hz ht'
  have hm : z ∈ b.ambientLine t ⊓ b.ambientLine s := ⟨hz.1, ht'.1⟩
  rw [b.ambientLine_inf h hcard ht hs hts] at hm
  exact hz.2 (mem_bot.mp hm)

end Data.CriticalChart
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
