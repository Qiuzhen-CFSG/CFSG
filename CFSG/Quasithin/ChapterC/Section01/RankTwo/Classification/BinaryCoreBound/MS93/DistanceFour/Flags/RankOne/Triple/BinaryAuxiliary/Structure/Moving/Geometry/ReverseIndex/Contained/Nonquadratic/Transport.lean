module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Model

/-!
# Transport between the source commutators and linear displacements

The exact quotient map translates an ambient commutator into a linear
displacement. The original vertex core kills this action, the first layer
is fixed by its own core, and its full-actor orbit spans the quotient.
Quadraticity and full-actor fixation of opposite-core displacements
therefore transfer to the source with their literal subgroup meanings.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), pp.905--907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic
universe u
variable {M : Type u} [Group M] {L R : Subgroup M}
namespace SourceModule
variable {source : LocalSource L R} {i : Bool} {d : M}

/-- The literal image of an ambient subgroup in Y/Z_alpha. -/
noncomputable def image (b : SourceModule source i d) (H : Subgroup (FreeAmalgam R)) :
    Submodule (ZMod 2) b.Space :=
  AddSubgroup.toZModSubmodule 2 ((H.subgroupOf (Y source i d)).map b.projection).toAddSubgroup

private noncomputable def preimage (b : SourceModule source i d)
    (S : Submodule (ZMod 2) b.Space) : Subgroup (FreeAmalgam R) :=
  (S.toAddSubgroup.toSubgroup.comap b.projection).map (Y source i d).subtype

/-- The actual opposite actor acts by ambient conjugation inside Y. -/
def conjugate (_b : SourceModule source i d)
    (a : localFlagActor source (!i) d) (x : Y source i d) : Y source i d :=
  ⟨(a : FreeAmalgam R) * (x : FreeAmalgam R) * (a : FreeAmalgam R)⁻¹,
    (mem_normalizer_iff.mp (Y_normalized source i d a.property) x).mp x.property⟩

/-- An actual commutator maps to the corresponding linear displacement. -/
theorem projection_commutator (b : SourceModule source i d)
    (a : localFlagActor source (!i) d) (x : Y source i d) :
    (b.projection (b.conjugate a x * x⁻¹)).toAdd =
      b.representation a (b.projection x).toAdd - (b.projection x).toAdd := by
  rw [map_mul, map_inv]
  change (b.projection (b.conjugate a x)).toAdd + -(b.projection x).toAdd = _
  rw [b.action a x (b.conjugate a x) rfl, sub_eq_add_neg]

/-- Ambient commutator containment gives pointwise fixation in the quotient. -/
theorem fixed_of_commutator (b : SourceModule source i d)
    (H E : Subgroup (FreeAmalgam R)) (h : ⁅H,E⁆ ≤ Z R (alpha R))
    (a : localFlagActor source (!i) d) (ha : (a : FreeAmalgam R) ∈ E)
    (x : Y source i d) (hx : (x : FreeAmalgam R) ∈ H) :
    b.representation a (b.projection x).toAdd = (b.projection x).toAdd := by
  have hk : b.conjugate a x * x⁻¹ ∈ b.projection.ker := by
    rw [b.kernel]
    rw [commutator_comm] at h
    exact commutator_le.mp h a ha x hx
  have he : b.projection (b.conjugate a x) = b.projection x := by
    simpa only [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] using hk
  rw [← b.action a x (b.conjugate a x) rfl]
  exact congrArg Multiplicative.toAdd he

/-- The exact coordinate kernel detects ambient commutator containment. -/
theorem commutator_le_iff_fixed (b : SourceModule source i d)
    (H E : Subgroup (FreeAmalgam R)) (hHY : H ≤ Y source i d)
    (hEP : E ≤ localFlagActor source (!i) d) :
    ⁅H,E⁆ ≤ Z R (alpha R) ↔
      ∀ a : localFlagActor source (!i) d, (a : FreeAmalgam R) ∈ E →
      ∀ x : Y source i d, (x : FreeAmalgam R) ∈ H →
      b.representation a (b.projection x).toAdd = (b.projection x).toAdd := by
  constructor
  · exact b.fixed_of_commutator H E
  · intro h
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha x hx
    let a' : localFlagActor source (!i) d := ⟨a, hEP ha⟩
    let x' : Y source i d := ⟨x, hHY hx⟩
    have he : b.projection (b.conjugate a' x') = b.projection x' :=
      (b.action a' x' (b.conjugate a' x') rfl).trans (h a' ha x' hx)
    have hk : b.conjugate a' x' * x'⁻¹ ∈ b.projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [b.kernel] at hk
    exact hk

/-- The original vertex core kills the quotient action by the early bound. -/
theorem core_le_kernel (b : SourceModule source i d) (geometry : Geometry R)
    (early : EarlyFacts R geometry) :
    (Q R (alpha R)).subgroupOf (localFlagActor source (!i) d) ≤ b.representation.ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  ext v
  obtain ⟨x, rfl⟩ := b.onto (Multiplicative.ofAdd v)
  exact b.fixed_of_commutator (Y source i d) (Q R (alpha R))
    ((commutator_mono (Y_le_radius source i d) le_rfl).trans
      (early.commutator_le_Z _ rfl)) a ha x x.property

private theorem preimage_normalized (b : SourceModule source i d)
    (S : Submodule (ZMod 2) b.Space)
    (hS : ∀ a : localFlagActor source (!i) d, ∀ v ∈ S, b.representation a v ∈ S) :
    localFlagActor source (!i) d ≤ normalizer (b.preimage S) := by
  apply le_normalizer_iff.mpr
  rintro a ha x ⟨v, hv, rfl⟩
  let a' : localFlagActor source (!i) d := ⟨a, ha⟩
  refine ⟨b.conjugate a' v, ?_, rfl⟩
  change (b.projection (b.conjugate a' v)).toAdd ∈ S
  rw [b.action a' v (b.conjugate a' v) rfl]
  exact hS a' _ hv

/-- The actual incident first layer generates the whole module under the opposite actor. -/
theorem first_orbit_eq_top [Finite M] (b : SourceModule source i d)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (hkernel : flagKernel source i = Q R (beta R)) (hd : flagIncident source i 1 d) :
    orbitSpan b.representation (b.image (V R (beta R))) = ⊤ := by
  let S := orbitSpan b.representation (b.image (V R (beta R)))
  have hfirst : V R (beta R) ≤ Y source i d := by
    simpa only [firstFlagLayer, localConjugate_one] using first_le_Y source i 1 d hd
  have hgen : Y source i d ≤ b.preimage S := by
    apply Y_le_of_first_and_normalized source geometry hlarge i hkernel d hd
    · intro x hx
      refine ⟨⟨x, hfirst hx⟩, ?_, rfl⟩
      exact le_orbitSpan b.representation (b.image (V R (beta R)))
        ⟨⟨x, hfirst hx⟩, hx, rfl⟩
    · exact b.preimage_normalized S (fun a _ hv => orbitSpan_invariant _ _ a hv)
  apply top_unique
  intro v _
  obtain ⟨x, hx⟩ := b.onto (Multiplicative.ofAdd v)
  obtain ⟨y, hy, he⟩ := hgen x.property
  have he' : y = x := Subtype.ext he
  subst y
  change (b.projection x).toAdd ∈ S at hy
  rw [hx] at hy
  exact hy

/-- The actual first core fixes the first-layer image. -/
theorem first_fixed (b : SourceModule source i d) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (a : localFlagActor source (!i) d) (ha : (a : FreeAmalgam R) ∈ flagKernel source i)
    (v : b.Space) (hv : v ∈ b.image (V R (beta R))) : b.representation a v = v := by
  obtain ⟨x, hx, rfl⟩ := hv
  apply b.fixed_of_commutator (V R (beta R)) (flagKernel source i) _ a ha x hx
  rw [hkernel]
  exact (edgeRadius_commutator_le_edgeZ geometry common.large_distance early).trans
    (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))

/-- Source quadraticity gives quadraticity of the restricted linear action. -/
theorem quadratic_of_commutator (b : SourceModule source i d)
    (E : Subgroup (FreeAmalgam R))
    (h : ⁅⁅Y source i d,E⁆,E⁆ ≤ Z R (alpha R)) :
    QuadraticOn b.representation (E.subgroupOf (localFlagActor source (!i) d)) := by
  intro a ha e he v
  obtain ⟨x, rfl⟩ := b.onto (Multiplicative.ofAdd v)
  have hc : (b.conjugate e x * x⁻¹ : FreeAmalgam R) ∈ ⁅Y source i d,E⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator he x.property
  have hf := b.fixed_of_commutator _ E h a ha (b.conjugate e x * x⁻¹) hc
  rwa [b.projection_commutator] at hf

/-- Full-actor fixation of the displacements kills the actual source triple. -/
theorem triple_le_of_displacementsFixed (b : SourceModule source i d)
    (E : Subgroup (FreeAmalgam R)) (hEP : E ≤ localFlagActor source (!i) d)
    (h : DisplacementsFixed b.representation
      (E.subgroupOf (localFlagActor source (!i) d))) :
    ⁅⁅Y source i d,E⁆,localFlagActor source (!i) d⁆ ≤ Z R (alpha R) := by
  have hc : ⁅Y source i d,E⁆ ≤ Y source i d :=
    le_normalizer_iff_commutator_le_left.mp (hEP.trans (Y_normalized source i d))
  have hpre : ⁅Y source i d,E⁆ ≤ b.preimage b.representation.invariants := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro e he x hx
    let a : localFlagActor source (!i) d := ⟨e, hEP he⟩
    let v : Y source i d := ⟨x, hx⟩
    refine ⟨b.conjugate a v * v⁻¹, ?_, rfl⟩
    change (b.projection (b.conjugate a v * v⁻¹)).toAdd ∈ b.representation.invariants
    rw [b.projection_commutator]
    exact fun g => h g a he _
  apply (b.commutator_le_iff_fixed _ _ hc le_rfl).mpr
  intro a _ x hx
  obtain ⟨y, hy, he⟩ := hpre hx
  have he' : y = x := Subtype.ext he
  subst y
  exact hy a

end SourceModule
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic
