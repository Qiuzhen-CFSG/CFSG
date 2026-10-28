module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitQuotient
public import Mathlib.RepresentationTheory.Invariants
public import Theory.Representation.SubspaceQuotient

/-!
# The fixed kernel in the symplectic orbit quotient

The source subgroup D is the full preimage of C_(A/Z-alpha)(L), expressed as
commutatorPreimage A L Z-alpha. Fixed-space coordinates identify this literal
subgroup as the kernel of any specified linear quotient by the fixed space.
A central elementary D and a transitive action on nonzero quotient vectors
then force A to be elementary, using an involution in the critical plane.
The target action is arbitrary, allowing the source's natural module marking.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
variable {M : Type*} [Group M] (L R : Subgroup M) (c b : Vertex R)

def orbitFixedKernel : Subgroup M :=
  commutatorPreimage (criticalOrbitNative R c b) L (orbitLayer R)

instance orbitFixedKernel_normal [L.Normal] : (orbitFixedKernel L R c b).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  exact commutatorPreimage_normalized _ _ _ ⊤ le_normalizer_of_normal
    le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal

theorem orbitFixedKernel_le : orbitFixedKernel L R c b ≤ criticalOrbitNative R c b :=
  commutatorPreimage_le _ _ _

theorem orbitLayer_le_fixedKernel (hZA : orbitLayer R ≤ criticalOrbitNative R c b) :
    orbitLayer R ≤ orbitFixedKernel L R c b :=
  le_commutatorPreimage hZA (commutator_le_left _ _)

variable [IsElementaryAbelian 2 (OrbitQuotient R c b)]

/-- The fixed subspace in A/Z-alpha, for the original component L. -/
def orbitFixedSpace : Submodule (ZMod 2) (Additive (OrbitQuotient R c b)) :=
  Representation.invariants ((orbitRepresentation R c b).comp
    (inclusion (show L ≤ ⊤ from le_top)))

private theorem quotient_fixed_iff (a : criticalOrbitNative R c b) (l : L) :
    orbitRepresentation R c b (inclusion (show L ≤ ⊤ from le_top) l)
      (orbitCoordinates R c b a).toAdd = (orbitCoordinates R c b a).toAdd ↔
      ⁅(l : M),(a : M)⁆ ∈ orbitLayer R := by
  change orbitConjugation R c b ⟨l,mem_top _⟩
    (QuotientGroup.mk' ((orbitLayer R).subgroupOf (criticalOrbitNative R c b)) a) =
      QuotientGroup.mk' ((orbitLayer R).subgroupOf (criticalOrbitNative R c b)) a ↔ _
  rw [orbitConjugation_mk]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
  change ((l : M) * (a : M) * (l : M)⁻¹) / (a : M) ∈ orbitLayer R ↔ _
  rw [div_eq_mul_inv, commutatorElement_def]

/-- Membership in the source D is exactly fixedness modulo Z-alpha. -/
theorem mem_orbitFixedKernel_iff (a : criticalOrbitNative R c b) :
    (a : M) ∈ orbitFixedKernel L R c b ↔
      (orbitCoordinates R c b a).toAdd ∈ orbitFixedSpace L R c b := by
  constructor
  · intro ha l
    apply (quotient_fixed_iff L R c b a l).mpr
    rw [←commutatorElement_inv]
    apply (orbitLayer R).inv_mem
    exact commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal
      (commutator_mem_commutator ha l.property)
  · intro ha
    rw [orbitFixedKernel,commutatorPreimage_eq_inf_comap_centralizer]
    refine ⟨a.property,?_⟩
    rintro _ ⟨l,hl,rfl⟩
    have hh := (quotient_fixed_iff L R c b a ⟨l,hl⟩).mp (ha ⟨l,hl⟩)
    have hq : QuotientGroup.mk' (orbitLayer R) ⁅l,(a : M)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hh
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hq
    exact hq

/-- Literal pullback equality for the source fixed kernel. -/
theorem orbitFixedKernel_subgroupOf_eq :
    (orbitFixedKernel L R c b).subgroupOf (criticalOrbitNative R c b) =
      ((orbitFixedSpace L R c b).toAddSubgroup.toSubgroup).comap (orbitCoordinates R c b) := by
  ext a
  exact mem_orbitFixedKernel_iff L R c b a

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
variable {M : Type*} [Group M] (L R : Subgroup M) (c b : Vertex R)
  [IsElementaryAbelian 2 (OrbitQuotient R c b)]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) (⊤ : Subgroup M) V}

/-- A marked linear quotient by the actual fixed space produces precisely
A/D, preserving the original coordinate map and ambient conjugation. -/
def orbitFixedSection (hZA : orbitLayer R ≤ criticalOrbitNative R c b)
    (f : (orbitRepresentation R c b).IntertwiningMap ρ)
    (hf : Function.Surjective f)
    (hk : f.toLinearMap.ker = orbitFixedSpace L R c b) :
    Representation.BinaryConjugationSection ⊤ (criticalOrbitNative R c b)
      (orbitFixedKernel L R c b) ρ where
  section_le := le_top
  kernel_le := orbitFixedKernel_le L R c b
  normalized := le_normalizer_of_normal
  coordinates := f.toLinearMap.toAddMonoidHom.toMultiplicative.comp (orbitCoordinates R c b)
  onto := by
    intro v
    obtain ⟨w,hw⟩ := hf v.toAdd
    obtain ⟨a,ha⟩ := (orbitSection R c b hZA).onto (Multiplicative.ofAdd w)
    refine ⟨a,?_⟩
    change f (orbitCoordinates R c b a).toAdd = v.toAdd
    rw [show (orbitCoordinates R c b a).toAdd = w from ha,hw]
  kernel_eq := by
    ext a
    change f (orbitCoordinates R c b a).toAdd = 0 ↔ (a : M) ∈ orbitFixedKernel L R c b
    change (orbitCoordinates R c b a).toAdd ∈ f.toLinearMap.ker ↔ _
    rw [hk]
    exact (mem_orbitFixedKernel_iff L R c b a).symm
  equivariant m a := by
    change f (orbitCoordinates R c b _).toAdd = ρ m (f (orbitCoordinates R c b a).toAdd)
    have he := (orbitSection R c b hZA).equivariant m a
    change (orbitCoordinates R c b _).toAdd =
      orbitRepresentation R c b m (orbitCoordinates R c b a).toAdd at he
    rw [he]
    exact LinearMap.congr_fun (f.isIntertwining' m) _

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
  {c b : Vertex R}
  (hb : s.geometry.b R = 2)
  (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
  (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
  (hne : core R (alpha R) ≠ U R (alpha R))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) (⊤ : Subgroup M) V}

/-- A quotient by the actual fixed space, applied with the elementary quotient
proved from the native distance-two source. No choice of four-space marking is
imposed on the target representation. -/
def nativeOrbitFixedSection
    (f : letI := s.orbitQuotient_elementary hb hc hab hcb hne
      (orbitRepresentation R c b).IntertwiningMap ρ)
    (hf : Function.Surjective f)
    (hk : letI := s.orbitQuotient_elementary hb hc hab hcb hne
      f.toLinearMap.ker = orbitFixedSpace L R c b) :
    Representation.BinaryConjugationSection ⊤ (criticalOrbitNative R c b)
      (orbitFixedKernel L R c b) ρ := by
  letI := s.orbitQuotient_elementary hb hc hab hcb hne
  exact orbitFixedSection L R c b (s.orbitLayer_le_orbit hb hc hab hcb) f hf hk

include s hb hc in
/-- The source involution argument for its genuine fixed kernel D. A transitive
binary action suffices, including either marking of the natural four-space. -/
theorem criticalOrbitNative_elementary_of_fixed_section
    (d : Representation.BinaryConjugationSection ⊤ (criticalOrbitNative R c b)
      (orbitFixedKernel L R c b) ρ)
    (hcentral : orbitFixedKernel L R c b ≤ centralizer (criticalOrbitNative R c b : Set M))
    (hkernel : IsElementaryAbelian 2 (orbitFixedKernel L R c b))
    (hseed : ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel L R c b)
    (htrans : ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ m : (⊤ : Subgroup M), ρ m u = v) :
    IsElementaryAbelian 2 (criticalOrbitNative R c b) := by
  classical
  let := hkernel
  apply d.elementary_of_transitive hcentral
  · exact fun y hy => elemPow_eq_one_of_isElementaryAbelian y hy
  · obtain ⟨y,hy,hny⟩ := Set.not_subset.mp hseed
    refine ⟨⟨y,le_normalClosure hy⟩,?_,?_⟩
    · exact Subtype.ext (s.criticalOrbitNative_seed_square hb hc b y hy)
    · exact fun he => hny ((d.coordinates_eq_one_iff _).mp he)
  · exact htrans

include s hb hc in
/-- Actual graph application: elementary abelianness obtained from A/D forces
the orbit-plane commutator to vanish. The geometric source must provide the
central elementary kernel and the nonzero seed, besides the transitive quotient. -/
theorem criticalOrbit_commutator_plane_eq_bot_of_fixed_section
    (d : Representation.BinaryConjugationSection ⊤ (criticalOrbitNative R c b)
      (orbitFixedKernel L R c b) ρ)
    (hcentral : orbitFixedKernel L R c b ≤ centralizer (criticalOrbitNative R c b : Set M))
    (hkernel : IsElementaryAbelian 2 (orbitFixedKernel L R c b))
    (hseed : ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel L R c b)
    (htrans : ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ m : (⊤ : Subgroup M), ρ m u = v) :
    ⁅criticalOrbit R c b,criticalPlane R c b⁆ = ⊥ := by
  let := s.criticalOrbitNative_elementary_of_fixed_section hb hc d hcentral hkernel hseed htrans
  apply le_bot_iff.mp
  apply (commutator_mono le_rfl (s.criticalPlane_le_orbit hb hc b)).trans
  change ⁅(criticalOrbitNative R c b).map (embedM R),
    (criticalOrbitNative R c b).map (embedM R)⁆ ≤ ⊥
  rw [←map_commutator,commutator_self_eq_bot_iff.mpr inferInstance,Subgroup.map_bot]

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
variable {M : Type*} [Group M] (L R : Subgroup M) [L.Normal] (c b : Vertex R)
  [IsElementaryAbelian 2 (OrbitQuotient R c b)]

/-- Normality of L makes its fixed space invariant under the whole actor. -/
def orbitFixedSubrepresentation (hZA : orbitLayer R ≤ criticalOrbitNative R c b) :
    Subrepresentation (orbitRepresentation R c b) where
  toSubmodule := orbitFixedSpace L R c b
  apply_mem_toSubmodule m x hx := by
    obtain ⟨a,ha⟩ := (orbitSection R c b hZA).onto (Multiplicative.ofAdd x)
    have ha' : (orbitCoordinates R c b a).toAdd = x := ha
    rw [←ha'] at hx ⊢
    have he := (orbitSection R c b hZA).equivariant m a
    change (orbitCoordinates R c b _).toAdd =
      orbitRepresentation R c b m (orbitCoordinates R c b a).toAdd at he
    rw [←he]
    apply (mem_orbitFixedKernel_iff L R c b _).mp
    exact (inferInstance : (orbitFixedKernel L R c b).Normal).conj_mem a
      ((mem_orbitFixedKernel_iff L R c b a).mpr hx) m

/-- The literal quotient of A/Z-alpha by its L-fixed space. -/
abbrev orbitFixedQuotientRepresentation (hZA : orbitLayer R ≤ criticalOrbitNative R c b) :=
  (orbitFixedSubrepresentation L R c b hZA).quotientRepresentation

/-- The canonical linear projection, retaining the original ambient action. -/
def orbitFixedProjection (hZA : orbitLayer R ≤ criticalOrbitNative R c b) :
    (orbitRepresentation R c b).IntertwiningMap
      (orbitFixedQuotientRepresentation L R c b hZA) where
  toLinearMap := (orbitFixedSpace L R c b).mkQ
  isIntertwining' m := by ext x; rfl

/-- The actual A/D section, without a recognition or coordinate hypothesis. -/
def canonicalOrbitFixedSection (hZA : orbitLayer R ≤ criticalOrbitNative R c b) :
    Representation.BinaryConjugationSection ⊤ (criticalOrbitNative R c b)
      (orbitFixedKernel L R c b) (orbitFixedQuotientRepresentation L R c b hZA) :=
  orbitFixedSection L R c b hZA (orbitFixedProjection L R c b hZA)
    (orbitFixedSpace L R c b).mkQ_surjective (Submodule.ker_mkQ _)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
  {c b : Vertex R}
  (hb : s.geometry.b R = 2)
  (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
  (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
  (hne : core R (alpha R) ≠ U R (alpha R))

/-- The genuine source constructs its canonical section A/D unconditionally in
the contrary distance-two branch. Recognition concerns the action on this section. -/
def nativeCanonicalOrbitFixedSection :
    letI := s.orbitQuotient_elementary hb hc hab hcb hne
    Representation.BinaryConjugationSection ⊤ (criticalOrbitNative R c b)
      (orbitFixedKernel L R c b) (orbitFixedQuotientRepresentation L R c b
        (s.orbitLayer_le_orbit hb hc hab hcb)) := by
  letI := s.orbitQuotient_elementary hb hc hab hcb hne
  exact canonicalOrbitFixedSection L R c b (s.orbitLayer_le_orbit hb hc hab hcb)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
