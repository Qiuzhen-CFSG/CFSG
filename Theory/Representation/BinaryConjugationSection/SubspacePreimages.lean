module
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.GroupTheory.CentralOverlapSupportMovement

/-!
# Lifting irreducible supports through a binary conjugation section

The full coordinate preimage of a subspace is an actual subgroup of the
original numerator. The correspondence preserves intersections and conjugates,
identifies the exact support normalizer, and places Irr⁺ lifts in the original
commutator subgroup whenever it contains the coordinate kernel.

Distinct Irr⁺ members intersect only in fixed vectors. If the actor is
perfect and centralizes the kernel, the three-subgroups lemma lifts this to
centralization of the actual overlap. This supplies separated supports even
for central covers with nonzero fixed space. A fixed-moving coordinate also
lifts inside the prescribed support, retaining the original commutators.

Source application: Aschbacher--Smith 14.6.22--24, printed pp.1038--1039,
using the Irr⁺ separation of A.1.40 and B.7.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H V}
  (c : BinaryConjugationSection H U Z ρ)

/-- The full preimage of a subspace under the original coordinate quotient. -/
@[expose] def subspacePreimage (I : Submodule (ZMod 2) V) : Subgroup G :=
  (I.toAddSubgroup.toSubgroup.comap c.coordinates).map U.subtype

theorem mem_subspacePreimage (I : Submodule (ZMod 2) V) (x : G) :
    x ∈ c.subspacePreimage I ↔ ∃ hx : x ∈ U, (c.coordinates ⟨x,hx⟩).toAdd ∈ I := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,hx⟩
  · rintro ⟨hx,hI⟩
    exact ⟨⟨x,hx⟩,hI,rfl⟩

theorem subspacePreimage_le (I : Submodule (ZMod 2) V) : c.subspacePreimage I ≤ U :=
  map_subtype_le _

theorem kernel_le_subspacePreimage (I : Submodule (ZMod 2) V) : Z ≤ c.subspacePreimage I := by
  intro z hz
  apply (c.mem_subspacePreimage I z).mpr
  refine ⟨c.kernel_le hz,?_⟩
  rw [(c.coordinates_eq_one_iff _).mpr hz]
  exact I.zero_mem

theorem imageSpace_subspacePreimage (I : Submodule (ZMod 2) V) :
    c.imageSpace (c.subspacePreimage I) = I := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff _ v).mp hv
    exact ((c.mem_subspacePreimage I u).mp hu).choose_spec
  · intro v hv
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    apply (c.mem_imageSpace_iff _ v).mpr
    exact ⟨u,(c.mem_subspacePreimage I u).mpr ⟨u.property,hu.symm ▸ hv⟩,hu⟩

/-- A subgroup containing the kernel contains every lift of its coordinate image. -/
theorem subspacePreimage_le_of_imageSpace_le
    (I : Submodule (ZMod 2) V) (B : Subgroup G)
    (hZB : Z ≤ B) (hI : I ≤ c.imageSpace B) :
    c.subspacePreimage I ≤ B := by
  intro x hx
  obtain ⟨hxU,hxI⟩ := (c.mem_subspacePreimage I x).mp hx
  obtain ⟨b,hb,he⟩ := (c.mem_imageSpace_iff B _).mp (hI hxI)
  have he' : c.coordinates b = c.coordinates ⟨x,hxU⟩ :=
    Multiplicative.toAdd.injective he
  have hz : x * (b:G)⁻¹ ∈ Z := by
    apply (c.coordinates_eq_one_iff ((⟨x,hxU⟩ : U) * b⁻¹)).mp
    rw [map_mul,map_inv,he',mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using B.mul_mem (hZB hz) hb

/-- Recover a literal subgroup containing the coordinate kernel. -/
theorem subspacePreimage_imageSpace (B : Subgroup G) (hBU : B ≤ U) (hZB : Z ≤ B) :
    c.subspacePreimage (c.imageSpace B) = B := by
  apply le_antisymm (c.subspacePreimage_le_of_imageSpace_le _ B hZB le_rfl)
  intro b hb
  exact (c.mem_subspacePreimage _ b).mpr
    ⟨hBU hb,(c.mem_imageSpace_iff B _).mpr ⟨⟨b,hBU hb⟩,hb,rfl⟩⟩

theorem subspacePreimage_injective : Function.Injective c.subspacePreimage := by
  intro I J h
  simpa only [c.imageSpace_subspacePreimage] using congrArg c.imageSpace h

theorem subspacePreimage_inf (I J : Submodule (ZMod 2) V) :
    c.subspacePreimage (I ⊓ J) = c.subspacePreimage I ⊓ c.subspacePreimage J := by
  ext x
  constructor
  · intro hx
    obtain ⟨hu,hi,hj⟩ := (c.mem_subspacePreimage (I ⊓ J) x).mp hx
    exact ⟨(c.mem_subspacePreimage I x).mpr ⟨hu,hi⟩,
      (c.mem_subspacePreimage J x).mpr ⟨hu,hj⟩⟩
  · rintro ⟨hi,hj⟩
    obtain ⟨hu,hi⟩ := (c.mem_subspacePreimage I x).mp hi
    obtain ⟨_,hj⟩ := (c.mem_subspacePreimage J x).mp hj
    exact (c.mem_subspacePreimage (I ⊓ J) x).mpr ⟨hu,hi,hj⟩

/-- The subspace correspondence retains literal ambient conjugation. -/
theorem subspacePreimage_map (I : Submodule (ZMod 2) V) (h : H) :
    c.subspacePreimage (I.map (ρ h)) =
      (c.subspacePreimage I).map (MulAut.conj (h : G)).toMonoidHom := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU,v,hv,hvx⟩ := (c.mem_subspacePreimage _ x).mp hx
    let y : U := ⟨(h:G)⁻¹*x*((h:G)⁻¹)⁻¹,
      (mem_normalizer_iff.mp (c.normalized (H.inv_mem h.property)) x).mp hxU⟩
    have hy : (c.coordinates y).toAdd ∈ I := by
      have he := c.equivariant h⁻¹ ⟨x,hxU⟩
      change (c.coordinates y).toAdd = ρ h⁻¹ (c.coordinates ⟨x,hxU⟩).toAdd at he
      rw [he,←hvx]
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
      exact hv
    refine ⟨y,(c.mem_subspacePreimage I y).mpr ⟨y.property,hy⟩,?_⟩
    change (h:G)*((h:G)⁻¹*x*((h:G)⁻¹)⁻¹)*(h:G)⁻¹ = x
    group
  · rintro x ⟨u,hu,rfl⟩
    obtain ⟨huU,huI⟩ := (c.mem_subspacePreimage I u).mp hu
    apply (c.mem_subspacePreimage _ _).mpr
    refine ⟨(mem_normalizer_iff.mp (c.normalized h.property) u).mp huU,?_⟩
    exact ⟨(c.coordinates ⟨u,huU⟩).toAdd,huI,(c.equivariant h ⟨u,huU⟩).symm⟩

/-- The original support normalizer is exactly its coordinate stabilizer. -/
theorem mem_normalizer_subspacePreimage_iff (I : Submodule (ZMod 2) V) (h : H) :
    (h:G) ∈ normalizer (c.subspacePreimage I : Set G) ↔ I.map (ρ h) = I := by
  rw [mem_normalizer_iff_map_conj_eq]
  change (c.subspacePreimage I).map (MulAut.conj (h:G)).toMonoidHom = _ ↔ _
  rw [←c.subspacePreimage_map]
  exact c.subspacePreimage_injective.eq_iff

theorem subspacePreimage_normalized (K : Subgroup G) (hKH : K ≤ H)
    (I : Submodule (ZMod 2) V) (hi : K.subgroupOf H ≤ subspaceStabilizer ρ I) :
    K ≤ normalizer (c.subspacePreimage I : Set G) := by
  intro k hk
  apply (c.mem_normalizer_subspacePreimage_iff I ⟨k,hKH hk⟩).mpr
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    exact (hi hk w).2 hw
  · intro v hv
    refine ⟨ρ (⟨k,hKH hk⟩ : H)⁻¹ v,(hi (K.inv_mem hk) v).2 hv,?_⟩
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

/-- Irr⁺ lifts lie in the original moved subgroup when it contains the kernel. -/
theorem irrPlus_preimage_le_commutator (K : Subgroup G) (hKH : K ≤ H)
    (hZ : Z ≤ ⁅U,K⁆) {I : Submodule (ZMod 2) V}
    (hi : IsIrrPlus ρ (K.subgroupOf H) I) : c.subspacePreimage I ≤ ⁅U,K⁆ := by
  apply c.subspacePreimage_le_of_imageSpace_le I _ hZ
  rw [commutator_comm U K,c.imageSpace_commutator K U hKH le_rfl,c.imageSpace_self]
  rw [←hi.choose_spec.1]
  exact subspaceCommutator_mono_left ρ le_top _

/-- Retain the prescribed subspace when lifting a fixed-moving vector. -/
theorem exists_fixed_moving_subspace_lift
    (I : Submodule (ZMod 2) V) (K S : Subgroup G) (hSH : S ≤ H)
    (v : V) (hv : v ∈ I)
    (hfixed : ∀ (s : G) (hs : s ∈ S), ρ ⟨s,hSH hs⟩ v = v)
    (hmoved : v ∉ Representation.OneCohomology.fixed (ρ.comp (K.subgroupOf H).subtype)) :
    ∃ u ∈ c.subspacePreimage I, (∀ s ∈ S, ⁅u,s⁆ ∈ Z) ∧ ∃ k ∈ K, ⁅u,k⁆ ∉ Z := by
  classical
  obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
  have hu' : (c.coordinates u).toAdd = v := congrArg Multiplicative.toAdd hu
  refine ⟨u,(c.mem_subspacePreimage I u).mpr ⟨u.property,hu'.symm ▸ hv⟩,?_,?_⟩
  · intro s hs
    apply (c.fixed_coordinate_iff_commutator_mem ⟨s,hSH hs⟩ u).mp
    rw [hu']
    exact hfixed s hs
  · by_contra hn
    push Not at hn
    apply hmoved
    intro k
    change ρ k.val v = v
    rw [←hu']
    exact (c.fixed_coordinate_iff_commutator_mem k.val u).mpr (hn k.val k.property)

/-- Distinct Irr⁺ supports may overlap, but their overlap centralizes the
original perfect component. No vanishing of the covering fixed part is used. -/
theorem irrPlus_preimages_central_intersection (K : Subgroup G) [Group.IsPerfect K]
    (hKH : K ≤ H) (hZK : Z ≤ centralizer (K : Set G))
    {I J : Submodule (ZMod 2) V}
    (hi : IsIrrPlus ρ (K.subgroupOf H) I) (hj : IsIrrPlus ρ (K.subgroupOf H) J)
    (hne : I ≠ J) :
    c.subspacePreimage I ⊓ c.subspacePreimage J ≤ centralizer (K : Set G) := by
  have hsep := (hi.le_or_inf_sup_fixedSpace_le ρ hj.choose).resolve_left
    (fun h => hne (hi.eq_of_le ρ hj h))
  apply centralizes_of_commutator_le_centralizer K
  rw [commutator_comm]
  apply le_trans (c.commutator_le_of_imageSpace_fixed K _ hKH
    (inf_le_left.trans (c.subspacePreimage_le I)) ?_) hZK
  rw [←c.subspacePreimage_inf,c.imageSpace_subspacePreimage]
  exact (inf_le_inf_left I le_sup_left).trans hsep

/-- Every distinct conjugate has the central overlap and normalization used
by the source fixed-moving argument. -/
theorem irrPlus_preimage_separated (K : Subgroup G) [Group.IsPerfect K]
    (hKH : K ≤ H) (hZK : Z ≤ centralizer (K : Set G))
    {I : Submodule (ZMod 2) V} (hi : IsIrrPlus ρ (K.subgroupOf H) I)
    (h : H) (hn : (h:G) ∈ normalizer (K : Set G))
    (hm : (h:G) ∉ normalizer (c.subspacePreimage I : Set G)) :
    c.subspacePreimage I ⊓ (c.subspacePreimage I).map (MulAut.conj (h:G)).toMonoidHom ≤
        centralizer (K : Set G) ∧
      K ≤ normalizer (((c.subspacePreimage I).map (MulAut.conj (h:G)).toMonoidHom) : Set G) := by
  have hnh : h ∈ normalizer (K.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hKH]
    exact hn
  have hj := hi.map_normalizer ρ hnh
  rw [←c.subspacePreimage_map]
  refine ⟨c.irrPlus_preimages_central_intersection K hKH hZK hi hj ?_,
    c.subspacePreimage_normalized K hKH _ hj.choose⟩
  intro he
  exact hm ((c.mem_normalizer_subspacePreimage_iff I h).mpr he.symm)

end Representation.BinaryConjugationSection
