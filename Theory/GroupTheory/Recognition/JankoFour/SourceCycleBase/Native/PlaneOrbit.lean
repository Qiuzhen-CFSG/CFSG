module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit.Checks
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit.Seeds
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneCardinality
/-!
# Plane hitting in the native trio geometry

The checked forest and the independent count of 1771 sextets cover every
native plane. Each root has an octad pencil consisting of near trios, and
literal M₂₄ permutations transport this property. Discs and ovals meet that
pencil, proving the coplanarity distance bound (3.11.2) for any two planes.
All actions are the original actions on point subsets.

Source: Aschbacher–Segev (1991), (3.11.2), p.596, used in (7.6), p.604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
@[simp] theorem smulPlane_parts (g : M24) (π : Plane) : (g • π).parts = g • π.parts := rfl

/-- A whole octad pencil in the second plane is near the first plane. -/
def PencilNear (π σ : Plane) : Prop := ∃ A, PlaneOctad σ A ∧
  ∀ l, Incident l σ → A ∈ l.parts → NearPlane π l

theorem pencilNear_transport (g : M24) {π σ : Plane} (h : PencilNear π σ) :
    PencilNear (g • π) (g • σ) := by
  obtain ⟨A,hA,h⟩ := h
  refine ⟨g • A,planeOctad_transport g rfl hA,?_⟩
  intro l hl hAl
  have hi : Incident (g⁻¹ • l) σ := incident_transport g⁻¹ rfl (by simp) hl
  have hm : A ∈ (g⁻¹ • l).parts := by
    simpa only [smulLine_parts,inv_smul_smul] using Finset.smul_mem_smul_finset (a := g⁻¹) hAl
  exact nearPlane_transport g (by simp) rfl (h _ hi hm)

namespace PlaneOrbit
open FarOrbit (support)
def parts (a : Fin 6 → BitVec 24) : Finset (Finset (Fin 24)) := (masks a).image support

theorem parts_transport (g : M24) (a b : Fin 6 → BitVec 24)
    (he : (masks a).image (m24PermuteMask g.val) = masks b) : g • parts a = parts b := by
  simp only [parts]
  rw [←he,Finset.image_image]
  change ((masks a).image support).image (g • ·) = _
  rw [Finset.image_image]
  apply Finset.image_congr
  intro v _
  exact (FarOrbit.support_permute g.val v).symm

theorem seed_parts (r : Fin 4) : parts (row (seed r)).masks = (rootPlane r).parts := by
  revert r; decide +kernel

theorem exists_transport (i : Fin 1771) : ∃ g : sextetStabilizer standardSextet,
    (g : M24) • (rootPlane (row i).root).parts = parts (row i).masks := by
  generalize hn : (row i).depth = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    have hc := (all_rows i).1.2
    by_cases hz : (row i).depth = 0
    · rw [if_pos hz] at hc
      refine ⟨1,?_⟩
      rw [Subgroup.coe_one,one_smul]
      conv_rhs => rw [hc]
      exact (seed_parts _).symm
    · rw [if_neg hz] at hc
      obtain ⟨g,hg⟩ := ih (row (row i).parent).depth (by omega) (row i).parent rfl
      refine ⟨FarOrbit.nativeGenerator (row i).generator * g,?_⟩
      rw [Subgroup.coe_mul,mul_smul,←hc.2.1,hg]
      exact parts_transport (FarOrbit.nativeGenerator (row i).generator : M24) _ _ hc.2.2

noncomputable def entry (i : Fin 1771) : Plane :=
  ((exists_transport i).choose : M24) • rootPlane (row i).root

theorem entry_parts (i : Fin 1771) : (entry i).parts = parts (row i).masks :=
  (exists_transport i).choose_spec

theorem key_strictMono : StrictMono key := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact (all_rows i.castSucc).2 (Nat.succ_lt_succ i.isLt)

theorem entry_injective : Function.Injective entry := by
  intro i j he
  have hp := congrArg Sextet.parts he
  rw [entry_parts,entry_parts] at hp
  have low (i j : Fin 1771) (hp : parts (row i).masks = parts (row j).masks) : key j ≤ key i := by
    have hi : support ((row i).masks 0) ∈ parts (row j).masks := by
      rw [←hp]
      exact Finset.mem_image.mpr ⟨(row i).masks 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,rfl⟩
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hi
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    have he' := FarOrbit.support_injective he
    have hlow := (all_rows j).1.1 a
    change ((row j).masks 0).toNat ≤ ((row i).masks 0).toNat
    rwa [he'] at hlow
  exact key_strictMono.injective (Nat.le_antisymm (low j i hp.symm) (low i j hp))

theorem entry_surjective : Function.Surjective entry :=
  (entry_injective.bijective_of_nat_card_le (by rw [plane_card,Nat.card_fin])).2

theorem standard_pencil_near (σ : Plane) : PencilNear standardSextet σ := by
  obtain ⟨i,rfl⟩ := entry_surjective σ
  let g := (exists_transport i).choose
  have hg : (g : M24) • standardSextet = standardSextet := plane_parts_injective g.property
  have hp := pencilNear_transport (g : M24) (root_pencil (row i).root)
  rw [hg] at hp
  exact hp
end PlaneOrbit

/-- The intrinsic form of (3.11.2): every plane contains an octad pencil
whose three trios are coplanar with trios of the prescribed plane. -/
theorem pencil_near (π σ : Plane) : PencilNear π σ := by
  obtain ⟨g,hg⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator π
  have hp := pencilNear_transport g (PlaneOrbit.standard_pencil_near (g⁻¹ • σ))
  have he : g • standardSextet = π := plane_parts_injective hg
  simpa only [he,smul_inv_smul] using hp

open Theory.SpecificGroups.SymmetricSix in
/-- AS91 (3.11.2), for the actual native residue and any tetrad labeling. -/
theorem residue_hits_plane (σ π : Plane) (e : Fin 6 ≃ {A // A ∈ σ.parts})
    (S : Finset Theory.SpecificGroups.SymmetricSix.Syntheme)
    (hS : Polar.Oval S ∨ ∃ s, S = Polar.disc s) :
    ∃ l : {l : Line // Incident l σ}, residueEquiv σ e l ∈ S ∧ NearPlane π l.val := by
  obtain ⟨A,hA,hnear⟩ := pencil_near π σ
  obtain ⟨a,ha⟩ := planeOctad_duad σ e hA
  have hit : ∃ s, s ∈ S ∧ incident a s := by
    rcases hS with ho | ⟨s,rfl⟩
    · obtain ⟨s,hs,_⟩ := Polar.oval_hits_pencil S ho a
      exact ⟨s,hs⟩
    · exact disc_hits_pencil s a
  obtain ⟨s,hs,has⟩ := hit
  let l := (residueEquiv σ e).symm s
  have he := (residueEquiv σ e).apply_symm_apply s
  refine ⟨l,he.symm ▸ hs,hnear l.val l.property ?_⟩
  rw [←ha]
  exact (residueEquiv_incidence σ e l a).mp (he.symm ▸ has)
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
