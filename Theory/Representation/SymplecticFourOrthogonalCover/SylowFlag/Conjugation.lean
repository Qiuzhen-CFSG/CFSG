module

public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Geometry

/-!
# Transport to every actual derived Sylow

Sylow conjugacy transports both linear actions through the original projection.
The fixed-space and unique singular-point conclusions therefore hold for the
source-selected flag of every Sylow, with no additional alignment assumption.
The general transport proofs follow the G₂ cover's `SylowFlag/Conjugation`.

Source: Aschbacher–Smith, I.2.3(1a),(2), printed p.413 / PDF p.424.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup
open Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
set_option linter.unusedSectionVars false

namespace Transport
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Conjugation of an actual subgroup, with its original embedding. -/
def conjugate (g : G) (T : Subgroup G) : Subgroup G :=
  T.map (MulAut.conj g).toMonoidHom

/-- The linear equivalence supplied by an actual group element. -/
def linear (ρ : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  { ρ g with
    invFun := ρ g⁻¹
    left_inv := ρ.inv_self_apply g
    right_inv := ρ.self_inv_apply g }

theorem conjugate_action (ρ : Representation k G V) (g h : G) (x : V) :
    ρ ((MulAut.conj g) h) (ρ g x) = ρ g (ρ h x) := by
  simp [MulAut.conj_apply, map_mul, Module.End.mul_apply]

theorem fixed_conjugate (ρ : Representation k G V) (g : G) (T : Subgroup G) :
    fixed (ρ.comp (conjugate g T).subtype) = (fixed (ρ.comp T.subtype)).map (ρ g) := by
  apply le_antisymm
  · intro x hx
    refine ⟨ρ g⁻¹ x, ?_, ρ.self_inv_apply g x⟩
    intro t
    change ρ t.val (ρ g⁻¹ x) = ρ g⁻¹ x
    apply (ρ.apply_bijective g).injective
    rw [← conjugate_action ρ g t.val, ρ.self_inv_apply]
    exact hx ⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩
  · rintro x ⟨y,hy,rfl⟩ ⟨h,hh⟩
    obtain ⟨t,ht,rfl⟩ := hh
    change ρ ((MulAut.conj g) t) (ρ g y) = ρ g y
    rw [conjugate_action, show ρ t y = y from hy ⟨t,ht⟩]

theorem invariant_map (ρ : Representation k G V) (g : G) (T : Subgroup G)
    (W : Submodule k V) (hW : ∀ t : T, W ≤ W.comap (ρ t.val)) :
    ∀ t : conjugate g T, W.map (ρ g) ≤ (W.map (ρ g)).comap (ρ t.val) := by
  rintro ⟨h,hh⟩ x ⟨y,hy,rfl⟩
  obtain ⟨t,ht,rfl⟩ := hh
  exact ⟨ρ t y, hW ⟨t,ht⟩ hy, (conjugate_action ρ g t y).symm⟩

theorem invariant_comap (ρ : Representation k G V) (g : G) (T : Subgroup G)
    (W : Submodule k V) (hW : ∀ t : conjugate g T, W ≤ W.comap (ρ t.val)) :
    ∀ t : T, W.comap (ρ g) ≤ (W.comap (ρ g)).comap (ρ t.val) := by
  intro t x hx
  change ρ g (ρ t.val x) ∈ W
  rw [← conjugate_action]
  exact hW ⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩ hx

theorem finrank_map (ρ : Representation k G V) (g : G) (W : Submodule k V) :
    Module.finrank k (W.map (ρ g)) = Module.finrank k W :=
  (linear ρ g).finrank_map_eq W

theorem finrank_comap (ρ : Representation k G V) (g : G) (W : Submodule k V) :
    Module.finrank k (W.comap (ρ g)) = Module.finrank k W := by
  rw [← finrank_map ρ g (W.comap (ρ g)),
    Submodule.map_comap_eq_of_surjective (ρ.apply_bijective g).surjective]

theorem central_conjugate (g : G) (T S : Subgroup G)
    (hS : S ≤ (Subgroup.center T).map T.subtype) :
    conjugate g S ≤ (Subgroup.center (conjugate g T)).map (conjugate g T).subtype := by
  rintro z ⟨s,hs,rfl⟩
  obtain ⟨t,ht,rfl⟩ := hS hs
  refine ⟨⟨(MulAut.conj g) t.val, ⟨t.val,t.property,rfl⟩⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  rintro ⟨h,hh⟩
  obtain ⟨u,hu,rfl⟩ := hh
  apply Subtype.ext
  change (MulAut.conj g) u * (MulAut.conj g) t.val =
    (MulAut.conj g) t.val * (MulAut.conj g) u
  rw [← map_mul, ← map_mul]
  exact congrArg (MulAut.conj g) (congrArg Subtype.val
    (Subgroup.mem_center_iff.mp ht ⟨u,hu⟩))

end Transport

def movedPoint (g : L (K := K)) := (singularPoint (K := K)).map (action g)
def movedLine (g : L (K := K)) := (firstLine (K := K)).map (symplecticDerivedNatural 2 g)
def movedPlane (g : L (K := K)) := (secondPlane (K := K)).map (symplecticDerivedNatural 2 g)
def movedRoot (g : L (K := K)) := Transport.conjugate g (transvectionRoot (K := K))
def movedSylow (g : L (K := K)) := Transport.conjugate g (standard (K := K))

lemma movedSylow_coe (g : L (K := K)) :
    ((g • standardSylow : Sylow 2 (L (K := K))) : Subgroup (L (K := K))) = movedSylow g := by
  rw [Sylow.coe_subgroup_smul, standardSylow_coe]
  rfl

lemma moved_preimage (g : L (K := K)) (N : Submodule K (Natural (K := K))) :
    (N.map (symplecticDerivedNatural 2 g)).comap projection.toLinearMap =
      (N.comap projection.toLinearMap).map (action g) := by
  apply le_antisymm
  · rintro x ⟨v,hv,hvx⟩
    refine ⟨action g⁻¹ x, ?_, (action (K := K)).self_inv_apply g x⟩
    change projection (action g⁻¹ x) ∈ N
    have he : projection (action g⁻¹ x) = v := by
      apply ((symplecticDerivedNatural 2).apply_bijective g).injective
      rw [projection.isIntertwining, (symplecticDerivedNatural 2).self_inv_apply]
      exact hvx.symm
    rw [he]
    exact hv
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨projection y,hy,rfl⟩

lemma radical_map (g : L (K := K)) : (radical (K := K)).map (action g) = radical := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    rw [radical_fixed hy g]
    exact hy
  · intro x hx
    exact ⟨x,hx,radical_fixed hx g⟩

lemma movedLine_fixed (g : L (K := K)) :
    fixed ((symplecticDerivedNatural 2).comp (movedSylow g).subtype) = movedLine g := by
  rw [movedSylow, Transport.fixed_conjugate, natural_fixed]
  rfl

lemma moved_cover_fixed (g : L (K := K)) :
    fixed ((action (K := K)).comp (movedSylow g).subtype) =
      (movedLine g).comap projection.toLinearMap := by
  rw [fixed_preimage, movedLine_fixed]

lemma movedLine_preimage (g : L (K := K)) :
    (movedLine g).comap projection.toLinearMap = movedPoint g ⊔ radical := by
  rw [movedLine, moved_preimage, first_preimage_eq, Submodule.map_sup, radical_map]
  rfl

lemma movedPoint_disjoint (g : L (K := K)) : Disjoint (movedPoint g) radical := by
  rw [← radical_map g]
  exact Submodule.disjoint_map ((action (K := K)).apply_bijective g).injective singularPoint_disjoint

lemma movedPoint_finrank (g : L (K := K)) : Module.finrank K (movedPoint g) = 1 :=
  (Transport.finrank_map _ _ _).trans singularPoint_finrank

lemma movedLine_finrank (g : L (K := K)) : Module.finrank K (movedLine g) = 1 :=
  (Transport.finrank_map _ _ _).trans firstLine_finrank

lemma movedPlane_finrank (g : L (K := K)) : Module.finrank K (movedPlane g) = 2 :=
  (Transport.finrank_map _ _ _).trans secondPlane_finrank

lemma moved_preimage_finrank (g : L (K := K)) :
    Module.finrank K ((movedLine g).comap projection.toLinearMap) = 2 := by
  rw [movedLine, moved_preimage, Transport.finrank_map, first_preimage_finrank]

lemma movedLine_invariant (g : L (K := K)) :
    ∀ t : movedSylow g, movedLine g ≤ (movedLine g).comap (symplecticDerivedNatural 2 t.val) :=
  Transport.invariant_map (symplecticDerivedNatural (k := K) 2) g standard firstLine firstLine_invariant

lemma movedPlane_invariant (g : L (K := K)) :
    ∀ t : movedSylow g, movedPlane g ≤ (movedPlane g).comap (symplecticDerivedNatural 2 t.val) :=
  Transport.invariant_map (symplecticDerivedNatural (k := K) 2) g standard secondPlane secondPlane_invariant

lemma movedLine_unique (g : L (K := K)) (W : Submodule K (Natural (K := K)))
    (hW : ∀ t : movedSylow g, W ≤ W.comap (symplecticDerivedNatural 2 t.val))
    (hdim : Module.finrank K W = 1) : W = movedLine g := by
  have he := invariant_line_unique (W.comap (symplecticDerivedNatural 2 g))
    (Transport.invariant_comap _ g standard W hW)
    ((Transport.finrank_comap _ _ _).trans hdim)
  have hm := congrArg (Submodule.map (symplecticDerivedNatural 2 g)) he
  rw [Submodule.map_comap_eq_of_surjective ((symplecticDerivedNatural 2).apply_bijective g).surjective] at hm
  exact hm

lemma movedPlane_unique (g : L (K := K)) (W : Submodule K (Natural (K := K)))
    (hW : ∀ t : movedSylow g, W ≤ W.comap (symplecticDerivedNatural 2 t.val))
    (hdim : Module.finrank K W = 2) : W = movedPlane g := by
  have he := invariant_plane_unique (W.comap (symplecticDerivedNatural 2 g))
    (Transport.invariant_comap _ g standard W hW)
    ((Transport.finrank_comap _ _ _).trans hdim)
  have hm := congrArg (Submodule.map (symplecticDerivedNatural 2 g)) he
  rw [Submodule.map_comap_eq_of_surjective ((symplecticDerivedNatural 2).apply_bijective g).surjective] at hm
  exact hm

lemma moved_singular_iff (g : L (K := K)) (x : Space (K := K))
    (hx : x ∈ (movedLine g).comap projection.toLinearMap) :
    ClassicalOrthogonal.formB 2 K x = 0 ↔ x ∈ movedPoint g := by
  rw [movedLine, moved_preimage] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  rw [action_preserves]
  constructor
  · intro hq
    exact ⟨y,(singular_iff y hy).mp hq,rfl⟩
  · rintro ⟨z,hz,he⟩
    have hzy := ((action (K := K)).apply_bijective g).injective he
    rw [← hzy]
    exact singularPoint_singular z hz

lemma moved_singular_unique (g : L (K := K)) (P : Submodule K (Space (K := K)))
    (hP : P ≤ (movedLine g).comap projection.toLinearMap) (hdim : Module.finrank K P = 1)
    (hq : ∀ x ∈ P, ClassicalOrthogonal.formB 2 K x = 0) : P = movedPoint g := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    exact (moved_singular_iff g x (hP hx)).mp (hq x hx)
  · rw [hdim, movedPoint_finrank]

lemma movedRoot_central (g : L (K := K)) :
    movedRoot g ≤ (Subgroup.center (movedSylow g)).map (movedSylow g).subtype :=
  Transport.central_conjugate g standard transvectionRoot transvectionRoot_central

lemma exists_marking (S : Sylow 2 (L (K := K))) :
    ∃ g : L (K := K), (S : Subgroup (L (K := K))) = movedSylow g := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (L (K := K)) standardSylow S
  exact ⟨g,hg ▸ movedSylow_coe g⟩

lemma movedPoint_singular (g : L (K := K)) (x : Space (K := K)) (hx : x ∈ movedPoint g) :
    ClassicalOrthogonal.formB 2 K x = 0 := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [action_preserves]
  exact singularPoint_singular y hy

lemma movedLine_le_plane (g : L (K := K)) : movedLine g ≤ movedPlane g := by
  apply Submodule.map_mono
  rw [firstLine_eq_point, secondPlane_eq_plane]
  exact point_le_plane

lemma movedLine_isotropic (g : L (K := K)) (x y : Natural (K := K))
    (hx : x ∈ movedLine g) (hy : y ∈ movedLine g) :
    (ClassicalOrthogonal.formD 2 K).polarBilin x y = 0 := by
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  rw [polar_invariant]
  exact firstLine_isotropic u v hu hv

lemma movedPlane_isotropic (g : L (K := K)) (x y : Natural (K := K))
    (hx : x ∈ movedPlane g) (hy : y ∈ movedPlane g) :
    (ClassicalOrthogonal.formD 2 K).polarBilin x y = 0 := by
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  rw [polar_invariant]
  exact secondPlane_isotropic u v hu hv

end Representation.SymplecticFourOrthogonalCover.SylowFlag
