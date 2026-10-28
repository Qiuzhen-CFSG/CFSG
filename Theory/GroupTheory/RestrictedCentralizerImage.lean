module

public import Theory.GroupTheory.RestrictedImageSection
public import Theory.GroupTheory.Centralizer

/-!
# Literal images of restricted centralizers

This is the map/comap calculation needed for the paired Baumann factors.  A
section on the full centralizer image restricts to the Baumann preimage, so
the image of `R ⊓ C(A)` is exactly the intersection of the Baumann image with
the marked centralizer axis.
-/

public section
open Subgroup
namespace Theory.GroupTheory

variable {G H : Type*} [Group G] [Group H]

theorem map_inf_centralizer_eq_of_section
    (q : G →* H) (Y F O : Subgroup H) (R A P : Subgroup G)
    (hR : R = F.comap q)
    (hP : P = Y.comap q ⊓ centralizer (A : Set G))
    (hPmap : P.map q = O)
    (hFY : F ≤ Y)
    (hsection : ∃ σ : P.map q →* P,
      (q.comp P.subtype).comp σ = (P.map q).subtype) :
    (R ⊓ centralizer (A : Set G)).map q = F ⊓ O := by
  obtain ⟨σ,hσ⟩ := hsection
  have hFsub : F ⊓ O ≤ P.map q := by
    rw [hPmap]
    exact inf_le_right
  obtain ⟨τ,hτ,hτP⟩ := exists_restricted_subgroup_comap_section q P R F (F ⊓ O)
    σ hσ hR hFsub inf_le_left
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hxR : (x : G) ∈ R := hx.1
    have hxA : (x : G) ∈ centralizer (A : Set G) := hx.2
    have hqxF : q (x : G) ∈ F := by
      rw [hR] at hxR
      exact hxR
    have hqxC : q (x : G) ∈ centralizer (A.map q : Set H) := by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := ha
      have hh := hxA b hb
      simpa only [map_mul] using congrArg q hh
    have hqxY : q (x : G) ∈ Y := hFY hqxF
    have hqxO : q (x : G) ∈ O := by
      rw [← hPmap]
      refine ⟨(x : G), ?_, rfl⟩
      rw [hP]
      exact ⟨hqxY, hxA⟩
    exact ⟨hqxF,hqxO⟩
  · intro y hy
    let z : ↥(F ⊓ O) := ⟨y, hy⟩
    have hzP : (τ z : G) ∈ P := hτP z
    have hzA : (τ z : G) ∈ centralizer (A : Set G) := by
      rw [hP] at hzP
      exact hzP.2
    have hzR : (τ z : G) ∈ R := by
      exact (τ z).property
    refine ⟨τ z,⟨hzR,hzA⟩,?_⟩
    exact DFunLike.congr_fun hτ z

end Theory.GroupTheory
