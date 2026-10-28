module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates

/-!
# Normal elementary planes and the marked involution classes

The dihedral base normalizes all four elementary products, while the Sylow
normalizes the two diagonal products. The marked t and z lie in A, but a
conjugate of t always has an identity base coordinate whereas z has neither.
The base centralizes t. Only square-dihedral coordinate checks are finite.

Source: Aschbacher–Smith 13.9.2(1,3–6), printed p.969 (PDF p.986).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private instance (b : Bool) : DecidablePred (·∈(plane b).map square) := fun x=>
  inferInstanceAs (Decidable (∃a,a∈plane b ∧ square a=x))

private theorem square_plane_normal (b : Bool) : ∀a : D8, ∀x:S4,
    x∈(plane b).map square → square a*x*(square a)⁻¹∈(plane b).map square := by
  cases b <;> decide +kernel

theorem J_le_normalizer_elementary (b c : Bool) : J≤normalizer (elementary b c:Set W) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have hx' := (mem_elementary b c x).mp hx
    have hg' := (mem_J g).mp hg
    apply (mem_elementary b c _).mpr
    refine ⟨by change (g*x*g⁻¹).right=1;simp [hx'.1],?_,?_⟩
    · change (g*x*g⁻¹).left 1∈_
      rw [conjugate_left g x hx'.1, hg'.1,inv_one,one_mul]
      obtain ⟨a,ha⟩ := hg'.2 1
      rw [←ha]
      exact square_plane_normal b a _ hx'.2.1
    · change (g*x*g⁻¹).left turn∈_
      rw [conjugate_left g x hx'.1,hg'.1,inv_one,one_mul]
      obtain ⟨a,ha⟩ := hg'.2 turn
      rw [←ha]
      exact square_plane_normal c a _ hx'.2.2
  · rw [card_map_of_injective (MulAut.conj g).injective]

theorem standardSylow_le_normalizer_diagonal (b : Bool) :
    (standardSylow:Subgroup W)≤normalizer (elementary b b:Set W) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have hx' := (mem_elementary b b x).mp hx
    have hxall (i : C2) : x.left i∈(plane b).map square := by
      rcases c2_eq_one_or_turn i with rfl|rfl
      · exact hx'.2.1
      · exact hx'.2.2
    have hall (i : C2) : (g*x*g⁻¹).left i∈(plane b).map square := by
      rw [conjugate_left g x hx'.1]
      obtain ⟨a,ha⟩ := (mem_standardSylow g).mp hg i
      rw [←ha]
      exact square_plane_normal b a _ (hxall _)
    exact (mem_elementary b b _).mpr ⟨by change (g*x*g⁻¹).right=1;simp [hx'.1],hall 1,hall turn⟩
  · rw [card_map_of_injective (MulAut.conj g).injective]

theorem t_mem_A : t∈A := by rw [mem_elementary];decide +kernel

theorem z_mem_A : z∈A := by rw [mem_elementary];decide +kernel

private theorem conjugate_t_has_identity_coordinate (g : W) :
    (g*t*g⁻¹).left (g.right*turn)=1 := by
  rw [conjugate_left g t rfl]
  simp [t,factor,turn_ne_one]

theorem not_isConj_t_z : ¬IsConj t z := by
  intro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have h := conjugate_t_has_identity_coordinate g
  have he : g*t*g⁻¹=z := hg
  rw [he] at h
  have hn (i : C2) : z.left i≠1 := by
    revert i
    decide +kernel
  exact hn _ h

theorem J_le_centralizer_t : J≤centralizer ({t}:Set W) := by
  rintro x hx
  obtain ⟨x,⟨a,rfl⟩,rfl⟩ := hx
  apply mem_centralizer_singleton_iff.mpr
  apply RegularWreathProduct.ext
  · funext i
    have hh : ∀a:D8×D8,∀i:C2,
        ((sylowEmbedding (pair a))*t).left i=(t*(sylowEmbedding (pair a))).left i := by
      decide +kernel
    exact hh a i
  · rfl
end SymmetricFourWreath
