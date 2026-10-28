module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# Displacement of actors fixing a symplectic plane pointwise

For the actual natural symplectic matrix action, a pointwise-fixed
self-orthogonal plane contains every displacement. The proof pairs a
displacement against the fixed plane and uses preservation of the original
form. Under a marked quotient of an ambient normal subgroup, centralizing
lifts of that plane therefore bounds the ambient commutator by those lifts
and the literal kernel. No central complement is chosen.

Source application: the first symplectic calculation in MS93 (3.3),
printed p.867, where the image of the critical commutator is an isotropic
plane in the natural quotient.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

/-- Displacement by an actor fixing a subspace is perpendicular to it. -/
theorem displacement_mem_orthogonal_of_fixed
    (U : Submodule F (Vector F)) (g : Sp F)
    (hfix : ∀ u ∈ U, g • u = u) (v : Vector F) :
    g • v-v ∈ (form F).orthogonal U := by
  intro u hu
  change form F u (g • v-v) = 0
  rw [map_sub]
  have h := preserves_form g u v
  rw [hfix u hu] at h
  exact sub_eq_zero.mpr h

/-- A pointwise-fixed self-orthogonal plane contains all natural displacement. -/
theorem displacement_mem_of_self_orthogonal
    (U : Submodule F (Vector F)) (hU : (form F).orthogonal U = U)
    (g : Sp F) (hfix : ∀ u ∈ U, g • u = u) (v : Vector F) :
    g • v-v ∈ U := by
  rw [←hU]
  exact displacement_mem_orthogonal_of_fixed U g hfix v

/-- The displacement bound lifts through the original subgroup map. The
kernel remains joined to the selected plane lifts, so central attachments
are retained even when they do not split. -/
theorem commutator_le_plane_sup_kernel
    {G : Type*} [Group G] (N Y D : Subgroup G) (hDN : D ≤ N)
    (hn : Y ≤ normalizer (N : Set G))
    (π : N →* Multiplicative (Vector F)) (α : Y →* Sp F)
    (hact : ∀ (y : Y) (n : N),
      π ⟨y.val*n.val*y.val⁻¹,(mem_normalizer_iff.mp (hn y.property) n).mp n.property⟩ =
        Multiplicative.ofAdd (α y • (π n).toAdd))
    (U : Submodule F (Vector F)) (hU : (form F).orthogonal U = U)
    (hcover : ∀ u ∈ U, ∃ d : D, (π ⟨d.val,hDN d.property⟩).toAdd = u)
    (hc : Y ≤ centralizer (D : Set G)) :
    ⁅N,Y⁆ ≤ D ⊔ π.ker.map N.subtype := by
  have hfix (y : Y) : ∀ u ∈ U, α y • u = u := by
    intro u hu
    obtain ⟨d,hd⟩ := hcover u hu
    have hconj : y.val*d.val*y.val⁻¹ = d.val := by
      have hh := hc y.property d.val d.property
      rw [←hh,mul_inv_cancel_right]
    have he := hact y ⟨d.val,hDN d.property⟩
    have heq : (⟨y.val*d.val*y.val⁻¹,
        (mem_normalizer_iff.mp (hn y.property) d.val).mp (hDN d.property)⟩ : N) =
        ⟨d.val,hDN d.property⟩ := Subtype.ext hconj
    rw [heq] at he
    have hh := congrArg Multiplicative.toAdd he
    simpa only [hd,toAdd_ofAdd] using hh.symm
  rw [commutator_comm]
  apply commutator_le.mpr
  intro y hy n hnN
  have hcn : ⁅y,n⁆ ∈ N :=
    le_normalizer_iff_commutator_le_right.mp hn (commutator_mem_commutator hy hnN)
  let c : N := ⟨⁅y,n⁆,hcn⟩
  have he : π c =
      π ⟨y*n*y⁻¹,(mem_normalizer_iff.mp (hn hy) n).mp hnN⟩ * (π ⟨n,hnN⟩)⁻¹ := by
    rw [←map_inv,←map_mul]
    rfl
  have hv : (π c).toAdd ∈ U := by
    rw [he,hact ⟨y,hy⟩ ⟨n,hnN⟩]
    simpa only [toAdd_mul,toAdd_inv,toAdd_ofAdd,sub_eq_add_neg] using
      displacement_mem_of_self_orthogonal U hU (α ⟨y,hy⟩) (hfix ⟨y,hy⟩)
        (π ⟨n,hnN⟩).toAdd
  obtain ⟨d,hd⟩ := hcover (π c).toAdd hv
  let k : N := c * (⟨d.val,hDN d.property⟩ : N)⁻¹
  have hk : k ∈ π.ker := by
    change π k = 1
    rw [map_mul,map_inv]
    exact mul_inv_eq_one.mpr (Multiplicative.toAdd.injective hd.symm)
  have hk' : k.val ∈ π.ker.map N.subtype := mem_map_of_mem N.subtype hk
  have hm := (D ⊔ π.ker.map N.subtype).mul_mem (mem_sup_right hk') (mem_sup_left d.property)
  change (⁅y,n⁆*d.val⁻¹)*d.val ∈ D ⊔ π.ker.map N.subtype at hm
  simpa only [inv_mul_cancel_right] using hm

end Theory.SpecificGroups.SymplecticFour
