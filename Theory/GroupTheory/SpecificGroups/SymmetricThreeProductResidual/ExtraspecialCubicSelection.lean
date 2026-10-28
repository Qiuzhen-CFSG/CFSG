module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeCubicLifts
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# Invariant cubic directions above a symmetric-three square

Let an extraspecial normal subgroup P of order 27 and exponent three map
onto the odd residual of S₃ × S₃ with kernel Z(P). The preimage of one
alternating factor meets P in order nine. Coprime complements then give
two invariant noncentral cubic generators. If an actor moves the image
of P, it moves at least one generator, whose image is faithful.

Source application: Aschbacher--Smith 15.2.6, printed p.1109, selecting
the cubic star subgroup in the extraspecial Omega residual.
-/

public section
open Subgroup
namespace SymmetricThreeProductResidual
variable {D : Type*} [Group D] [Finite D]

private theorem cubic_disjoint_kernel (P C : Subgroup D) [IsExtraspecial 3 P]
    (f : D →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hk : (f.domRestrict P).ker = center P)
    (hCP : C ≤ P) (hc : Nat.card C = 3)
    (hne : C ≠ (center P).map P.subtype) : Disjoint C f.ker := by
  let K := f.ker.subgroupOf C
  let : Fact (Nat.Prime (Nat.card C)) := ⟨hc ▸ Nat.prime_three⟩
  rcases K.eq_bot_or_eq_top_of_prime_card with he | he
  · apply disjoint_def.mpr
    intro x hx hfx
    have hh : (⟨x,hx⟩ : C) ∈ K := hfx
    rw [he] at hh
    exact congrArg C.subtype hh
  · have hCZ : C ≤ (center P).map P.subtype := by
      intro x hx
      have hfx : f x = 1 := show (⟨x,hx⟩ : C) ∈ K from he ▸ mem_top _
      have hz : (⟨x,hCP hx⟩ : P) ∈ center P := hk ▸ hfx
      exact mem_map_of_mem P.subtype hz
    exact (hne (eq_of_le_of_card_ge hCZ (by
      rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P,hc]))).elim

/-- A moving actor detects a faithful invariant cubic in the extraspecial cover. -/
theorem exists_extraspecial_cubic_moved_by_square_actor
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (f : D →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (him : P.map f = pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hk : (f.domRestrict P).ker = center P)
    (S R : Subgroup D) (hS : IsPGroup 2 S)
    (hm : ¬ R.map f ≤ centralizer (P.map f : Set _)) :
    ∃ C : Subgroup D, C ≤ P ∧ Nat.card C = 3 ∧
      S ≤ normalizer (C : Set D) ∧ Disjoint C f.ker ∧
      ¬ R.map f ≤ centralizer (C.map f : Set _) := by
  let F := (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3)))
  have hF : Nat.card F = 3 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
      card_bot,mul_one,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hFP : F ≤ P.map f := by rw [him,residual_eq]; exact prod_mono le_rfl bot_le
  let N := F.comap f
  let g := f.domRestrict P
  let J := N.subgroupOf P
  have hZ : center P ≤ J := by
    intro x hx
    change f (x : D) ∈ F
    have hh : x ∈ (f.domRestrict P).ker := hk.symm ▸ hx
    rw [show f (x : D) = 1 from hh]
    exact F.one_mem
  have hJmap : J.map g = F := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx
    · intro x hx
      obtain ⟨p,hp,he⟩ := hFP hx
      exact ⟨⟨p,hp⟩,show f p ∈ F from he.symm ▸ hx,he⟩
  have hker : (g.comp J.subtype).ker = (center P).subgroupOf J := by
    change g.ker.comap J.subtype = _
    rw [hk]
    rfl
  have hJ : Nat.card J = 9 := by
    have hh := (g.comp J.subtype).ker.card_mul_index
    rw [index_ker,MonoidHom.range_comp,range_subtype,hJmap,hF,hker,
      Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv,
      IsExtraspecial.center_order_p 3 P] at hh
    omega
  obtain ⟨C,E,hCP,hEP,hCc,hEc,hCZ,hEZ,hgen,hSC,hSE⟩ :=
    IsExtraspecial.cubic_generators_of_normal_nine P hP hexp N hJ hZ S hS
  have hCk := cubic_disjoint_kernel P C f hk hCP hCc hCZ
  have hEk := cubic_disjoint_kernel P E f hk hEP hEc hEZ
  by_cases hCm : R.map f ≤ centralizer (C.map f : Set _)
  · refine ⟨E,hEP,hEc,hSE,hEk,?_⟩
    intro hEm
    apply hm
    rw [←hgen,Subgroup.map_sup]
    exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mpr hCm)
      (le_centralizer_iff.mpr hEm))
  · exact ⟨C,hCP,hCc,hSC,hCk,hCm⟩
end SymmetricThreeProductResidual
