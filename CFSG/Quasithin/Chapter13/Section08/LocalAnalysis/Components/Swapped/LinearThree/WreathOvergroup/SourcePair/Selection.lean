module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Input
public import Theory.GroupTheory.DisjointCommutingProduct.SolvableProjections
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Identification

/-!
# Selecting the compatible pair of binary parabolics

Project the actual solvable subgroup (L₁T)* intersected with K₀* into the
commuting component images K* and (Kᵗ)*. The projections contain Sylow
two-subgroups, and the specified mover interchanges them. Neither projection
is a two-group, since otherwise their product, and hence L₁*, would be a
two-group. Solvability and component nonsolvability make both projections
proper. The PSL₃(2) parabolic classification and the concrete S₄ equivalence
therefore identify the literal projected subgroups with S₄.

Conjugation covariance of these projections supplies compatibility with every
element of T*. No invariant choice of a point or line stabilizer is assumed.
The resulting `ParabolicPair` retains containment in the respective component
images and both swap equations for the specified source mover. Its existing
lift gives a solvable overgroup of L₁T inside H.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16(1), printed p.952 (PDF p.969), using the earlier outputs recorded
in `SourcePair.Input`. The wreath quotient is a separate construction.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair

private theorem parabolic_equiv_s4 {A : Type*} [Group A] [Finite A]
    (e₀ : A ≃* Matrix.PSL3Two.PSL) (S : Sylow 2 A) (P : Subgroup A)
    (hSP : (S : Subgroup A) ≤ P) (hP : P ≠ ⊤) (h₂ : ¬ IsPGroup 2 P) :
    Nonempty (P ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨e, _, he⟩ := Matrix.PSL3Two.exists_sylow_line_marking e₀ S P hSP hP h₂
  exact ⟨(e.subgroupMap P).trans ((MulEquiv.subgroupCongr he).trans
    ((Matrix.PSL3Two.lineParabolicSL.equivMapOfInjective Matrix.PSL3Two.project
      Matrix.PSL3Two.project_injective).trans Matrix.PSL3Two.lineParabolicEquivS4))⟩

namespace Input
variable {G : Type*} [Group G] [Finite G]
variable {H L₁ T K K₀ : Subgroup G} (d : Input H L₁ T K K₀)

/-- The actual projections construct the pair, including the embeddings and
both conjugation equations for the specified source mover. -/
theorem exists_parabolicPair : ∃ p : ParabolicPair H L₁ T,
    p.left ≤ Source.starImage H K ∧
    p.right ≤ Source.starImage H (K.conjBy d.mover) ∧
    let t := QuotientGroup.mk' (pCore 2 H) ⟨d.mover, d.T_le d.mover_mem⟩
    p.left.map (MulAut.conj t).toMonoidHom = p.right ∧
      p.right.map (MulAut.conj t).toMonoidHom = p.left := by
  let A := Source.starImage H K
  let B := Source.starImage H (K.conjBy d.mover)
  let U := Source.starImage H L₁
  let t := QuotientGroup.mk' (pCore 2 H) ⟨d.mover, d.T_le d.mover_mem⟩
  have ht : t ∈ Source.starImage H T := mem_map_of_mem _ d.mover_mem
  have hAB : A ≠ B := by
    intro h
    have hd : Disjoint A B := d.star_factor_disjoint
    rw [← h] at hd
    have hbot : A = ⊥ := disjoint_self.mp hd
    exact (starImage_isCComponent H K d.component).ne_bot hbot
  have hAt : A.map (MulAut.conj t).toMonoidHom = B :=
    LinearTwo.starImage_conjBy H K d.component_le (d.T_le d.mover_mem)
  have hBt : B.map (MulAut.conj t).toMonoidHom = A := by
    rcases d.star_factor_permutation t ht with h | h
    · exact (hAB (h.1.symm.trans hAt)).elim
    · exact h.2
  have hc : A ≤ centralizer (B : Set (Source.Hstar H)) := by
    intro x hx y hy
    exact (d.star_factor_commute x hx y hy).eq.symm
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    A B d.star_factor_disjoint hc
  obtain ⟨S, hS⟩ := d.star_sylow_marking
  have hsol : Group.IsSolvable (U ⊔ (S : Subgroup (Source.Hstar H)) : Subgroup _) := by
    rw [hS]
    exact d.star_base_solvable
  have hperm : ∀ s ∈ (S : Subgroup (Source.Hstar H)),
      (A.map (MulAut.conj s).toMonoidHom = A ∧
        B.map (MulAut.conj s).toMonoidHom = B) ∨
      (A.map (MulAut.conj s).toMonoidHom = B ∧
        B.map (MulAut.conj s).toMonoidHom = A) := by
    rw [hS]
    exact d.star_factor_permutation
  have htS : t ∈ (S : Subgroup (Source.Hstar H)) := hS ▸ ht
  obtain ⟨hPsol, hQsol, hPtwo, hQtwo, ⟨SA, SB, hSA, hSB⟩,
      hU, hPQperm, hPt, hQt⟩ :=
    solvable_projections_of_swapped_factors A B hc
      d.star_factors_subnormal.1 d.star_factors_subnormal.2 S U
      d.star_seed_le d.star_seed_not_two hsol e he hperm t htS hAt hBt
  let P := MultiplicationProjections.left e (U ⊔ (S : Subgroup (Source.Hstar H)))
  let Q := MultiplicationProjections.right e (U ⊔ (S : Subgroup (Source.Hstar H)))
  have hP : P ≠ ⊤ := by
    intro h
    have : Group.IsSolvable (⊤ : Subgroup A) := h ▸ hPsol
    exact (starImage_isCComponent H K d.component).not_isSolvable
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
        topEquiv.surjective)
  have hQ : Q ≠ ⊤ := by
    intro h
    have : Group.IsSolvable (⊤ : Subgroup B) := h ▸ hQsol
    exact (starImage_isCComponent H (K.conjBy d.mover) d.second_component.2).not_isSolvable
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom)
        topEquiv.surjective)
  obtain ⟨eP⟩ := parabolic_equiv_s4 d.model SA P hSA hP hPtwo
  obtain ⟨eQ⟩ := parabolic_equiv_s4 d.second_model SB Q hSB hQ hQtwo
  let P₀ := P.map A.subtype
  let Q₀ := Q.map B.subtype
  have hPA : P₀ ≤ A := map_subtype_le P
  have hQB : Q₀ ≤ B := map_subtype_le Q
  let p : ParabolicPair H L₁ T := {
    base_le := d.base_le
    two := d.two
    left := P₀
    right := Q₀
    leftEquiv := (P.equivMapOfInjective A.subtype A.subtype_injective).symm.trans eP
    rightEquiv := (Q.equivMapOfInjective B.subtype B.subtype_injective).symm.trans eQ
    disjoint := d.star_factor_disjoint.mono hPA hQB
    commute := fun x hx y hy => d.star_factor_commute x (hPA hx) y (hQB hy)
    seed_le := hU
    permutes := by
      intro s hs
      rcases hPQperm s (hS ▸ hs) with h | h
      · exact Or.inl h.2.2
      · exact Or.inr h.2.2
    moves := ⟨t, ht, hPt⟩ }
  exact ⟨p, hPA, hQB, hPt, hQt⟩

/-- The compatible pair selected from the actual solvable projections. -/
noncomputable def parabolicPair : ParabolicPair H L₁ T :=
  Classical.choose d.exists_parabolicPair

/-- The left parabolic lies in the original component image. -/
theorem parabolicPair_left_le : d.parabolicPair.left ≤ Source.starImage H K :=
  (Classical.choose_spec d.exists_parabolicPair).1

/-- The right parabolic lies in the component moved by the source element. -/
theorem parabolicPair_right_le :
    d.parabolicPair.right ≤ Source.starImage H (K.conjBy d.mover) :=
  (Classical.choose_spec d.exists_parabolicPair).2.1

/-- The specified source mover exchanges both actual parabolics. -/
theorem parabolicPair_swapped :
    let t := QuotientGroup.mk' (pCore 2 H) ⟨d.mover, d.T_le d.mover_mem⟩
    d.parabolicPair.left.map (MulAut.conj t).toMonoidHom = d.parabolicPair.right ∧
      d.parabolicPair.right.map (MulAut.conj t).toMonoidHom = d.parabolicPair.left :=
  (Classical.choose_spec d.exists_parabolicPair).2.2

/-- The selected pair feeds the literal lift through H → H/O₂(H), yielding
the solvable overgroup used in the PSL₃(2) branch of 13.8.16(1). -/
theorem parabolicPair_overgroup_spec :
    L₁ ⊔ T ≤ d.parabolicPair.overgroup ∧ d.parabolicPair.overgroup ≤ H ∧
      Group.IsSolvable d.parabolicPair.overgroup :=
  ⟨d.parabolicPair.base_le_overgroup, d.parabolicPair.overgroup_le,
    d.parabolicPair.overgroup_solvable⟩

end Input
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair

end
