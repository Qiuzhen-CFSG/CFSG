module

public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Restricting central two-extensions to their perfect residuals

A surjection onto a group with perfect derived subgroup restricts to a
perfect central cover of that derived subgroup. If its kernel has order two,
oddness of the restricted kernel makes the restriction an isomorphism.
The kernel and residual then form their genuine internal direct product.
When the derived subgroup downstairs has index two, this product has index
two upstairs and the residual is the entire commutator subgroup: the quotient
by the residual has order four and is abelian.

This is the residual-cover argument in Aschbacher--Smith 14.3.22, printed
p.999, with the correction recorded in `docs/quasithin-proof-basis.md`.
It makes no assertion that the entire extension splits.
-/

@[expose] public section

open Subgroup PerfectCentralCovering
namespace Subgroup
variable {E Q : Type*} [Group E] [Finite E] [Group Q]

/-- A perfect first derived subgroup is already the terminal derived subgroup. -/
theorem residual_eq_commutator_of_perfect_derived [Group.IsPerfect (_root_.commutator Q)] :
    solvableResidual Q = _root_.commutator Q := by
  exact le_antisymm (solvableResidual_le_derivedSeries 1)
    (le_solvableResidual_of_isPerfect _)

/-- Restriction of the original map, with codomain the actual derived subgroup. -/
def residualDerivedMap (f : E →* Q) : solvableResidual E →* _root_.commutator Q :=
  (f.comp (solvableResidual E).subtype).codRestrict _ (fun x =>
    (map_solvableResidual_le f).trans (solvableResidual_le_derivedSeries 1)
      (mem_map_of_mem f x.property))

/-- Surjectivity retains the actual restriction of the original map. -/
theorem residualDerivedMap_surjective (f : E →* Q) (hf : Function.Surjective f)
    [Group.IsPerfect (_root_.commutator Q)] : Function.Surjective (residualDerivedMap f) := by
  intro x
  have hx : x.val ∈ (solvableResidual E).map f := by
    rw [map_solvableResidual_eq f hf, residual_eq_commutator_of_perfect_derived]
    exact x.property
  obtain ⟨y, hy, he⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- The residual restriction is a perfect central cover. -/
def residualDerivedCover (f : E →* Q) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) [Group.IsPerfect (_root_.commutator Q)] :
    Cover (solvableResidual E) (_root_.commutator Q) where
  toMonoidHom := residualDerivedMap f
  surjective := residualDerivedMap_surjective f hf
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    have hxk : x.val ∈ f.ker := congrArg Subtype.val hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hc hxk) y.val))

/-- A restricted kernel of odd order cannot meet the original two-kernel. -/
theorem residualDerivedMap_bijective_of_two_kernel
    (f : E →* Q) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 2) [Group.IsPerfect (_root_.commutator Q)]
    (hodd : ¬ 2 ∣ Nat.card (residualDerivedMap f).ker) :
    Function.Bijective (residualDerivedMap f) := by
  refine ⟨?_, residualDerivedMap_surjective f hf⟩
  let i : (residualDerivedMap f).ker →* f.ker := {
    toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a : f.ker => (a : E)) h))
  have hd : Nat.card (residualDerivedMap f).ker ∣ 2 := by
    rw [← hk]
    exact card_dvd_of_injective i hi
  have hcard : Nat.card (residualDerivedMap f).ker = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · exact (hodd (h.symm ▸ dvd_refl 2)).elim
  exact (MonoidHom.ker_eq_bot_iff _).mp (Subgroup.card_eq_one.mp hcard)

omit [Finite E] in
/-- Injectivity of the residual restriction separates the two factors. -/
theorem residual_disjoint_kernel (f : E →* Q)
    (hi : Function.Injective (residualDerivedMap f)) :
    Disjoint f.ker (solvableResidual E) := by
  apply disjoint_def.mpr
  intro x hx hy
  have he : residualDerivedMap f ⟨x, hy⟩ = 1 := Subtype.ext hx
  have : (⟨x, hy⟩ : solvableResidual E) = 1 := hi (he.trans (map_one _).symm)
  exact congrArg Subtype.val this

/-- The full preimage of the derived subgroup is the kernel-residual join. -/
theorem residual_join_kernel_index (f : E →* Q) (hf : Function.Surjective f)
    [Group.IsPerfect (_root_.commutator Q)] (hd : (_root_.commutator Q).index = 2) :
    (f.ker ⊔ solvableResidual E).index = 2 := by
  have he : f.ker ⊔ solvableResidual E = (_root_.commutator Q).comap f := by
    rw [← residual_eq_commutator_of_perfect_derived,
      ← map_solvableResidual_eq f hf, comap_map_eq, sup_comm]
  rw [he, index_comap_of_surjective _ hf, hd]

omit [Finite E] in
/-- The remaining quotient has order four, so every commutator lies in the residual. -/
theorem commutator_eq_residual_of_two_kernel
    [Finite Q] (f : E →* Q) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 2) [Group.IsPerfect (_root_.commutator Q)]
    (hd : (_root_.commutator Q).index = 2)
    (hb : Function.Bijective (residualDerivedMap f)) :
    _root_.commutator E = solvableResidual E := by
  have hcard : Nat.card (solvableResidual E) = Nat.card (_root_.commutator Q) :=
    Nat.card_congr (MulEquiv.ofBijective _ hb).toEquiv
  have htotal : Nat.card E = 2 * Nat.card Q := by
    have h := f.ker.card_mul_index
    rw [hk, show f.ker.index = Nat.card Q from
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
    exact h.symm
  have hindex : (solvableResidual E).index = 2 ^ 2 := by
    have h := (solvableResidual E).card_mul_index
    have hQ := (_root_.commutator Q).card_mul_index
    rw [hcard, htotal] at h
    rw [hd] at hQ
    have hp : 0 < Nat.card (_root_.commutator Q) := Nat.card_pos
    nlinarith
  let : IsMulCommutative (E ⧸ solvableResidual E) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hindex
  exact le_antisymm (Normal.quotient_commutative_iff_commutator_le.mp inferInstance)
    (solvableResidual_le_derivedSeries 1)
omit [Finite E] in
/-- The product is internal: its isomorphism is multiplication in E. -/
theorem residual_kernel_internal_product (f : E →* Q)
    (hc : f.ker ≤ center E) (hi : Function.Injective (residualDerivedMap f)) :
    ∃ e : f.ker × solvableResidual E ≃* ↥(f.ker ⊔ solvableResidual E),
      ∀ k l, (e (k, l) : E) = (k : E) * (l : E) := by
  apply exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (residual_disjoint_kernel f hi)
  intro k hk l _
  exact mem_center_iff.mp (hc hk) l

end Subgroup
