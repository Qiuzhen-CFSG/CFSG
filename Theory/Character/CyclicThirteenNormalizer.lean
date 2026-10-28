module
public import Theory.Character.CyclicThirteenOrbits
public import Theory.GroupTheory.CyclicThirteenNormalizer
public import Theory.Character.Transport

/-!
# The four cubic characters of an order-thirteen normalizer

Split the actual normalizer as P semidirect C3. Its faithful complement acts
freely on the twelve nonprincipal linear characters of P. Inducing one character
from each of the four orbits gives four distinct actual irreducibles of degree
three. Their restrictions are the orbit sums, and they vanish outside P.
The transport proof identifies this construction with ordinary induction from
the actual subgroup of N_G(P), rather than only the abstract semidirect factor.

Source: the local exceptional-character construction in
Alperin--Brauer--Gorenstein, III.8, printed pp.116--117.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace CyclicThirteenNormalizer
variable {G : Type*} [Group G] [Finite G] (P : Subgroup G)

/-- The actual subgroup of the normalizer from which we induce. -/
abbrev core := P.subgroupOf (Normalizer P)
/-- The canonical identification of the inducing subgroup with P. -/
abbrev coreEquiv : core P ≃* P := Subgroup.subgroupOfEquivOfLe P.le_normalizer

variable (α : Three →* MulAut P) (e : P ⋊[α] Three ≃* Normalizer P)
    (he : ∀ p : P, e (SemidirectProduct.inl p) = inclusion P p)

local instance finiteProduct : Finite (P ⋊[α] Three) :=
  Finite.of_equiv (P × Three) SemidirectProduct.equivProd.symm

/-- Transport the induced character along the splitting of the actual normalizer. -/
def row (ψ : P →* ℂ) : ConjClassFunction (Normalizer P) :=
  toConjClassFunction
    (fun x => ofConjClassFunction (SemidirectLinearInduction.induced α ψ)
      (e.symm.toMonoidHom x))
    (isClassFunction_comp_hom e.symm.toMonoidHom
      (ofConjClassFunction_isClassFunction _))

@[simp] theorem row_apply (ψ : P →* ℂ) (x : Normalizer P) :
    row P α e ψ (ConjClasses.mk x) =
      if (e.symm x).right = 1 then ∑ a : Three, ψ (α a (e.symm x).left) else 0 :=
  SemidirectLinearInduction.induced_apply α ψ _

theorem row_irreducible (hP : Nat.card P = 13) (hα : Function.Injective α)
    (ψ : P →* ℂ) (hψ : ψ ≠ 1) : IsIrreducibleConjCharacter (row P α e ψ) := by
  have hi := SemidirectLinearInduction.induced_irreducible α ψ
    (CyclicThirteenOrbits.orbit_injective hP α hα ψ hψ)
  constructor
  · obtain ⟨n, ρ, hρ⟩ := hi.1
    refine ⟨n, ρ.comp e.symm.toMonoidHom, ?_⟩
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    change SemidirectLinearInduction.induced α ψ (ConjClasses.mk (e.symm x)) = _
    rw [hρ]
    rfl
  · unfold row
    rw [classFunctionInner_toConjClassFunction]
    convert (scalarProduct_comp_mulEquiv e.symm
      (ofConjClassFunction (SemidirectLinearInduction.induced α ψ))
      (ofConjClassFunction (SemidirectLinearInduction.induced α ψ))).trans
      ((scalarProduct_ofConjClassFunction _ _).trans hi.2) using 1
    congr 1
    exact Subsingleton.elim _ _

theorem row_degree (ψ : P →* ℂ) : row P α e ψ (ConjClasses.mk 1) = 3 := by
  simp [row_apply, Three]

include he in
theorem row_restriction (ψ : P →* ℂ) (p : P) :
    row P α e ψ (ConjClasses.mk (inclusion P p)) = ∑ a : Three, ψ (α a p) := by
  rw [← he p]
  simp [row_apply]

omit [Finite G] in
include he in
private theorem split_mem_core (x : P ⋊[α] Three) : e x ∈ core P ↔ x.right = 1 := by
  constructor
  · intro hx
    let p : P := ⟨(e x : G), hx⟩
    have heq : e x = e (SemidirectProduct.inl p) := by
      rw [he]
      rfl
    have hh := congrArg SemidirectProduct.right (e.injective heq)
    exact hh
  · intro hx
    have heq : x = SemidirectProduct.inl x.left := by ext <;> simp [hx]
    rw [heq, he]
    exact x.left.property

omit [Finite G] in
include he in
private theorem split_core_value (x : P ⋊[α] Three) (hx : e x ∈ core P) :
    coreEquiv P ⟨e x, hx⟩ = x.left := by
  have hr := (split_mem_core P α e he x).mp hx
  have heq : x = SemidirectProduct.inl x.left := by ext <;> simp [hr]
  apply Subtype.ext
  change (e x : G) = (x.left : G)
  conv_lhs => rw [heq, he]
  rfl

include he in
/-- The transported construction is induction from the actual P inside N_G(P). -/
theorem row_induction (ψ : P →* ℂ) (n : Normalizer P) :
    row P α e ψ (ConjClasses.mk n) =
      inducedClassFunction (core P) (ψ.comp (coreEquiv P).toMonoidHom) n := by
  change SemidirectLinearInduction.induced α ψ (ConjClasses.mk (e.symm n)) = _
  rw [SemidirectLinearInduction.induced_eq_induction]
  unfold inducedClassFunction
  rw [Nat.card_congr (SemidirectLinearInduction.kernelEquiv α).symm.toEquiv,
    Nat.card_congr (coreEquiv P).toEquiv]
  congr 1
  rw [← e.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  have hh : e (x⁻¹ * e.symm n * x) = (e x)⁻¹ * n * e x := by simp
  have hm : (e x)⁻¹ * n * e x ∈ core P ↔
      x⁻¹ * e.symm n * x ∈ SemidirectLinearInduction.kernel α := by
    rw [← hh, split_mem_core P α e he, SemidirectLinearInduction.mem_kernel]
  by_cases hx : x⁻¹ * e.symm n * x ∈ SemidirectLinearInduction.kernel α
  · rw [dif_pos hx, dif_pos (hm.mpr hx), SemidirectLinearInduction.kernelCharacter_apply]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    symm
    convert split_core_value P α e he (x⁻¹ * e.symm n * x)
      (by rw [hh]; exact hm.mpr hx) using 1
    exact congrArg (coreEquiv P) (Subtype.ext hh.symm)
  · rw [dif_neg hx, dif_neg (mt hm.mp hx)]

include he in
/-- Every constructed row vanishes outside the actual order-thirteen subgroup. -/
theorem row_vanish (ψ : P →* ℂ) (n : Normalizer P) (hn : n ∉ core P) :
    row P α e ψ (ConjClasses.mk n) = 0 := by
  rw [row_apply, if_neg]
  intro hh
  apply hn
  have hm := (split_mem_core P α e he (e.symm n)).mpr hh
  simpa using hm

/-- Orbit representatives yield distinct transported induced characters. -/
theorem rows_injective (hP : Nat.card P = 13) (hα : Function.Injective α)
    (ψ : Fin 4 → P →* ℂ) (hψ : ∀ i, ψ i ≠ 1)
    (hinj : Function.Injective (fun p : Fin 4 × Three =>
      (ψ p.1).comp (α p.2).toMonoidHom)) :
    Function.Injective (fun i => row P α e (ψ i)) := by
  intro i j hij
  have hi : SemidirectLinearInduction.induced α (ψ i) =
      SemidirectLinearInduction.induced α (ψ j) := by
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
    have hv := congrFun hij (ConjClasses.mk (e x))
    change SemidirectLinearInduction.induced α (ψ i) (ConjClasses.mk (e.symm (e x))) =
      SemidirectLinearInduction.induced α (ψ j) (ConjClasses.mk (e.symm (e x))) at hv
    simpa using hv
  obtain ⟨a, ha⟩ := SemidirectLinearInduction.orbit_of_induced_eq α (ψ i) (ψ j)
    (CyclicThirteenOrbits.orbit_injective hP α hα (ψ i) (hψ i)) hi
  have hab : (ψ i).comp (α a).toMonoidHom = (ψ j).comp (α 1).toMonoidHom := by
    ext p
    simpa using DFunLike.congr_fun ha p
  exact congrArg Prod.fst (hinj (show
    (fun p : Fin 4 × Three => (ψ p.1).comp (α p.2).toMonoidHom) (i,a) =
    (fun p : Fin 4 × Three => (ψ p.1).comp (α p.2).toMonoidHom) (j,1) from hab))

/-- Four distinct cubic rows, with the actual inducing characters and full
restriction and induction formulas. The orbit coordinates exhaust all twelve
nonprincipal linear characters of P. -/
structure Rows where
  action : Three →* MulAut P
  splitting : P ⋊[action] Three ≃* Normalizer P
  action_injective : Function.Injective action
  splitting_inl : ∀ p : P, splitting (SemidirectProduct.inl p) = inclusion P p
  linear : Fin 4 → P →* ℂ
  linear_ne_one : ∀ i, linear i ≠ 1
  orbit_injective : Function.Injective (fun q : Fin 4 × Three =>
    (linear q.1).comp (action q.2).toMonoidHom)
  orbit_covers : ∀ ψ : P →* ℂ, ψ ≠ 1 → ∃ (i : Fin 4) (a : Three),
    (linear i).comp (action a).toMonoidHom = ψ
  chi : Fin 4 → ConjClassFunction (Normalizer P)
  irreducible : ∀ i, IsIrreducibleConjCharacter (chi i)
  distinct : Function.Injective chi
  degree : ∀ i, chi i (ConjClasses.mk 1) = 3
  induction : ∀ (i : Fin 4) (n : Normalizer P), chi i (ConjClasses.mk n) =
    inducedClassFunction (core P) ((linear i).comp (coreEquiv P).toMonoidHom) n
  restriction : ∀ (i : Fin 4) (p : P), chi i (ConjClasses.mk (inclusion P p)) =
    ∑ a : Three, linear i (action a p)
  value : ∀ (i : Fin 4) (n : Normalizer P), chi i (ConjClasses.mk n) =
    if (splitting.symm n).right = 1 then
      ∑ a : Three, linear i (action a (splitting.symm n).left) else 0
  vanish : ∀ (i : Fin 4) (n : Normalizer P), n ∉ core P → chi i (ConjClasses.mk n) = 0

/-- Construct the four irreducible cubic characters from the original local
hypotheses alone. Sylow maximality is not needed for this local construction. -/
theorem nonempty_rows (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (hindex : P.relIndex (Normalizer P) = 3) : Nonempty (Rows P) := by
  obtain ⟨α, e, hα, he⟩ := exists_semidirect P hP hC hindex
  obtain ⟨ψ, hψ, hinj, hcover⟩ := CyclicThirteenOrbits.exists_four_orbits hP
    (by simp [Three, Nat.card_eq_fintype_card] : Nat.card Three = 3) α hα
  exact ⟨{
    action := α
    splitting := e
    action_injective := hα
    splitting_inl := he
    linear := ψ
    linear_ne_one := hψ
    orbit_injective := hinj
    orbit_covers := hcover
    chi := fun i => row P α e (ψ i)
    irreducible := fun i => row_irreducible P α e hP hα (ψ i) (hψ i)
    distinct := rows_injective P α e hP hα ψ hψ hinj
    degree := fun i => row_degree P α e (ψ i)
    induction := fun i => row_induction P α e he (ψ i)
    restriction := fun i => row_restriction P α e he (ψ i)
    value := fun i => row_apply P α e (ψ i)
    vanish := fun i => row_vanish P α e he (ψ i) }⟩

end CyclicThirteenNormalizer
