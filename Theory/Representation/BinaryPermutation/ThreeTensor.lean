module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Quadratic actors on an external tensor product with the natural S₃-module

The second tensor factor is the actual augmentation core on three points.
A coordinate separating a vector from its image detects both the kernel of
projection to S₃ and a full copy of the first factor in the displacement space.
For a quadratic actor with nontrivial S₃ projection, fixed codimension equals
the dimension of the first factor. Faithfulness makes that projection injective,
so an elementary actor has rank one. Restriction to the first direct factor is
identified equivariantly with two copies of its original representation.

Source: the tensor calculation used in Aschbacher–Smith 13.8.21(1), printed
p.957, combined manuscript of 1 March 2004. The first representation is arbitrary;
its classification and any single-factor offender bound are separate inputs.
-/

public section

open TensorProduct Representation Representation.BinaryOffender
namespace BinaryPermutation.ThreeTensor

private theorem separating_coordinate (t : Equiv.Perm (Fin 3)) (ht : t ≠ 1) :
    ∃ n : core (Fin 3), ∃ i : Fin 3,
      n.val i = 0 ∧ (coreRepresentation (Fin 3) t n).val i = 1 := by
  let : DecidablePred (· ∈ core (Fin 3)) := fun v =>
    inferInstanceAs (Decidable ((∑ i, v i) = (0 : ZMod 2)))
  let : Fintype (core (Fin 3)) := Subtype.fintype _
  revert t
  decide

private def evaluation (i : Fin 3) : core (Fin 3) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj i).comp (core (Fin 3)).subtype

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The genuine external tensor action of G × S₃. -/
@[expose] noncomputable def action (ρ : Representation (ZMod 2) G V) :
    Representation (ZMod 2) (G × Equiv.Perm (Fin 3)) (V ⊗[ZMod 2] core (Fin 3)) :=
  Representation.tprod (ρ.comp (MonoidHom.fst _ _))
    ((coreRepresentation (Fin 3)).comp (MonoidHom.snd _ _))

@[simp] theorem action_tmul (ρ : Representation (ZMod 2) G V)
    (g : G × Equiv.Perm (Fin 3)) (v : V) (n : core (Fin 3)) :
    action ρ g (v ⊗ₜ[ZMod 2] n) = ρ g.1 v ⊗ₜ[ZMod 2] coreRepresentation (Fin 3) g.2 n := rfl

private noncomputable def contract (i : Fin 3) :
    (V ⊗[ZMod 2] core (Fin 3)) →ₗ[ZMod 2] V :=
  (TensorProduct.rid (ZMod 2) V).toLinearMap.comp
    (TensorProduct.map LinearMap.id (evaluation i))

private theorem contract_tmul (i : Fin 3) (v : V) (n : core (Fin 3)) :
    contract i (v ⊗ₜ[ZMod 2] n) = n.val i • v := rfl

variable (ρ : Representation (ZMod 2) G V)

/-- Quadraticity kills the kernel of projection when the first action is faithful. -/
theorem kernel_trivial_of_quadratic (hfaith : Function.Injective ρ)
    (A : Subgroup (G × Equiv.Perm (Fin 3))) (hq : IsQuadratic (action ρ) A)
    (a : G × Equiv.Perm (Fin 3)) (ha : a ∈ A) (hat : a.2 ≠ 1)
    (b : G) (hb : (b, 1) ∈ A) : b = 1 := by
  obtain ⟨n, i, hn, htn⟩ := separating_coordinate a.2 hat
  have hfix (v : V) : ρ b v = v := by
    have he := congrArg (contract (V := V) i) (hq a ha (b, 1) hb (v ⊗ₜ[ZMod 2] n))
    simp only [map_sub, action_tmul, map_one, Module.End.one_apply,
      contract_tmul, hn, htn, zero_smul, one_smul, sub_self] at he
    have hh := congrArg (ρ a.1⁻¹) he
    simpa only [map_sub, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, inv_mul_cancel_left, map_one, Module.End.one_apply, map_zero, sub_eq_zero] using hh
  apply hfaith
  ext v
  simpa using hfix v

/-- The projection of a quadratic actor to S₃ is injective if it is nontrivial. -/
theorem projection_injective (hfaith : Function.Injective ρ)
    (A : Subgroup (G × Equiv.Perm (Fin 3))) (hq : IsQuadratic (action ρ) A)
    (ha : ∃ a ∈ A, a.2 ≠ 1) :
    Function.Injective ((MonoidHom.snd G (Equiv.Perm (Fin 3))).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro b hb
  obtain ⟨a, ha, hat⟩ := ha
  have hbt : b.val.2 = 1 := hb
  have hbf : b.val.1 = 1 := kernel_trivial_of_quadratic ρ hfaith A hq a ha hat b.val.1
    (by simpa only [← hbt, Prod.mk.eta] using b.property)
  exact Subgroup.mem_bot.mpr (Subtype.ext (Prod.ext hbf hbt))

/-- One element moving the S₃ factor forces this lower displacement bound. -/
theorem dimension_le_fixedCodim [FiniteDimensional (ZMod 2) V]
    (A : Subgroup (G × Equiv.Perm (Fin 3)))
    (a : G × Equiv.Perm (Fin 3)) (ha : a ∈ A) (hat : a.2 ≠ 1) :
    Module.finrank (ZMod 2) V ≤ fixedCodim (action ρ) A := by
  obtain ⟨n, i, hn, htn⟩ := separating_coordinate a.2 hat
  let f : V →ₗ[ZMod 2] (V ⊗[ZMod 2] core (Fin 3)) ⧸ fixedSpace (action ρ) A :=
    (fixedSpace (action ρ) A).mkQ.comp ((TensorProduct.mk (ZMod 2) V (core (Fin 3))).flip n)
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hmem : v ⊗ₜ[ZMod 2] n ∈ fixedSpace (action ρ) A :=
      (Submodule.Quotient.mk_eq_zero _).mp hv
    have hhfix : action ρ a (v ⊗ₜ[ZMod 2] n) = v ⊗ₜ[ZMod 2] n := hmem ⟨a, ha⟩
    have he := congrArg (contract (V := V) i) hhfix
    simp only [action_tmul, contract_tmul, hn, htn, zero_smul, one_smul] at he
    have hh := congrArg (ρ a.1⁻¹) he
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] using hh
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- Quadraticity makes the preceding displacement bound an equality. -/
theorem fixedCodim_eq_dimension [FiniteDimensional (ZMod 2) V]
    (A : Subgroup (G × Equiv.Perm (Fin 3))) (hq : IsQuadratic (action ρ) A)
    (a : G × Equiv.Perm (Fin 3)) (ha : a ∈ A) (hat : a.2 ≠ 1) :
    fixedCodim (action ρ) A = Module.finrank (ZMod 2) V := by
  obtain ⟨n, i, hn, htn⟩ := separating_coordinate a.2 hat
  let f : V →ₗ[ZMod 2] V ⊗[ZMod 2] core (Fin 3) :=
    (action ρ a - 1).comp ((TensorProduct.mk (ZMod 2) V (core (Fin 3))).flip n)
  have hmem (v : V) : f v ∈ fixedSpace (action ρ) A := by
    intro b
    exact hq b.val b.property a ha (v ⊗ₜ[ZMod 2] n)
  let ff := f.codRestrict (fixedSpace (action ρ) A) hmem
  have hinj : Function.Injective ff := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have he := congrArg (fun z : fixedSpace (action ρ) A => contract (V := V) i z.val) hv
    change contract i (action ρ a (v ⊗ₜ[ZMod 2] n) - v ⊗ₜ[ZMod 2] n) = contract i 0 at he
    simp only [map_sub, action_tmul, contract_tmul, hn, htn,
      zero_smul, one_smul, sub_zero, map_zero] at he
    have hh := congrArg (ρ a.1⁻¹) he
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] using hh
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdim := fixedCodim_add_finrank (action ρ) A
  rw [Module.finrank_tensorProduct, finrank_core] at hdim
  have hlo := dimension_le_fixedCodim ρ A a ha hat
  simp only [Fintype.card_fin] at hdim
  omega

/-- An elementary quadratic actor with nontrivial S₃ projection has rank one. -/
theorem rank_eq_one [Finite G] (hfaith : Function.Injective ρ)
    (A : Subgroup (G × Equiv.Perm (Fin 3))) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (action ρ) A) (ha : ∃ a ∈ A, a.2 ≠ 1) : rank A = 1 := by
  let f := (MonoidHom.snd G (Equiv.Perm (Fin 3))).comp A.subtype
  have hf := projection_injective ρ hfaith A hq ha
  have hc : Nat.card A ∣ 6 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    convert Subgroup.card_subgroup_dvd_card f.range using 1
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hA.card_eq_two_pow_rank] at hc
  have hle : rank A ≤ 1 := by
    by_contra! hlarge
    have hd : 4 ∣ 6 := dvd_trans (pow_dvd_pow 2 (show 2 ≤ rank A by omega)) hc
    norm_num at hd
  have hp := hA.rank_pos
  omega

/-- A first factor of dimension greater than two excludes a ratio at most two. -/
theorem outer_bound [Finite G] [FiniteDimensional (ZMod 2) V]
    (hfaith : Function.Injective ρ) (hdim : 2 < Module.finrank (ZMod 2) V)
    (A : Subgroup (G × Equiv.Perm (Fin 3))) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (action ρ) A) (ha : ∃ a ∈ A, a.2 ≠ 1) :
    2 * rank A < fixedCodim (action ρ) A := by
  rw [rank_eq_one ρ hfaith A hA hq ha]
  obtain ⟨a, ha, hat⟩ := ha
  have hd := dimension_le_fixedCodim ρ A a ha hat
  omega

private def corePair : core (Fin 3) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) where
  toFun n := (n.val 0, n.val 1)
  invFun p := ⟨![p.1,p.2,-p.1-p.2], by
    rw [mem_core, Fin.sum_univ_three]
    change p.1 + p.2 + (-p.1 - p.2) = 0
    ring⟩
  left_inv n := by
    apply Subtype.ext
    have hn := n.property
    rw [mem_core, Fin.sum_univ_three] at hn
    ext i
    fin_cases i
    · rfl
    · rfl
    · change -n.val 0 - n.val 1 = n.val 2
      linear_combination -hn
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Tensor coordinates identify the vector space with two copies of V. -/
noncomputable def pairEquiv : (V ⊗[ZMod 2] core (Fin 3)) ≃ₗ[ZMod 2] (V × V) :=
  (TensorProduct.congr (LinearEquiv.refl (ZMod 2) V) corePair).trans
    ((TensorProduct.prodRight (ZMod 2) (ZMod 2) V (ZMod 2) (ZMod 2)).trans
      ((TensorProduct.rid (ZMod 2) V).prodCongr (TensorProduct.rid (ZMod 2) V)))

@[simp] theorem pairEquiv_tmul (v : V) (n : core (Fin 3)) :
    pairEquiv (v ⊗ₜ[ZMod 2] n) = (n.val 0 • v, n.val 1 • v) := by rfl

/-- The coordinate identification intertwines the component action. -/
theorem pairEquiv_equivariant (g : G) (v : V ⊗[ZMod 2] core (Fin 3)) :
    pairEquiv (action ρ (g, 1) v) = (ρ.prod ρ) g (pairEquiv v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v n => simp [Representation.prod]
  | add u v hu hv => simpa only [map_add] using congrArg₂ (· + ·) hu hv

/-- On actors in the first factor, a strict single-factor bound doubles. -/
theorem component_bound [FiniteDimensional (ZMod 2) V]
    (hρ : ∀ B, IsElementaryTwo B → IsQuadratic ρ B → rank B < fixedCodim ρ B)
    (A : Subgroup (G × Equiv.Perm (Fin 3))) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (action ρ) A) (hinside : ∀ a ∈ A, a.2 = 1) :
    2 * rank A < fixedCodim (action ρ) A := by
  let B := A.map (MonoidHom.fst G (Equiv.Perm (Fin 3)))
  let ι : G →* G × Equiv.Perm (Fin 3) := MonoidHom.inl _ _
  have hmap : B.map ι = A := by
    ext a
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      change (c.1, 1) ∈ A
      have he : (c.1, 1) = c := Prod.ext rfl (hinside c hc).symm
      rw [he]
      exact hc
    · intro ha
      exact ⟨a.1, ⟨a, ha, rfl⟩, Prod.ext rfl (hinside a ha).symm⟩
  have hi : Function.Injective ι := fun _ _ he => congrArg Prod.fst he
  have hB : IsElementaryTwo B := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hb
    apply hA.1
    rw [← hmap, hb, Subgroup.map_bot]
  have hrank : rank B = rank A := by rw [← hmap, rank_map_injective ι hi]
  have hqB : IsQuadratic ((action ρ).comp ι) B := by
    intro a ha b hb v
    exact hq (ι a) (hmap ▸ Subgroup.mem_map_of_mem ι ha)
      (ι b) (hmap ▸ Subgroup.mem_map_of_mem ι hb) v
  have he (g : G) (v : V ⊗[ZMod 2] core (Fin 3)) :
      pairEquiv (((action ρ).comp ι) g v) = (ρ.prod ρ) g (pairEquiv v) :=
    pairEquiv_equivariant ρ g v
  have hqp := quadratic_of_equivariant_surjection ((action ρ).comp ι) (ρ.prod ρ)
    pairEquiv.toLinearMap pairEquiv.surjective he B hqB
  have hcod := fixedCodim_map_equivariant ((action ρ).comp ι) (ρ.prod ρ)
    (MonoidHom.id G) pairEquiv he B
  simp only [Subgroup.map_id] at hcod
  have hcodA : fixedCodim ((action ρ).comp ι) B = fixedCodim (action ρ) A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, hmap]
  rw [hcodA, fixedCodim_prod] at hcod
  have hlt := hρ B hB ((quadratic_prod_iff ρ ρ B).mp hqp).1
  omega

end BinaryPermutation.ThreeTensor

namespace BinaryPermutation.ThreeTensor
variable {G V H U : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H U)

/-- Transport the actor, quadratic identity, rank and codimension through actual
group and representation equivalences. -/
theorem transport_quadratic (eH : H ≃* G × Equiv.Perm (Fin 3))
    (eV : σ.Equiv ((action ρ).comp eH.toMonoidHom))
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A) :
    IsElementaryTwo (A.map eH.toMonoidHom) ∧
      IsQuadratic (action ρ) (A.map eH.toMonoidHom) ∧
      rank (A.map eH.toMonoidHom) = rank A ∧
      fixedCodim σ A = fixedCodim (action ρ) (A.map eH.toMonoidHom) := by
  have he (g : H) (u : U) : eV (σ g u) = action ρ (eH g) (eV u) :=
    LinearMap.congr_fun (eV.isIntertwining' g) u
  have hele : IsElementaryTwo (A.map eH.toMonoidHom) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hb
    apply hA.1
    apply Subgroup.map_injective (f := eH.toMonoidHom) eH.injective
    simpa using hb
  refine ⟨hele, ?_, rank_map_injective eH.toMonoidHom eH.injective A,
    fixedCodim_map_equivariant σ (action ρ) eH.toMonoidHom eV.toLinearEquiv he A⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨u, rfl⟩ := eV.surjective v
  change action ρ (eH a) (action ρ (eH b) (eV u) - eV u) =
    action ρ (eH b) (eV u) - eV u
  have hh := congrArg eV (hq a ha b hb u)
  simpa only [map_sub, he, MulEquiv.coe_toMonoidHom] using hh

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- The rank and displacement calculation in an arbitrary equivariant model. -/
theorem rank_codim_of_equiv (hfaith : Function.Injective ρ)
    (eH : H ≃* G × Equiv.Perm (Fin 3))
    (eV : σ.Equiv ((action ρ).comp eH.toMonoidHom))
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hout : ∃ a ∈ A, (eH a).2 ≠ 1) :
    rank A = 1 ∧ fixedCodim σ A = Module.finrank (ZMod 2) V := by
  obtain ⟨hele, hquad, hrank, hcod⟩ := transport_quadratic ρ σ eH eV A hA hq
  obtain ⟨a, ha, hat⟩ := hout
  have hm : eH a ∈ A.map eH.toMonoidHom := Subgroup.mem_map_of_mem _ ha
  exact ⟨hrank ▸ rank_eq_one ρ hfaith _ hele hquad ⟨eH a, hm, hat⟩,
    hcod.trans (fixedCodim_eq_dimension ρ _ hquad (eH a) hm hat)⟩


end BinaryPermutation.ThreeTensor
