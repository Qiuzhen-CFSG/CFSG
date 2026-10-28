module

public import Theory.Representation.BinaryParabolicNatural.Basic
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# Central covers of binary natural and dual modules

In dimension at least four, the checked elementary-matrix H¹ vanishing,
transported through inverse transpose, annihilates the fixed kernel of any
commutator-generated central cover of the natural or dual module. The original
covering map is therefore an equivariant linear equivalence. A trivial quotient
extension then splits off the global fixed space by the connecting cocycle map.
The final equalities transport the literal parabolic fixed-space commutator,
including all globally fixed summands, through the original covering map.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.5.1(1)(i), printed p.99, applied in C.4.8,
printed p.154; H¹ vanishing is I.1.6(6), printed p.408. Neither irreducibility
nor a prescribed fixed-space commutator is assumed upstairs.
-/

@[expose] public section
namespace Representation.BinaryParabolicNatural
open OneCohomology BinaryLinear.OuterCyclic

private theorem graphSL_inv_transpose (n : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    graphSL n g = Matrix.SpecialLinearGroup.transpose g⁻¹ := by
  change (Matrix.SpecialLinearGroup.transpose g)⁻¹ = Matrix.SpecialLinearGroup.transpose g⁻¹
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change g⁻¹.val.transpose * g.val.transpose = 1
  rw [← Matrix.transpose_mul]
  change (g * g⁻¹).val.transpose = 1
  rw [mul_inv_cancel]
  exact Matrix.transpose_one

/-- The natural H¹ vanishing also holds for the contragredient, by the actual
inverse-transpose automorphism and dot-product equivalence. -/
theorem dualSL_H1_zero {n : ℕ} (hn : 4 ≤ n) :
    Module.finrank (ZMod 2) (H1 (specialLinearNatural (k := ZMod 2) n).dual) = 0 := by
  let e := dotProductEquiv (ZMod 2) (Fin n)
  have he : ∀ g f, e.symm ((specialLinearNatural (k := ZMod 2) n).dual g f) =
      specialLinearNatural n (graphSL n g) (e.symm f) := by
    intro g f
    apply e.injective
    rw [e.apply_symm_apply]
    obtain ⟨v, rfl⟩ := e.surjective f
    rw [e.symm_apply_apply]
    apply LinearMap.ext
    intro w
    rw [graphSL_inv_transpose]
    change dotProduct v (g⁻¹.val.mulVec w) = dotProduct (g⁻¹.val.transpose.mulVec v) w
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  exact (H1Congr _ _ (graphSL n) e.symm he).finrank_eq.trans
    (OneCohomology.SLHigherNatural.finrank_H1_of_four_le hn)

/-- H¹ vanishes on the literal general-linear natural module in degrees at least four. -/
theorem natural_H1_zero {n : ℕ} (hn : 4 ≤ n) :
    Module.finrank (ZMod 2) (H1 (natural (Space n))) = 0 := by
  have h := H1Congr (specialLinearNatural (k := ZMod 2) n) (natural (Space n))
    (slEquivLinear n) (LinearEquiv.refl (ZMod 2) (Space n)) (fun _ _ => rfl)
  exact h.finrank_eq.symm.trans (OneCohomology.SLHigherNatural.finrank_H1_of_four_le hn)

/-- The same vanishing for the literal dual general-linear module. -/
theorem dual_H1_zero {n : ℕ} (hn : 4 ≤ n) :
    Module.finrank (ZMod 2) (H1 (natural (Space n)).dual) = 0 := by
  have he : ∀ g f,
      (specialLinearNatural (k := ZMod 2) n).dual g f =
        (natural (Space n)).dual (slEquivLinear n g) f := by
    intro g f
    apply LinearMap.ext
    intro v
    change f (g⁻¹.val.mulVec v) = f ((slEquivLinear n g)⁻¹ v)
    rw [← map_inv]
    rfl
  have h := H1Congr (specialLinearNatural (k := ZMod 2) n).dual (natural (Space n)).dual
    (slEquivLinear n) (LinearEquiv.refl (ZMod 2) (Module.Dual (ZMod 2) (Space n))) he
  exact h.finrank_eq.symm.trans (dualSL_H1_zero hn)

/-- Double duality preserves H¹ with the original actor. -/
theorem doubleDual_H1_finrank {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) :
    Module.finrank (ZMod 2) (H1 ρ.dual.dual) = Module.finrank (ZMod 2) (H1 ρ) := by
  have he : ∀ g f, (Module.evalEquiv (ZMod 2) V).symm (ρ.dual.dual g f) =
      ρ g ((Module.evalEquiv (ZMod 2) V).symm f) := by
    intro g f
    exact LinearMap.congr_fun ((evaluationIntertwining ρ).isIntertwining' g) f
  exact (H1Congr _ _ (MulEquiv.refl G) (Module.evalEquiv (ZMod 2) V).symm he).finrank_eq

/-- Vanishing dual H¹ rules out a nontrivial fixed kernel in any central cover.
The source is commutator generated; it is not assumed irreducible. -/
theorem cover_injective_of_H1_zero {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (hH : Module.finrank (ZMod 2) (H1 ρ.dual) = 0) : Function.Injective p := by
  have h := finrank_ker_le_H1_of_cover p hp
  rw [hH] at h
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h))

/-- B.5.1(i)'s natural central cover in degrees four and five has zero central kernel. -/
theorem natural_cover_injective {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (p : σ.IntertwiningMap (natural (Space n))) (hp : IsCover p) : Function.Injective p := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  exact cover_injective_of_H1_zero p hp (dual_H1_zero hn)

/-- The same conclusion for the dual natural central cover. -/
theorem dual_cover_injective {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (p : σ.IntertwiningMap (natural (Space n)).dual) (hp : IsCover p) : Function.Injective p := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  apply cover_injective_of_H1_zero p hp
  rw [doubleDual_H1_finrank, natural_H1_zero hn]


/-- An extension by a trivial quotient splits off the global fixed space when
its submodule is fixed-point-free and has vanishing H¹. -/
theorem isCompl_fixed_of_H1_zero {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) G W} (C : Subrepresentation σ)
    (hq : HasTrivialQuotient C) (hfixed : fixed C.toRepresentation = ⊥)
    [FiniteDimensional (ZMod 2) (H1 C.toRepresentation)]
    (hH : Module.finrank (ZMod 2) (H1 C.toRepresentation) = 0) :
    IsCompl C.toSubmodule (fixed σ) := by
  have : Subsingleton (H1 C.toRepresentation) :=
    (Module.finrank_eq_zero_iff_of_free (ZMod 2) _).mp hH
  constructor
  · apply Submodule.disjoint_def.mpr
    intro w hw hf
    have hc : (⟨w, hw⟩ : C.toSubmodule) ∈ fixed C.toRepresentation := by
      intro g
      exact Subtype.ext (hf g)
    rw [hfixed, Submodule.mem_bot] at hc
    exact congrArg Subtype.val hc
  · apply codisjoint_iff.mpr
    apply top_unique
    intro w _
    exact (extensionClass_eq_zero_iff C hq w).mp (Subsingleton.elim _ _)

/-- Central covers and trivial quotient extensions are treated together, with
the original subrepresentation retained. No irreducibility is assumed upstairs. -/
theorem isCompl_fixed_of_cover {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    (C : Subrepresentation σ) (hq : HasTrivialQuotient C)
    (p : C.toRepresentation.IntertwiningMap ρ) (hp : IsCover p)
    (hH : Module.finrank (ZMod 2) (H1 ρ) = 0)
    (hHd : Module.finrank (ZMod 2) (H1 ρ.dual) = 0)
    (hρ : fixed ρ = ⊥) : IsCompl C.toSubmodule (fixed σ) := by
  have hi := cover_injective_of_H1_zero p hp hHd
  let e := LinearEquiv.ofBijective p.toLinearMap ⟨hi, hp.1⟩
  have he : ∀ g v, e (C.toRepresentation g v) = ρ g (e v) :=
    fun g v => LinearMap.congr_fun (p.isIntertwining' g) v
  apply isCompl_fixed_of_H1_zero C hq
  · apply bot_unique
    intro v hv
    have hf : e v ∈ fixed ρ := by
      intro g
      rw [← he, hv g]
    rw [hρ, Submodule.mem_bot] at hf
    exact e.injective (hf.trans e.map_zero.symm)
  · exact (H1Congr _ _ (MulEquiv.refl G) e he).finrank_eq.trans hH

/-- The full module in B.5.1(i), when its commutator core covers the natural
module, splits as that core and its fixed space. -/
theorem natural_cover_splitting {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (C : Subrepresentation σ) (hq : HasTrivialQuotient C)
    (p : C.toRepresentation.IntertwiningMap (natural (Space n))) (hp : IsCover p) :
    IsCompl C.toSubmodule (fixed σ) := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  apply isCompl_fixed_of_cover C hq p hp (natural_H1_zero hn) (dual_H1_zero hn)
  exact natural_invariants (by simpa [Space] using (le_trans (by decide : 2 ≤ 4) hn))

/-- The dual natural alternative also splits, including all globally fixed summands. -/
theorem dual_cover_splitting {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (C : Subrepresentation σ) (hq : HasTrivialQuotient C)
    (p : C.toRepresentation.IntertwiningMap (natural (Space n)).dual) (hp : IsCover p) :
    IsCompl C.toSubmodule (fixed σ) := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  apply isCompl_fixed_of_cover C hq p hp (dual_H1_zero hn)
  · rw [doubleDual_H1_finrank, natural_H1_zero hn]
  · change (natural (Space n)).dual.invariants = ⊥
    rw [invariants_dual_eq_commutator_annihilator,
      natural_coinvariants (by simpa [Space] using (le_trans (by decide : 2 ≤ 4) hn)),
      Submodule.dualAnnihilator_top]


/-- The original natural covering map is an actual linear equivalence. -/
noncomputable def naturalCoverEquiv {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (p : σ.IntertwiningMap (natural (Space n))) (hp : IsCover p) : W ≃ₗ[ZMod 2] Space n :=
  LinearEquiv.ofBijective p.toLinearMap ⟨natural_cover_injective hn p hp, hp.1⟩

/-- The original dual covering map is an actual linear equivalence. -/
noncomputable def dualCoverEquiv {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (p : σ.IntertwiningMap (natural (Space n)).dual) (hp : IsCover p) :
    W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Space n) :=
  LinearEquiv.ofBijective p.toLinearMap ⟨dual_cover_injective hn p hp, hp.1⟩

/-- The parabolic construction transports along the original natural covering map. -/
theorem natural_cover_calculation {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (p : σ.IntertwiningMap (natural (Space n))) (hp : IsCover p)
    (R M : Subgroup (LinearGroup n)) :
    (fixedCommutator σ R M).map p.toLinearMap = fixedCommutator (natural (Space n)) R M :=
  fixedCommutator_map_equiv σ (natural (Space n)) (naturalCoverEquiv hn p hp)
    (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v) R M

/-- The parabolic construction transports along the original dual covering map. -/
theorem dual_cover_calculation {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (p : σ.IntertwiningMap (natural (Space n)).dual) (hp : IsCover p)
    (R M : Subgroup (LinearGroup n)) :
    (fixedCommutator σ R M).map p.toLinearMap =
      fixedCommutator (natural (Space n)).dual R M :=
  fixedCommutator_map_equiv σ (natural (Space n)).dual (dualCoverEquiv hn p hp)
    (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v) R M

/-- Splitting off a globally fixed summand does not change the actual parabolic
commutator. The equality uses the original inclusion of C into the full module. -/
theorem fixedCommutator_of_fixed_supplement {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (C : Subrepresentation σ)
    (hsup : C.toSubmodule ⊔ fixed σ = ⊤) (R M : Subgroup G) :
    fixedCommutator σ R M =
      (fixedCommutator C.toRepresentation R M).map C.toSubmodule.subtype := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp
      (show v ∈ C.toSubmodule ⊔ fixed σ from hsup ▸ Submodule.mem_top)
    have hcf : (⟨c, hc⟩ : C.toSubmodule) ∈ BinaryOffender.fixedSpace C.toRepresentation R := by
      intro r
      apply Subtype.ext
      have h := hv r
      change σ r.val v = v at h
      rw [← hcz, map_add, hz r.val] at h
      exact add_right_cancel h
    refine ⟨C.toRepresentation g ⟨c, hc⟩ - ⟨c, hc⟩, ?_, ?_⟩
    · exact Submodule.subset_span ⟨g, hg, ⟨c, hc⟩, hcf, rfl⟩
    · change σ g c - c = σ g v - v
      rw [← hcz, map_add, hz g]
      abel
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    change σ g (v : W) - (v : W) ∈ fixedCommutator σ R M
    apply Submodule.subset_span
    refine ⟨g, hg, v, ?_, rfl⟩
    intro r
    exact congrArg Subtype.val (hv r)

/-- A natural central-cover core gives the full module's C.4.8 calculation,
including arbitrary globally fixed summands. -/
theorem full_natural_cover_calculation {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (C : Subrepresentation σ) (hq : HasTrivialQuotient C)
    (p : C.toRepresentation.IntertwiningMap (natural (Space n))) (hp : IsCover p)
    (R M : Subgroup (LinearGroup n)) :
    fixedCommutator σ R M =
      (fixedCommutator C.toRepresentation R M).map C.toSubmodule.subtype ∧
    (fixedCommutator C.toRepresentation R M).map p.toLinearMap =
      fixedCommutator (natural (Space n)) R M :=
  ⟨fixedCommutator_of_fixed_supplement σ C
    (natural_cover_splitting hn C hq p hp).sup_eq_top R M,
    natural_cover_calculation hn p hp R M⟩

/-- The full-module calculation for a dual natural central-cover core. -/
theorem full_dual_cover_calculation {n : ℕ} (hn : 4 ≤ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (LinearGroup n) W}
    (C : Subrepresentation σ) (hq : HasTrivialQuotient C)
    (p : C.toRepresentation.IntertwiningMap (natural (Space n)).dual) (hp : IsCover p)
    (R M : Subgroup (LinearGroup n)) :
    fixedCommutator σ R M =
      (fixedCommutator C.toRepresentation R M).map C.toSubmodule.subtype ∧
    (fixedCommutator C.toRepresentation R M).map p.toLinearMap =
      fixedCommutator (natural (Space n)).dual R M :=
  ⟨fixedCommutator_of_fixed_supplement σ C
    (dual_cover_splitting hn C hq p hp).sup_eq_top R M,
    dual_cover_calculation hn p hp R M⟩

end Representation.BinaryParabolicNatural
