module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Rigidity

/-!
# Transvection fixed-space kernels in the degree-six models

A permutation fixing the six indicated duads is identity or `(01)`.
Applied to fixed natural vectors, this determines the pointwise kernel for
one transposition; conjugation treats every natural transvection. The
augmentation fixed space maps onto the natural fixed space because their
codimensions agree. Thus the same kernel equality holds on the cover.
All finite calculations are checked by the Lean kernel.

Source: Aschbacher–Smith 13.8.26, printed p.962, and B.3.2–4, pp.83–85.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
open BinaryPermutation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix (pair)

private theorem mem_A1 (g : Symmetric) :
    g ∈ disjointTranspositions 6 1 ↔ g = 1 ∨ g = Equiv.swap 0 1 := by
  rw [mem_disjointTranspositions_iff (⟨1, by decide⟩ : Fin 4) g]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [initialWords, dWords, cubeWords, pairSwap]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem fixed_duads_certificate : ∀ g : Symmetric,
    pair (g 0) (g 1) = pair 0 1 →
    pair (g 2) (g 3) = pair 2 3 →
    pair (g 2) (g 4) = pair 2 4 →
    pair (g 2) (g 5) = pair 2 5 →
    pair (g 3) (g 4) = pair 3 4 →
    pair (g 3) (g 5) = pair 3 5 →
    g = 1 ∨ g = Equiv.swap 0 1 := by decide +kernel

private theorem natural_kernel_A1 :
    subspaceKernel symmetricAction
      (fixedSpace symmetricAction (disjointTranspositions 6 1)) ⊤ =
        disjointTranspositions 6 1 := by
  apply le_antisymm
  · intro g hg
    apply (mem_A1 g).mpr
    apply fixed_duads_certificate g
    all_goals
      apply (pairVector_eq_iff (g.injective.ne (by decide)) (by decide)).mp
      rw [← pairVector_map]
      apply hg.2
      intro a
      rcases (mem_A1 a.val).mp a.property with ha | ha
      · simp [ha]
      · change naturalRepresentation (Fin 6) a.val _ = _
        rw [ha, pairVector_map]
        first | rfl | simpa using pairVector_comm (1 : Fin 6) 0
  · intro a ha
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨a, ha⟩⟩

/-- Pointwise-kernel rigidity transports through the actual group embedding
and an intertwining linear equivalence. Surjectivity of the actor map is not needed. -/
theorem fixed_kernel_eq_of_equivariant
    {G D U W : Type*} [Group G] [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G U) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Injective f) (E : U ≃ₗ[ZMod 2] W)
    (he : ∀ g u, E (ρ g u) = σ (f g) (E u)) (A : Subgroup G)
    (hσ : subspaceKernel σ (fixedSpace σ (A.map f)) ⊤ = A.map f) :
    subspaceKernel ρ (fixedSpace ρ A) ⊤ = A := by
  apply le_antisymm
  · intro g hg
    have hm : f g ∈ A.map f := by
      rw [← hσ]
      refine ⟨Subgroup.mem_top _, ?_⟩
      intro w hw
      rw [← fixedSpace_map_equivariant ρ σ f E he A] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      change σ (f g) (E v) = E v
      rw [← he, hg.2 v hv]
    obtain ⟨a, ha, hag⟩ := hm
    exact hf hag ▸ ha
  · intro a ha
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨a, ha⟩⟩

private theorem conjugate_kernel
    {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) G U) (A : Subgroup G) (g : G)
    (h : subspaceKernel ρ (fixedSpace ρ A) ⊤ = A) :
    subspaceKernel ρ (fixedSpace ρ (A.map (MulAut.conj g).toMonoidHom)) ⊤ =
      A.map (MulAut.conj g).toMonoidHom := by
  let f := (MulAut.conj g⁻¹).toMonoidHom
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g⁻¹)
  have he (a : G) (u : U) : E (ρ a u) = ρ (f a) (E u) := by
    change ρ g⁻¹ (ρ a u) = ρ (g⁻¹ * a * (g⁻¹)⁻¹) (ρ g⁻¹ u)
    simp only [← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  apply fixed_kernel_eq_of_equivariant ρ ρ f (MulAut.conj g⁻¹).injective E he
  have hm : (A.map (MulAut.conj g).toMonoidHom).map f = A := by
    rw [Subgroup.map_map]
    have hf : f.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
      ext a
      change g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a
      simp [mul_assoc]
    rw [hf, Subgroup.map_id]
  rw [hm]
  exact h

/-- A natural transvection group is the full pointwise stabilizer of its fixed space. -/
theorem natural_fixed_kernel {A : Subgroup Symmetric}
    (hA : IsElementaryTwo A) (hcodim : fixedCodim symmetricAction A = 1) :
    subspaceKernel symmetricAction (fixedSpace symmetricAction A) ⊤ = A := by
  obtain ⟨g, rfl⟩ := natural_small_codim_conjugate hA hcodim.le
  exact conjugate_kernel symmetricAction _ g natural_kernel_A1

/-- On every elementary actor the augmentation and natural fixed codimensions agree. -/
theorem core_fixedCodim_eq_natural {A : Subgroup Symmetric} (hA : IsElementaryTwo A) :
    fixedCodim (coreRepresentation (Fin 6)) A = fixedCodim symmetricAction A := by
  rcases elementaryTwo_conjugacy hA with he | he | he | he | he | he | he | he | he | he
  all_goals obtain ⟨g, rfl⟩ := he
  all_goals rw [fixedCodim_map_conj, fixedCodim_map_conj]
  · exact fixedCodim_A1.2.2.1.trans fixedCodim_A1.2.2.2.symm
  · exact fixedCodim_A2.2.2.1.trans fixedCodim_A2.2.2.2.symm
  · exact fixedCodim_D.2.2.1.trans fixedCodim_D.2.2.2.symm
  · exact fixedCodim_exceptional.2.2.1.trans fixedCodim_exceptional.2.2.2.symm
  · exact fixedCodim_evenPart.2.2.1.trans fixedCodim_evenPart.2.2.2.symm
  · exact fixedCodim_plus.2.2.1.trans fixedCodim_plus.2.2.2.symm
  · exact fixedCodim_double.2.2.1.trans fixedCodim_double.2.2.2.symm
  · exact fixedCodim_triple.2.2.1.trans fixedCodim_triple.2.2.2.symm
  · exact fixedCodim_klein.2.2.1.trans fixedCodim_klein.2.2.2.symm
  · exact fixedCodim_twisted.2.2.1.trans fixedCodim_twisted.2.2.2.symm

private theorem fixedSpace_map_of_codim_eq
    {G U W : Type*} [Group G]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G U) (σ : Representation (ZMod 2) G W)
    (q : U →ₗ[ZMod 2] W) (hq : Function.Surjective q)
    (he : ∀ g u, q (ρ g u) = σ g (q u)) (A : Subgroup G)
    (hc : fixedCodim ρ A = fixedCodim σ A) :
    (fixedSpace ρ A).map q = fixedSpace σ A := by
  let C := fixedSpace ρ A
  have hle : C.map q ≤ fixedSpace σ A := by
    rintro _ ⟨u, hu, rfl⟩ a
    change σ (a : G) (q u) = q u
    rw [← he]
    exact congrArg q (hu a)
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply le_antisymm (Submodule.finrank_mono hle)
  let k : (q.comp C.subtype).ker →ₗ[ZMod 2] q.ker :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => z.val) h
  have hkd := LinearMap.finrank_le_finrank_of_injective hk
  have hd := (q.comp C.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype] at hd
  have hq := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr ‹Function.Surjective q›, finrank_top] at hq
  have hu := fixedCodim_add_finrank ρ A
  have hw := fixedCodim_add_finrank σ A
  change Module.finrank (ZMod 2) (fixedSpace σ A) ≤ Module.finrank (ZMod 2) (C.map q)
  change fixedCodim ρ A + Module.finrank (ZMod 2) C = Module.finrank (ZMod 2) U at hu
  omega

/-- Fixed vectors on the augmentation cover surject onto natural fixed vectors. -/
theorem core_fixedSpace_map {A : Subgroup Symmetric} (hA : IsElementaryTwo A) :
    (fixedSpace (coreRepresentation (Fin 6)) A).map (coreToNatural (Fin 6)) =
      fixedSpace symmetricAction A :=
  fixedSpace_map_of_codim_eq _ _ _ coreToNatural_surjective
    coreToNatural_equivariant A (core_fixedCodim_eq_natural hA)

/-- The transvection pointwise-kernel assertion also holds on the augmentation cover. -/
theorem core_fixed_kernel {A : Subgroup Symmetric}
    (hA : IsElementaryTwo A)
    (hcodim : fixedCodim (coreRepresentation (Fin 6)) A = 1) :
    subspaceKernel (coreRepresentation (Fin 6))
      (fixedSpace (coreRepresentation (Fin 6)) A) ⊤ = A := by
  apply le_antisymm
  · intro g hg
    rw [← natural_fixed_kernel hA ((core_fixedCodim_eq_natural hA).symm.trans hcodim)]
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    rw [← core_fixedSpace_map hA] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← coreToNatural_equivariant, hg.2 u hu]
  · intro a ha
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨a, ha⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
