module
public import Theory.AlgebraicGroup.Representations.Nilpotence
public import Theory.AlgebraicGroup.Representations.Subrepresentation

universe u v w
open scoped MonoidAlgebra

namespace Theory.AlgebraicGroup

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Burnside's theorem in the form needed for Kolchin's theorem: over an
algebraically closed field, the group algebra of a finite-dimensional
irreducible representation acts as every linear endomorphism. -/
public lemma irreducibleRepresentation_asAlgebraHom_surjective
    (ρ : Representation k Γ V) [ρ.IsIrreducible] :
    Function.Surjective ρ.asAlgebraHom := by
  classical
  let A := k[Γ]
  let D := Module.End A ρ.asModule
  let : Module D ρ.asModule := Module.End.applyModule
  let : IsScalarTower k D ρ.asModule := ⟨fun _ _ _ => rfl⟩
  let : Module.Finite D ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k D ρ.asModule
  intro f
  let fD : Module.End D ρ.asModule :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro d x
        obtain ⟨c, hc⟩ :=
          (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
            (A := A) (V := ρ.asModule) k).2 d
        rw [← hc]
        change f (c • x) = c • f x
        exact f.map_smul c x }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective
      (R := A) (M := ρ.asModule) fD
  refine ⟨a, ?_⟩
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun ha x

open scoped MonoidAlgebra

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- An irreducible finite-dimensional representation whose every group
operator is unipotent is the trivial representation. -/
public lemma irreducible_unipotentRepresentation_eq_one
    (ρ : Representation k Γ V) [ρ.IsIrreducible]
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1)) :
    ∀ g : Γ, ρ g = 1 := by
  intro g
  apply sub_eq_zero.mp
  apply endomorphism_eq_zero_of_trace_mul_eq_zero (ρ g - 1)
  intro y
  obtain ⟨a, ha⟩ :=
    irreducibleRepresentation_asAlgebraHom_surjective ρ y
  rw [← ha]
  apply MonoidAlgebra.induction_on a
  · intro h
    rw [Representation.asAlgebraHom_of]
    rw [sub_mul, one_mul, ← ρ.map_mul, map_sub]
    have hgh :=
      (LinearMap.isNilpotent_trace_of_isNilpotent
        (hunipotent (g * h))).eq_zero
    have hh :=
      (LinearMap.isNilpotent_trace_of_isNilpotent
        (hunipotent h)).eq_zero
    rw [map_sub] at hgh hh
    exact sub_eq_zero.mpr
      (sub_eq_zero.mp hgh |>.trans (sub_eq_zero.mp hh).symm)
  · intro a b ha hb
    simp only [map_add, mul_add, ha, hb, add_zero]
  · intro c a ha
    simp only [map_smul, mul_smul_comm, ha, smul_zero]

open scoped MonoidAlgebra

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A finite-dimensional representation whose every operator is unipotent has
a nonzero vector fixed by the whole group. -/
public lemma unipotentRepresentation_exists_common_fixed_ne_zero
    (ρ : Representation k Γ V)
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1))
    [Nontrivial V] :
    ∃ x : V, x ≠ 0 ∧ ∀ g : Γ, ρ g x = x := by
  let : Nontrivial ρ.asModule := ρ.asModuleEquiv.toEquiv.nontrivial
  let : IsArtinian k[Γ] ρ.asModule :=
    isArtinian_of_tower k (inferInstance : IsArtinian k ρ.asModule)
  have htop : (⊤ : Submodule k[Γ] ρ.asModule) ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : ρ.asModule)
    intro h
    have hxbot : x ∈ (⊥ : Submodule k[Γ] ρ.asModule) := by
      rw [← h]
      trivial
    exact hx (by simpa using hxbot)
  obtain ⟨m, hmAtom, _⟩ :=
    (eq_bot_or_exists_atom_le (⊤ : Submodule k[Γ] ρ.asModule)).resolve_left htop
  let s : Subrepresentation ρ := Subrepresentation.ofSubmodule' m
  have hsAtom : IsAtom s := by
    apply (OrderIso.isAtom_iff
      (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)) s).mp
    change IsAtom m
    exact hmAtom
  let σ := s.toRepresentation
  let : σ.IsIrreducible :=
    Subrepresentation.isIrreducible_toRepresentation_of_isAtom s hsAtom
  have he (g : Γ) (x : s.toSubmodule) :
      (s.toSubmodule.subtype : s.toSubmodule →ₗ[k] V) (σ g x) =
        ρ g ((s.toSubmodule.subtype : s.toSubmodule →ₗ[k] V) x) := rfl
  have einj : Function.Injective
      (s.toSubmodule.subtype : s.toSubmodule →ₗ[k] V) :=
    s.toSubmodule.subtype_injective
  have hσunipotent : ∀ g : Γ, IsNilpotent (σ g - 1) := by
    intro g
    obtain ⟨n, hn⟩ := hunipotent g
    refine ⟨n, ?_⟩
    apply LinearMap.ext
    intro x
    apply einj
    have hpow : ∀ j : ℕ,
        (s.toSubmodule.subtype : s.toSubmodule →ₗ[k] V)
            (((σ g - 1) ^ j) x) =
          ((ρ g - 1) ^ j)
            ((s.toSubmodule.subtype : s.toSubmodule →ₗ[k] V) x) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
          simp only [LinearMap.sub_apply, Module.End.one_apply]
          rw [LinearMap.map_sub, he, ih]
    rw [hpow n, hn]
    simp
  have hσ := irreducible_unipotentRepresentation_eq_one σ hσunipotent
  have hsSub : s.toSubmodule ≠ ⊥ := by
    intro h
    apply hsAtom.1
    apply Subrepresentation.ext
    exact h
  let : Nontrivial s.toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr hsSub
  obtain ⟨x, hx⟩ := exists_ne (0 : s.toSubmodule)
  refine ⟨x, ?_, ?_⟩
  · exact fun h => hx (Subtype.ext h)
  · intro g
    have hg := LinearMap.congr_fun (hσ g) x
    exact congrArg Subtype.val hg

open scoped MonoidAlgebra

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A finite-dimensional representation whose every operator is unipotent has a
one-dimensional invariant subrepresentation. -/
public lemma unipotentRepresentation_exists_oneDimensional_subrepresentation
    (ρ : Representation k Γ V)
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1))
    [Nontrivial V] :
    ∃ σ : Subrepresentation ρ, Module.finrank k σ.toSubmodule = 1 := by
  obtain ⟨x, hx, hfix⟩ :=
    unipotentRepresentation_exists_common_fixed_ne_zero ρ hunipotent
  let W : Submodule k V := Submodule.span k {x}
  have hW : ∀ g : Γ, ∀ v : V, v ∈ W → ρ g v ∈ W := by
    intro g v hv
    rw [Submodule.mem_span_singleton] at hv ⊢
    obtain ⟨a, rfl⟩ := hv
    use a
    rw [map_smul, hfix]
  let σ : Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := hW }
  refine ⟨σ, ?_⟩
  dsimp [σ, W]
  exact finrank_span_singleton hx

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A nonzero finite-dimensional pointwise-unipotent representation has a
one-dimensional invariant subrepresentation whose quotient remains
pointwise unipotent. -/
public lemma
    unipotentRepresentation_exists_oneDimensional_subrepresentation_quotient_unipotent
    (ρ : Representation k Γ V)
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1))
    [Nontrivial V] :
    ∃ σ : Subrepresentation ρ,
      Module.finrank k σ.toSubmodule = 1 ∧
      ∀ g : Γ, IsNilpotent
        (ρ.quotient σ.toSubmodule
          (fun g => σ.apply_mem_toSubmodule g) g - 1) := by
  obtain ⟨σ, hσdim⟩ :=
    unipotentRepresentation_exists_oneDimensional_subrepresentation ρ hunipotent
  refine ⟨σ, hσdim, ?_⟩
  exact Representation.isNilpotent_quotient_sub_one ρ σ.toSubmodule
    (fun g => σ.apply_mem_toSubmodule g) hunipotent

end Theory.AlgebraicGroup
