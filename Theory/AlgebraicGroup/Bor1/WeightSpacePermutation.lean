module

public import Theory.AlgebraicGroup.Bor1.CommonEigenspaces
public import Theory.AlgebraicGroup.Bor1.NormalWeights

universe u v w

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The abstract linear representation underlying a rational representation. -/
@[expose]
public def rationalRepresentationUnderlying
    {G : Variety k} [AlgebraicGroup G]
    (ρ : RationalRepresentation G V) :
    Representation k (Variety.Point G) V :=
  (Units.coeHom (Module.End k V)).comp ρ.action

/-- The simultaneous eigenspace belonging to a joint eigenvalue function. -/
@[expose]
public def Representation.commonEigenspace
    (ρ : Representation k Γ V) (N : Subgroup Γ) (χ : N → k) :
    Submodule k V :=
  ⨅ n : N, Module.End.eigenspace (ρ n : Module.End k V) (χ n)

/-- Joint eigenvalue functions whose common eigenspace is nonzero. -/
@[expose]
public def Representation.commonWeightIndex
    (ρ : Representation k Γ V) (N : Subgroup Γ) :=
  {χ : N → k // Representation.commonEigenspace ρ N χ ≠ ⊥}

/-- The nonzero common weight space indexed by `χ`. -/
@[expose]
public def Representation.commonWeightSpace
    (ρ : Representation k Γ V) (N : Subgroup Γ)
    (χ : Representation.commonWeightIndex ρ N) : Submodule k V :=
  Representation.commonEigenspace ρ N χ.1

/-- The sum of all nonzero common weight spaces. -/
@[expose]
public def Representation.commonWeightSpan
    (ρ : Representation k Γ V) (N : Subgroup Γ) : Submodule k V :=
  ⨆ χ : Representation.commonWeightIndex ρ N,
    Representation.commonWeightSpace ρ N χ

/-- The nonzero common weight spaces form an independent family. -/
public theorem Representation.commonWeightSpace_iSupIndep
    (ρ : Representation k Γ V) (N : Subgroup Γ) :
    iSupIndep (Representation.commonWeightSpace ρ N) := by
  exact (iSupIndep_commonEigenspaces
    (fun n : N => (ρ n : Module.End k V))).comp Subtype.val_injective

/-- Conjugation by `g` permutes the nonzero common weights of a normal
subgroup. -/
@[expose]
public noncomputable def Representation.normalCommonWeightEquiv
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal] (g : Γ) :
    Representation.commonWeightIndex ρ N ≃
      Representation.commonWeightIndex ρ N where
  toFun χ := ⟨normalSubgroupConjugateWeight N χ.1 g,
    Representation.commonEigenspace_conjugateWeight_ne_bot
      ρ N χ.1 χ.2 g⟩
  invFun χ := ⟨normalSubgroupConjugateWeight N χ.1 g⁻¹,
    Representation.commonEigenspace_conjugateWeight_ne_bot
      ρ N χ.1 χ.2 g⁻¹⟩
  left_inv χ := by
    apply Subtype.ext
    funext n
    dsimp [normalSubgroupConjugateWeight]
    apply congrArg χ.1
    apply Subtype.ext
    group
  right_inv χ := by
    apply Subtype.ext
    funext n
    dsimp [normalSubgroupConjugateWeight]
    apply congrArg χ.1
    apply Subtype.ext
    group

/-- The normal-conjugation equivalences assemble into a permutation
representation of the ambient group on the common weights. -/
@[expose]
public noncomputable def Representation.normalCommonWeightPermutation
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal] :
    Γ →* Equiv.Perm (Representation.commonWeightIndex ρ N) where
  toFun := Representation.normalCommonWeightEquiv ρ N
  map_one' := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    funext n
    dsimp [normalCommonWeightEquiv, normalSubgroupConjugateWeight]
    apply congrArg χ.1
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    funext n
    dsimp [normalCommonWeightEquiv, normalSubgroupConjugateWeight]
    apply congrArg χ.1
    apply Subtype.ext
    group

/-- The ambient representation sends each common weight space exactly to the
space indexed by the conjugated weight. -/
public theorem Representation.commonWeightSpace_map
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (g : Γ) (χ : Representation.commonWeightIndex ρ N) :
    Submodule.map (ρ g : Module.End k V)
        (Representation.commonWeightSpace ρ N χ) =
      Representation.commonWeightSpace ρ N
        (Representation.normalCommonWeightPermutation ρ N g χ) := by
  exact Representation.commonEigenspace_conjugateWeight_eq_map
    ρ N χ.1 g

/-- The sum of all common weight spaces is invariant under the ambient
normalizing representation. -/
public theorem Representation.commonWeightSpan_invariant
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (g : Γ) :
    Submodule.map (ρ g : Module.End k V)
        (Representation.commonWeightSpan ρ N) =
      Representation.commonWeightSpan ρ N := by
  rw [Representation.commonWeightSpan, Submodule.map_iSup]
  simp_rw [Representation.commonWeightSpace_map ρ N g]
  exact Equiv.iSup_comp
    (g := Representation.commonWeightSpace ρ N)
    (Representation.normalCommonWeightPermutation ρ N g)

/-- A common weight space, regarded as a submodule of their total span. -/
@[expose]
public def Representation.commonWeightBlock
    (ρ : Representation k Γ V) (N : Subgroup Γ)
    (χ : Representation.commonWeightIndex ρ N) :
    Submodule k (Representation.commonWeightSpan ρ N) :=
  (Representation.commonWeightSpace ρ N χ).comap
    (Representation.commonWeightSpan ρ N).subtype

/-- Mapping a weight block into the ambient space recovers its weight space. -/
public theorem Representation.commonWeightBlock_map_subtype
    (ρ : Representation k Γ V) (N : Subgroup Γ)
    (χ : Representation.commonWeightIndex ρ N) :
    (Representation.commonWeightBlock ρ N χ).map
        (Representation.commonWeightSpan ρ N).subtype =
      Representation.commonWeightSpace ρ N χ := by
  rw [Representation.commonWeightBlock, Submodule.map_comap_eq,
    Submodule.range_subtype, inf_eq_right]
  exact le_iSup (Representation.commonWeightSpace ρ N) χ

/-- Inside their total span, the common weight blocks span the whole space. -/
public theorem Representation.commonWeightBlock_iSup_eq_top
    (ρ : Representation k Γ V) (N : Subgroup Γ) :
    ⨆ χ, Representation.commonWeightBlock ρ N χ = ⊤ := by
  let F := Representation.commonWeightSpan ρ N
  let blocks := Representation.commonWeightBlock ρ N
  have hmap_each : ∀ χ,
      (blocks χ).map F.subtype =
        Representation.commonWeightSpace ρ N χ := by
    intro χ
    exact Representation.commonWeightBlock_map_subtype ρ N χ
  have hmap : (⨆ χ, blocks χ).map F.subtype = F := by
    rw [Submodule.map_iSup]
    simp_rw [hmap_each]
    rfl
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hxmap : (x : V) ∈ (⨆ χ, blocks χ).map F.subtype := by
    rw [hmap]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hxmap
  have hyxeq : y = x := Subtype.ext hyx
  rwa [hyxeq] at hy

/-- Inside their total span, the common weight blocks remain independent. -/
public theorem Representation.commonWeightBlock_iSupIndep
    (ρ : Representation k Γ V) (N : Subgroup Γ) :
    iSupIndep (Representation.commonWeightBlock ρ N) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s vectors hvectors hsum χ hχ
  have hvalmem : ∀ μ ∈ s, (vectors μ : V) ∈
      Representation.commonWeightSpace ρ N μ := by
    intro μ hμ
    exact hvectors μ hμ
  have hvalsum : ∑ μ ∈ s, (vectors μ : V) = 0 := by
    have h := congrArg
      (Representation.commonWeightSpan ρ N).subtype hsum
    simpa using h
  have hzero :=
    (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
      (Representation.commonWeightSpace ρ N)).mp
      (Representation.commonWeightSpace_iSupIndep ρ N)
      s (fun μ => (vectors μ : V)) hvalmem hvalsum χ hχ
  apply Subtype.ext
  exact hzero

/-- Any representation on the common-weight span satisfying the pointwise
restriction equation permutes the internal weight blocks by normal
conjugation. -/
public theorem Representation.commonWeightBlock_map_of_restriction
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (τ : Γ →* LinearMap.GeneralLinearGroup k
      (Representation.commonWeightSpan ρ N))
    (hτ : ∀ g x,
      ((((τ g : LinearMap.GeneralLinearGroup k
        (Representation.commonWeightSpan ρ N)) : Module.End k
          (Representation.commonWeightSpan ρ N)) x :
            Representation.commonWeightSpan ρ N) : V) =
        (ρ g : Module.End k V) (x : V))
    (g : Γ) (χ : Representation.commonWeightIndex ρ N) :
    Submodule.map
        (τ g : Module.End k (Representation.commonWeightSpan ρ N))
        (Representation.commonWeightBlock ρ N χ) =
      Representation.commonWeightBlock ρ N
        (Representation.normalCommonWeightPermutation ρ N g χ) := by
  let F := Representation.commonWeightSpan ρ N
  apply (Submodule.map_injective_of_injective F.injective_subtype)
  have hlinear : F.subtype.comp (τ g : Module.End k F) =
      (ρ g : Module.End k V).comp F.subtype := by
    apply LinearMap.ext
    intro x
    exact hτ g x
  calc
    (Submodule.map (τ g : Module.End k F)
        (Representation.commonWeightBlock ρ N χ)).map F.subtype =
        (Representation.commonWeightBlock ρ N χ).map
          (F.subtype.comp (τ g : Module.End k F)) :=
      (Submodule.map_comp _ _ _).symm
    _ = (Representation.commonWeightBlock ρ N χ).map
          ((ρ g : Module.End k V).comp F.subtype) := by rw [hlinear]
    _ = Submodule.map (ρ g : Module.End k V)
          ((Representation.commonWeightBlock ρ N χ).map F.subtype) :=
      Submodule.map_comp _ _ _
    _ = Submodule.map (ρ g : Module.End k V)
          (Representation.commonWeightSpace ρ N χ) := by
      rw [Representation.commonWeightBlock_map_subtype]
    _ = Representation.commonWeightSpace ρ N
          (Representation.normalCommonWeightPermutation ρ N g χ) :=
      Representation.commonWeightSpace_map ρ N g χ
    _ = (Representation.commonWeightBlock ρ N
          (Representation.normalCommonWeightPermutation ρ N g χ)).map
          F.subtype :=
      (Representation.commonWeightBlock_map_subtype ρ N _).symm

/-- If a representation on the common-weight span is the restriction of the
ambient representation, each element of `N` acts by its weight scalar on
every internal weight block. -/
public theorem Representation.commonWeightBlock_scalar_of_mem_of_restriction
    (ρ : Representation k Γ V) (N : Subgroup Γ)
    (τ : Γ →* LinearMap.GeneralLinearGroup k
      (Representation.commonWeightSpan ρ N))
    (hτ : ∀ g x,
      ((((τ g : LinearMap.GeneralLinearGroup k
        (Representation.commonWeightSpan ρ N)) : Module.End k
          (Representation.commonWeightSpan ρ N)) x :
            Representation.commonWeightSpan ρ N) : V) =
        (ρ g : Module.End k V) (x : V))
    (n : N) :
    ∀ χ, ∃ c : k, ∀ x : Representation.commonWeightSpan ρ N,
      x ∈ Representation.commonWeightBlock ρ N χ →
      (τ n.1 : Module.End k (Representation.commonWeightSpan ρ N)) x =
        c • x := by
  intro χ
  refine ⟨χ.1 n, ?_⟩
  intro x hx
  apply Subtype.ext
  calc
    (((τ n.1 : Module.End k (Representation.commonWeightSpan ρ N)) x :
        Representation.commonWeightSpan ρ N) : V) =
        (ρ n.1 : Module.End k V) (x : V) := hτ n.1 x
    _ = χ.1 n • (x : V) := by
      apply Module.End.mem_eigenspace_iff.mp
      have hxall : (x : V) ∈ Representation.commonEigenspace ρ N χ.1 := hx
      rw [Representation.commonEigenspace, Submodule.mem_iInf] at hxall
      exact hxall n
    _ = ((χ.1 n • x : Representation.commonWeightSpan ρ N) : V) := rfl

/-- The common-weight span of a normal subgroup is an invariant submodule of
the original rational representation. -/
public theorem RationalRepresentation.commonWeightSpan_isInvariantSubmodule
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    (ρ : RationalRepresentation G V)
    (N : Subgroup (Variety.Point G)) [N.Normal] :
    IsInvariantSubmodule ρ
      (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N) := by
  intro g x hx
  have hmem : (ρ.action g : Module.End k V) x ∈
      Submodule.map (ρ.action g : Module.End k V)
        (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N) :=
      ⟨x, hx, rfl⟩
  change (rationalRepresentationUnderlying ρ g) x ∈
    Submodule.map (rationalRepresentationUnderlying ρ g)
      (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N)
    at hmem
  rw [Representation.commonWeightSpan_invariant
    (rationalRepresentationUnderlying ρ) N g] at hmem
  exact hmem

/-- A restriction representation on the common-weight span permutes its
internal weight blocks exactly as the ambient representation does.  The
pointwise restriction equation is used as a light behavioral bridge. -/
public theorem RationalRepresentation.commonWeightBlock_map_of_restriction
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    (ρ : RationalRepresentation G V)
    (N : Subgroup (Variety.Point G)) [N.Normal]
    (τ : RationalRepresentation G
      (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N))
    (hτ : ∀ g x,
      (((τ.action g : Module.End k
        (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N)) x :
          Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N) : V) =
        (ρ.action g : Module.End k V) (x : V))
    (g : Variety.Point G)
    (χ : Representation.commonWeightIndex
      (rationalRepresentationUnderlying ρ) N) :
    Submodule.map
        (τ.action g : Module.End k
          (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N))
        (Representation.commonWeightBlock (rationalRepresentationUnderlying ρ) N χ) =
      Representation.commonWeightBlock (rationalRepresentationUnderlying ρ) N
        (Representation.normalCommonWeightPermutation
          (rationalRepresentationUnderlying ρ) N g χ) := by
  exact Representation.commonWeightBlock_map_of_restriction
    (rationalRepresentationUnderlying ρ) N τ.action hτ g χ

end Theory.AlgebraicGroup.Bor1
