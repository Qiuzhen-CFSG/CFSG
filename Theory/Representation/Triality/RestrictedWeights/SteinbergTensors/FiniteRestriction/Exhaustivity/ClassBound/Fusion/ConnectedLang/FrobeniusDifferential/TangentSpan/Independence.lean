module

public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Independence of torus and realized root tangents

Distinct realized roots give independent nonzero tangent vectors, since their
characters are distinct. The torus tangent has trivial character and is
disjoint from their span. This gives the lower dimension bound needed for the
root-product argument in Steinberg 6.2(b--c), without differentiating characters
or assuming separability. A matching upper bound then proves tangent spanning.

The character-weight argument also occurs for the concrete G2 carrier in
`Theory.AlgebraicGroup.RootSystems.G2ChevalleyTorusRootSupport`; here it applies
to arbitrary realized root data and keeps the ambient dimension premise explicit.
-/

noncomputable section

namespace Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}

/-- A realized root is a nontrivial character, because its integral pairing
with its own cocharacter is two. This remains valid in characteristic two. -/
public theorem RootGroupData.IsRealization.rootWeight_ne_one
    {D : RootGroupData K T} (hD : D.IsRealization) (a : D.Root) :
    D.rootWeight a ≠ 1 := by
  intro ha
  have hpair := hD.weightPairing_rootWeight a a
  have hdiag : D.pairing a a = 2 := hD.2.2.2.2.2.2.1 a
  rw [ha, hD.weightPairing_one, hdiag] at hpair
  norm_num at hpair

/-- The chosen root parametrizations give linearly independent ambient
tangent vectors. The weights used are group characters, not Lie characters. -/
public theorem realizedRootTangents_linearIndependent
    (D : RootGroupData K T) (hD : D.IsRealization)
    (x : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety) :
    LinearIndependent k (fun a => oneParameterTangent (D.rootSubgroup a) (x a)) := by
  let weights : D.Root → TorusWeight T := fun a => (D.rootWeight a)⁻¹
  have hweights : Function.Injective weights := by
    intro a b hab
    exact hD.1 (inv_injective hab)
  let p : D.Root → Submodule k (IdentityPointDerivation K) := fun a =>
    weightSpace (identityTangentRepresentation K) T (weights a)
  have hp : iSupIndep p :=
    (weightSpace_iSupIndep (identityTangentRepresentation K) T).comp hweights
  apply iSupIndep.linearIndependent p hp
  · intro a
    exact (oneParameterTangent_isWeightVector T (D.rootSubgroup a) (x a)
      (hD.2.2.1 a).2).2
  · intro a
    exact oneParameterTangent_ne_zero (D.rootSubgroup a) (x a)

/-- The embedded tangent of a torus has trivial conjugation weight. -/
public theorem torusTangentRange_le_trivialWeight (hT : IsTorus T.carrierVariety) :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap T.inclusion) ≤
      weightSpace (identityTangentRepresentation K) T 1 := by
  rintro D ⟨E, rfl⟩
  intro s
  apply Derivation.ext
  intro f
  have hone : (1 : TorusWeight T).pointCharacter s = 1 := rfl
  rw [hone, one_smul, identityTangentRepresentation_action_apply,
    Bor1.identityTangentMorphismLinearMap_apply,
    Bor1.identityTangentMorphismLinearMap_apply]
  change E (T.inclusion.toVariety.pullbackAlgHom
    ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).pullbackAlgHom f)) =
      E (T.inclusion.toVariety.pullbackAlgHom f)
  apply congrArg E
  apply Variety.PolynomialFunction.ext
  intro y
  change f (T.includePoint s * T.includePoint y * (T.includePoint s)⁻¹) =
    f (T.includePoint y)
  congr 1
  have hcomm : T.includePoint s * T.includePoint y =
      T.includePoint y * T.includePoint s := by
    have hcommT := hT.isMulCommutative
    rw [isMulCommutative_iff] at hcommT
    exact congrArg T.inclusion.onPoints (hcommT s y)
  rw [hcomm]
  simp

private def realizedTangentWeight (D : RootGroupData K T) :
    Option D.Root → TorusWeight T
  | none => 1
  | some a => (D.rootWeight a)⁻¹

private theorem realizedTangentWeight_injective
    (D : RootGroupData K T) (hD : D.IsRealization) :
    Function.Injective (realizedTangentWeight D) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b =>
          exfalso
          apply hD.rootWeight_ne_one b
          have h := congrArg Inv.inv hab
          simpa [realizedTangentWeight] using h.symm
  | some a =>
      cases b with
      | none =>
          exfalso
          apply hD.rootWeight_ne_one a
          have h := congrArg Inv.inv hab
          simpa [realizedTangentWeight] using h
      | some b =>
          congr 1
          exact hD.1 (inv_injective hab)

/-- The torus tangent and the span of the realized root tangents meet only at zero. -/
public theorem torusTangentRange_disjoint_realizedRootTangentSpan
    (D : RootGroupData K T) (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety)
    (x : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety) :
    Disjoint (LinearMap.range (Bor1.identityTangentMorphismLinearMap T.inclusion))
      (Submodule.span k (Set.range fun a =>
        oneParameterTangent (D.rootSubgroup a) (x a))) := by
  let p : Option D.Root → Submodule k (IdentityPointDerivation K) := fun i =>
    weightSpace (identityTangentRepresentation K) T (realizedTangentWeight D i)
  have hp : iSupIndep p :=
    (weightSpace_iSupIndep (identityTangentRepresentation K) T).comp
      (realizedTangentWeight_injective D hD)
  have hdisjoint : Disjoint (p none)
      (⨆ i ∈ Set.range (@some D.Root), p i) :=
    hp.disjoint_biSup (x := none) (y := Set.range (@some D.Root)) (by simp)
  apply hdisjoint.mono
  · exact torusTangentRange_le_trivialWeight hT
  · apply Submodule.span_le.mpr
    rintro v ⟨a, rfl⟩
    have hle : p (some a) ≤ (⨆ i ∈ Set.range (@some D.Root), p i) :=
      le_iSup_of_le (some a) (le_iSup_of_le ⟨a, rfl⟩ le_rfl)
    apply hle
    exact (oneParameterTangent_isWeightVector T (D.rootSubgroup a) (x a)
      (hD.2.2.1 a).2).2

/-- The embedded torus and the independent root tangent lines give the
expected lower bound for the ambient tangent dimension. -/
public theorem realized_torus_root_tangent_finrank_lower_bound
    (D : RootGroupData K T) [Finite D.Root] (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety)
    (x : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety) :
    Module.finrank k (Bor1.IdentityPointDerivation T.carrierVariety) + Nat.card D.Root ≤
      Module.finrank k (Bor1.IdentityPointDerivation K) := by
  let := Fintype.ofFinite D.Root
  have h := Submodule.finrank_add_finrank_le_of_disjoint
    (torusTangentRange_disjoint_realizedRootTangentSpan D hD hT x)
  rw [LinearMap.finrank_range_of_inj
    (Bor1.identityTangentMorphismLinearMap_inclusion_injective T),
    finrank_span_eq_card (realizedRootTangents_linearIndependent D hD x)] at h
  simpa only [Nat.card_eq_fintype_card] using h

/-- The independent torus and root directions span once the ambient dimension
is bounded by the torus dimension plus the number of roots. The geometric
upper bound is an explicit premise and is not inferred from point generation. -/
public theorem realized_torus_root_tangent_span_of_finrank_le
    (D : RootGroupData K T) [Finite D.Root] (hD : D.IsRealization)
    (hT : IsTorus T.carrierVariety)
    (x : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (hdim : Module.finrank k (Bor1.IdentityPointDerivation K) ≤
      Module.finrank k (Bor1.IdentityPointDerivation T.carrierVariety) + Nat.card D.Root) :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap T.inclusion) ⊔
      (⨆ a : D.Root, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (D.rootSubgroup a).inclusion)) = ⊤ := by
  let := Fintype.ofFinite D.Root
  have hsmall : LinearMap.range (Bor1.identityTangentMorphismLinearMap T.inclusion) ⊔
      Submodule.span k (Set.range fun a =>
        oneParameterTangent (D.rootSubgroup a) (x a)) = ⊤ := by
    apply Submodule.eq_top_of_disjoint
    · rw [LinearMap.finrank_range_of_inj
        (Bor1.identityTangentMorphismLinearMap_inclusion_injective T),
        finrank_span_eq_card (realizedRootTangents_linearIndependent D hD x)]
      simpa only [Nat.card_eq_fintype_card] using hdim
    · exact torusTangentRange_disjoint_realizedRootTangentSpan D hD hT x
  apply top_unique
  rw [← hsmall]
  apply sup_le_sup_left
  apply Submodule.span_le.mpr
  rintro v ⟨a, rfl⟩
  exact (le_iSup (fun b => LinearMap.range
    (Bor1.identityTangentMorphismLinearMap (D.rootSubgroup b).inclusion)) a)
      (oneParameterTangent_mem_range_inclusion (D.rootSubgroup a) (x a))

end Theory.AlgebraicGroup
