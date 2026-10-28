module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialIntertwining
public import Theory.AlgebraicGroup.Bor1.WeightDecompositionCentralizer
public import Theory.AlgebraicGroup.Bor1.WeightSpacePermutation

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- If the differential on the common-weight-span restriction centralizes the
block-diagonal endomorphisms, then the ambient differential preserves the line
of every nonzero common weight vector. -/
public theorem RationalRepresentation.differential_mem_vectorLine_of_commonWeightBlock_centralizer
    (ρ : RationalRepresentation G V)
    (N : Subgroup (Variety.Point G))
    (v : V) (hv : v ≠ 0)
    (hNLine : ∀ n : N, (ρ.action n.1 : Module.End k V) v ∈ k ∙ v)
    (τ : RationalRepresentation G
      (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N))
    (hτ : IsRestrictionRepresentation ρ
      (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N) τ)
    (b : Module.Basis
      (Fin (Module.finrank k
        (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N))) k
      (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N))
    (f : AlgebraicGroup.Morphism G
      (glVarietyOf k
        (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N)))
    (hf : ∀ g, glPointEquivOf k
      (Representation.commonWeightSpan (rationalRepresentationUnderlying ρ) N)
      b (f.onPoints g) = τ.action g)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (q : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hq : ∀ g, glPointEquivOf k V e (q.onPoints g) = ρ.action g)
    (D : IdentityPointDerivation G)
    (hcentral : ∀ u : blockDiagonalEnd
      (Representation.commonWeightBlock (rationalRepresentationUnderlying ρ) N),
      Commute (rationalRepresentationDifferential τ b f D) u.1) :
    rationalRepresentationDifferential ρ e q D v ∈ k ∙ v := by
  classical
  let σ := rationalRepresentationUnderlying ρ
  let χ : N → k := fun n =>
    Classical.choose (Submodule.mem_span_singleton.mp (hNLine n))
  have hχ (n : N) : (ρ.action n.1 : Module.End k V) v = χ n • v :=
    (Classical.choose_spec
      (Submodule.mem_span_singleton.mp (hNLine n))).symm
  have hvcommon : v ∈ Representation.commonEigenspace σ N χ := by
    rw [Representation.commonEigenspace, Submodule.mem_iInf]
    intro n
    exact Module.End.mem_eigenspace_iff.mpr (hχ n)
  have hcommonne : Representation.commonEigenspace σ N χ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, hvcommon, hv⟩
  let χD : Representation.commonWeightIndex σ N := ⟨χ, hcommonne⟩
  let F := Representation.commonWeightSpan σ N
  have hvF : v ∈ F :=
    (le_iSup (Representation.commonWeightSpace σ N) χD) hvcommon
  let vf : F := ⟨v, hvF⟩
  have hvblock : vf ∈ Representation.commonWeightBlock σ N χD := hvcommon
  have hscalar :=
    (blockDiagonalEnd_centralizer_iff_blockwise_scalar
      (Representation.commonWeightBlock σ N)
      (Representation.commonWeightBlock_iSupIndep σ N)
      (Representation.commonWeightBlock_iSup_eq_top σ N)
      (rationalRepresentationDifferential τ b f D)).mp hcentral χD
  obtain ⟨c, hc⟩ := hscalar
  have hvscalar : rationalRepresentationDifferential τ b f D vf = c • vf :=
    hc vf hvblock
  have hinter := rationalRepresentationDifferential_intertwines
    τ ρ F.subtype hτ b f hf e q hq D vf
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  calc
    c • v = ((c • vf : F) : V) := rfl
    _ = ((rationalRepresentationDifferential τ b f D vf : F) : V) :=
      congrArg Subtype.val hvscalar.symm
    _ = rationalRepresentationDifferential ρ e q D v := hinter

end Theory.AlgebraicGroup.Bor1
