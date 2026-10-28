module
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.InvolutionBound
public import Theory.Representation.SimpleHeadQuotient.Independent
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.SpecificGroups.PSL3Two.PairedGraphInputs

/-!
# Intrinsic natural–dual recognition from a rank-two outer action

A fully moved binary representation of SL₃(2) with involution displacement
at most two has dimension at most six. An irreducible quotient is therefore
natural or dual-natural. An implemented noninner automorphism gives a quotient
of the opposite type. Their inequivalence makes the combined quotient onto
the six-dimensional natural–dual pair; the dimension bound makes it an
equivalence. No splitting or semisimplicity hypothesis is used.

The root-rank-two theorem is the intrinsic representation input for the
original global span section in Aschbacher–Smith E.2.17, printed p.230.
It uses the concrete H.6.1 irreducible catalogue and the three-involution
generation bound, with the literal implementing linear map.
-/

public section
open Representation Representation.BinaryOffender
namespace BinaryLinearThree.RankTwoOuterRecognition
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M] (ρ : Representation (ZMod 2) Group M)

omit [FiniteDimensional (ZMod 2) M] in
private theorem quotient_has_movement (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (N : Subrepresentation ρ) (hN : IsCoatom N) :
    ∃ g : Group, ∃ v : M ⧸ N.toSubmodule, N.quotientRepresentation g v ≠ v := by
  by_contra! h
  have hle : subspaceCommutator ρ ⊤ ⊤ ≤ N.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp
    change N.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (h g (N.toSubmodule.mkQ v))
  apply hN.1
  apply Subrepresentation.toSubmodule_injective
  exact top_unique (hfull ▸ hle)

private theorem exists_natural_or_dual_quotient [Nontrivial M]
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hdim : Module.finrank (ZMod 2) M ≤ 6) :
    (∃ p : ρ.IntertwiningMap W, Function.Surjective p) ∨
      ∃ p : ρ.IntertwiningMap W.dual, Function.Surjective p := by
  let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
  obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  let q : ρ.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  have hq : Function.Surjective q := N.toSubmodule.mkQ_surjective
  rcases IrreducibleCatalogue.classify_nontrivial N.quotientRepresentation
    (quotient_has_movement ρ hfull N hN) with he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact Or.inl ⟨e.toIntertwiningMap.comp q,e.toLinearEquiv.surjective.comp hq⟩
  · exact Or.inr ⟨e.toIntertwiningMap.comp q,e.toLinearEquiv.surjective.comp hq⟩
  · have hd := LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap) hq
    have he := e.toLinearEquiv.finrank_eq
    rw [finrank_steinberg] at he
    omega

-- Precompose a quotient with the actual implementing operator.
private def twistQuotient {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    {σ : Representation (ZMod 2) Group A}
    (α : MulAut Group) (f : M ≃ₗ[ZMod 2] M)
    (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v))
    (p : ρ.IntertwiningMap σ) : ρ.IntertwiningMap (σ.comp α.toMonoidHom) where
  toLinearMap := p.toLinearMap.comp f.toLinearMap
  isIntertwining' g := by
    ext v
    change p (f (ρ g v)) = σ (α g) (p (f v))
    rw [hf,p.isIntertwining]

private theorem natural_dual_quotients [Nontrivial M]
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hdim : Module.finrank (ZMod 2) M ≤ 6)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    ∃ p : ρ.IntertwiningMap W, ∃ q : ρ.IntertwiningMap W.dual,
      Function.Surjective p ∧ Function.Surjective q := by
  rcases exists_natural_or_dual_quotient ρ hfull hdim with ⟨p,hp⟩ | ⟨q,hq⟩
  · let e := AutomorphismAction.naturalOuterEquiv α hα
    exact ⟨p,e.toIntertwiningMap.comp (twistQuotient ρ α f hf p),hp,
      e.toLinearEquiv.surjective.comp (hp.comp f.surjective)⟩
  · let e := AutomorphismAction.dualOuterEquiv α hα
    exact ⟨e.toIntertwiningMap.comp (twistQuotient ρ α f hf q),q,
      e.toLinearEquiv.surjective.comp (hq.comp f.surjective),hq⟩

/-- A fully moved nonzero binary SL₃(2) module of dimension at most six
which extends to a noninner automorphism is the natural–dual pair. -/
theorem equiv_natural_dual_of_finrank_le_six [Nontrivial M]
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hdim : Module.finrank (ZMod 2) M ≤ 6)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    Nonempty (ρ.Equiv (W.prod W.dual)) := by
  obtain ⟨p,q,hp,hq⟩ := natural_dual_quotients ρ hfull hdim α hα f hf
  let := IrreducibleCatalogue.natural_irreducible
  let := IrreducibleCatalogue.dual_irreducible
  have hs := SimpleHeadQuotient.surjective_prod_of_inequivalent_simple_quotients
    p q hp hq AutomorphismAction.natural_not_equiv_dual
  have he : Module.finrank (ZMod 2) (Vector × Module.Dual (ZMod 2) Vector) = 6 := by
    rw [Module.finrank_prod,Subspace.dual_finrank_eq]
    norm_num [Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_fin_fun]
  have hl := LinearMap.finrank_le_finrank_of_surjective (f := (p.prod q).toLinearMap) hs
  have hd : Module.finrank (ZMod 2) M =
      Module.finrank (ZMod 2) (Vector × Module.Dual (ZMod 2) Vector) := by omega
  exact ⟨(p.prod q).ofBijective
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs,hs⟩⟩

/-- Rank at most two for one involution bounds the entire nonzero module,
so an implemented outer automorphism forces the natural–dual pair. -/
theorem equiv_natural_dual_of_involution_fixedCodim_le_two [Nontrivial M]
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (a : Group) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hcodim : fixedCodim ρ (Subgroup.zpowers a) ≤ 2)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    Nonempty (ρ.Equiv (W.prod W.dual)) := by
  apply equiv_natural_dual_of_finrank_le_six ρ hfull _ α hα f hf
  have hb := ResidualFFForms.ConstituentBudget.finrank_le_three_mul_involution_fixedCodim
    ρ hfull a ha hne
  omega

/-- The highest-root displacement bound, retaining nonzero dimension. -/
theorem equiv_natural_dual_of_root_fixedCodim_le_two [Nontrivial M]
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hcodim : fixedCodim ρ (Subgroup.zpowers
      Matrix.PSL3Two.PairedGraphInputs.highestRoot) ≤ 2)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    Nonempty (ρ.Equiv (W.prod W.dual)) :=
  equiv_natural_dual_of_involution_fixedCodim_le_two ρ hfull _
    Matrix.PSL3Two.PairedGraphInputs.highestRoot_sq
    Matrix.PSL3Two.PairedGraphInputs.highestRoot_ne_one hcodim α hα f hf

/-- Intrinsic recognition for the rank-two original E.2.17 span section.
The exact displacement rank excludes the zero module. -/
theorem equiv_natural_dual_of_root_fixedCodim_eq_two
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hcodim : fixedCodim ρ (Subgroup.zpowers
      Matrix.PSL3Two.PairedGraphInputs.highestRoot) = 2)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    Nonempty (ρ.Equiv (W.prod W.dual)) := by
  have hd := fixedCodim_add_finrank ρ
    (Subgroup.zpowers Matrix.PSL3Two.PairedGraphInputs.highestRoot)
  let : Nontrivial M := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (ZMod 2) M by omega)
  exact equiv_natural_dual_of_root_fixedCodim_le_two ρ hfull hcodim.le α hα f hf

end BinaryLinearThree.RankTwoOuterRecognition
