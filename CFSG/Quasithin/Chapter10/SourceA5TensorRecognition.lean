module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Model
public import Theory.Representation.OrthogonalFourPlusMatrix.TensorRecognition
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.Representation.BinaryConjugationSection.Irreducible
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality
public import Theory.Representation.CommutingCubicCentralCover

/-!
# The determinant recognition consumer for the original A₅ tensor branch

Apply the proved cubic-free product classification to an actual binary
conjugation section of the full source module. Its determinant coordinates
retain the literal L₀ projection, its intrinsic two-core kernel, and the
original A₅ first-factor marking. This produces the exact model consumed by
the specialized tensor exclusion.

The source inputs still to be established are the marked product projection,
the actual central cover, and cubic fixed-point-freeness in the two factors.
Seed minimality proves irreducibility, and commuting cubic trace splits the
central cover. In D.3.7 cubic fixed-point-freeness comes from the cubic-ratio
bound excluding the deleted tensor alternative; it is not a consequence of
the abstract A₅ × A₅ quotient alone.

Source: Aschbacher–Smith D.3.7 and 3.2.6(1), printed pp.197–199,581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.QuadraticFourGroup Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) W] in
private theorem full_section_irreducible
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hseed : D.seed = D.fullModule)
    (q : (localOrbit T L) →* Factor 2 × Factor 2) (hq : Function.Surjective q)
    (σ : Representation (ZMod 2) (Factor 2 × Factor 2) W)
    (hfree : CubicFreeOnFactors σ)
    (s : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥ (σ.comp q)) :
    σ.IsIrreducible := by
  have hs : Function.Injective s.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [s.kernel_eq,bot_subgroupOf]
  let : Nontrivial D.fullModule := (nontrivial_iff_ne_bot _).mpr (by
    rw [← hseed]
    exact D.seed_ne_bot)
  have : Nontrivial W := by
    by_contra h
    let : Subsingleton W := not_nontrivial_iff_subsingleton.mp h
    let : Subsingleton D.fullModule := Function.Injective.subsingleton hs
    exact false_of_nontrivial_of_subsingleton D.fullModule
  apply (Representation.irreducible_comp_surjective_iff q hq σ).mp
  apply s.irreducible_of_subgroup_minimal
  intro J hJV hOJ
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer
      (localJoin T L) (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus J
      (by change J ≤ D.seed; rw [hseed]; exact hJV) hOJ with he | hc
  · exact Or.inl (he.trans hseed)
  · right
    intro x hx
    obtain ⟨a,ha⟩ := hq (cubicElement 2,1)
    let v : D.fullModule := ⟨x,hJV hx⟩
    have hc' : (a : G) * x * (a : G)⁻¹ = x := by
      rw [hc hx a a.property,mul_inv_cancel_right]
    have hv := s.equivariant a v
    have heq : (⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalized a.property) x).mp v.property⟩ : D.fullModule) = v :=
      Subtype.ext hc'
    change (s.coordinates _).toAdd = σ (q a) (s.coordinates v).toAdd at hv
    rw [heq,ha] at hv
    have hz := hfree.1 (cubicElement 2) (cubicElement_order 2) _ hv.symm
    exact (s.coordinates_eq_one_iff v).mp hz

/-- An irreducible cubic-free original product section supplies the literal
determinant model. No tensor equivalence or model action is assumed. -/
theorem source_a5_tensor_model_of_cubic_free_product
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hminimal : D.IsMinimalFullModule)
    (hseed : D.seed = D.fullModule) (hmodule : D.moduleSubgroup = D.fullModule)
    (q : (localOrbit T L) →* Factor 2 × Factor 2)
    (hq : Function.Surjective q) (hker : q.ker = pCore 2 (localOrbit T L))
    (j : alternatingGroup (Fin 5) ≃* Factor 2)
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
      (j (e (QuotientGroup.mk' (pCore 2 L) l)),1))
    (σ : Representation (ZMod 2) (Factor 2 × Factor 2) W)
    (hfree : CubicFreeOnFactors σ)
    (s : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥ (σ.comp q)) :
    Nonempty (SourceA5TensorModel D e) := by
  let : σ.IsIrreducible := full_section_irreducible D hseed q hq σ hfree s
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Factor 2) :=
    Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
  obtain ⟨j₁,j₂,⟨a⟩⟩ :=
    ClassicalOrthogonal.FourPlusMatrix.TensorRecognition.exists_binary_determinant_equiv σ hfree
  let p := j₁.prodCongr j₂
  refine ⟨{
    minimal := hminimal
    seed_eq := hseed
    module_eq := hmodule
    quotient := p.toMonoidHom.comp q
    onto := p.surjective.comp hq
    kernel_eq := ?_
    firstMarking := j.trans j₁
    first_factor := ?_
    sectionData := s.relabel q a }⟩
  · rw [MonoidHom.ker_comp_of_injective q p.toMonoidHom p.injective,hker]
  · intro l
    change p (q ⟨l,le_componentOrbit L T l.property⟩) = _
    rw [hfirst]
    exact Prod.ext rfl j₂.map_one

/-- A cubic-free central quotient suffices: commuting cubic trace eliminates
the fixed kernel, and seed minimality proves irreducibility of that quotient. -/
theorem source_a5_tensor_model_of_cubic_free_cover
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hminimal : D.IsMinimalFullModule)
    (hseed : D.seed = D.fullModule) (hmodule : D.moduleSubgroup = D.fullModule)
    (q : (localOrbit T L) →* Factor 2 × Factor 2)
    (hq : Function.Surjective q) (hker : q.ker = pCore 2 (localOrbit T L))
    (j : alternatingGroup (Fin 5) ≃* Factor 2)
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
      (j (e (QuotientGroup.mk' (pCore 2 L) l)),1))
    (τ : Representation (ZMod 2) (Factor 2 × Factor 2) U)
    (σ : Representation (ZMod 2) (Factor 2 × Factor 2) W)
    (p : τ.IntertwiningMap σ) (hp : OneCohomology.IsCover p)
    (hfree : CubicFreeOnFactors σ)
    (s : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥ (τ.comp q)) :
    Nonempty (SourceA5TensorModel D e) := by
  have hi : Function.Injective p :=
    OneCohomology.injective_of_cover_product_cubics p hp (cubicElement 2)
      (by rw [← cubicElement_order 2]; exact pow_orderOf_eq_one _)
      (cubicElement 2)
      (hfree.1 _ (cubicElement_order 2)) (hfree.2 _ (cubicElement_order 2))
  let a : τ.Equiv σ := Representation.Equiv.mk
    (LinearEquiv.ofBijective p.toLinearMap ⟨hi,hp.1⟩) p.isIntertwining'
  exact source_a5_tensor_model_of_cubic_free_product D e hminimal hseed hmodule
    q hq hker j hfirst σ hfree (s.relabel q a)

end CFSG.Quasithin.Chapter10
