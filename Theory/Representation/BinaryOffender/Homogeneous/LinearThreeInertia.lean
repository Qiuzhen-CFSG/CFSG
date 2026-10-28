module
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeOrbit
public import Theory.Representation.BinaryOffender.LinearThreeCentralCover
public import Theory.Representation.BinaryNaturalAutomorphisms

/-!
# Exact inertia of a natural binary-three central cover

A normalizing operator on a seed induces an operator on its actual central
quotient. Every linear automorphism of the natural binary three-space is
a special-linear matrix, so the induced component automorphism is inner.
Conversely, homogeneous uniqueness lifts an inner intertwiner to stability
of the original seed. Thus inertia is exactly the inverse image of the
inner automorphisms, even for a nonsplit four-dimensional cover.

Source: Aschbacher--Smith A.1.40--42 and14.6.22, printed pp.31--32 and1038.
The terminal source application retains both the original quotient action
and its coordinate preimages.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.OneCohomology
namespace Representation.BinaryOffender.Homogeneous

private theorem automorphism_inner_of_operator {D E : Type*} [Group D]
    [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) D E) (hf : Function.Injective σ)
    (α : MulAut D) (c : E ≃ₗ[ZMod 2] E)
    (hc : ∀ g v, c (σ g v) = σ (α g) (c v))
    (g : D) (hg : ∀ v, c v = σ g v) : α = MulAut.conj g := by
  apply MulEquiv.ext
  intro x
  apply hf
  apply LinearMap.ext
  intro v
  have hh := hc x (σ g⁻¹ v)
  rw [hg,hg] at hh
  change σ (α x) v = σ (g*x*g⁻¹) v
  simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply,mul_assoc]
    using hh.symm

private theorem natural_intertwiner_inner (α : MulAut BinaryLinearThree.Group)
    (c : BinaryLinearThree.Vector ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (hc : ∀ g v, c (BinaryLinearThree.W g v) = BinaryLinearThree.W (α g) (c v)) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨g,hg⟩ := specialLinearNatural_binary_full 3 c.toAddEquiv.toMultiplicative
  refine ⟨g,automorphism_inner_of_operator BinaryLinearThree.W
    (specialLinearNatural_injective 3) α c hc g ?_⟩
  intro v
  exact (hg (Multiplicative.ofAdd v)).symm

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K T : Subgroup G}
    {I : Submodule (ZMod 2) V}

/-- Stabilizing a seed with a natural binary-three central quotient induces
an inner automorphism on its component; the covering kernel is retained. -/
theorem IsIrrPlusWith.inner_of_natural_map_eq
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v))
    (ht : I.map (ρ t.val) = I) :
    ∃ k : K, K.normalizerMonoidHom ⟨t,hI.normalizes t.property⟩ = MulAut.conj k := by
  let S := quotientImage ρ K I hI.invariant
  let σ := S.toRepresentation
  let θ := normalizerQuotientRepresentation ρ K
  let tN : normalizer (K : Set G) := ⟨t,hI.normalizes t.property⟩
  let n := K.normalizerMonoidHom tN
  have hS : S.toSubmodule.map (θ tN) = S.toSubmodule := by
    change (I.map (fixedSpace ρ K).mkQ).map (normalizerQuotientRepresentation ρ K tN) =
      I.map (fixedSpace ρ K).mkQ
    rw [←quotientImage_map_normalizer ρ K I tN]
    exact congrArg (Submodule.map (fixedSpace ρ K).mkQ) ht
  let a := (Submodule.equivMapOfInjective (θ tN) (θ.apply_bijective tN).1 S.toSubmodule).trans
    (LinearEquiv.ofEq _ _ hS)
  have ha (v : S.toSubmodule) : (a v : V ⧸ fixedSpace ρ K) = θ tN v := rfl
  have hcomm (k : K) (w : V ⧸ fixedSpace ρ K) :
      θ tN (fixedQuotientRepresentation ρ K k w) =
        fixedQuotientRepresentation ρ K (n k) (θ tN w) := by
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
      change (fixedSpace ρ K).mkQ (ρ t.val (ρ k.val w)) =
        (fixedSpace ρ K).mkQ (ρ (n k).val (ρ t.val w))
      simp only [n,Subgroup.normalizerMonoidHom_apply_apply_coe,tN,
        ←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have heq (k : K) (v : S.toSubmodule) : a (σ k v) = σ (n k) (a v) := by
    apply Subtype.ext
    change (a (σ k v)).val = fixedQuotientRepresentation ρ K (n k) (a v).val
    rw [ha,ha]
    exact hcomm k v.val
  let q := centralQuotientImageEquiv ρ K I
  let b : S.toSubmodule ≃ₗ[ZMod 2] BinaryLinearThree.Vector := q.symm.trans l
  have hb (k : K) (v : S.toSubmodule) : b (σ k v) = BinaryLinearThree.W (j k) (b v) := by
    obtain ⟨w,rfl⟩ := q.surjective v
    rw [←centralQuotientImageEquiv_equivariant ρ K I hI.invariant]
    change l (q.symm (q (centralQuotientRepresentation ρ K I hI.invariant k w))) =
      BinaryLinearThree.W (j k) (l (q.symm (q w)))
    simpa only [q.symm_apply_apply] using he k w
  let α := (MulAut.congr j) n
  let c := b.symm.trans (a.trans b)
  have hc (g : BinaryLinearThree.Group) (v : BinaryLinearThree.Vector) :
      c (BinaryLinearThree.W g v) = BinaryLinearThree.W (α g) (c v) := by
    obtain ⟨k,rfl⟩ := j.surjective g
    obtain ⟨w,rfl⟩ := b.surjective v
    change b (a (b.symm (BinaryLinearThree.W (j k) (b w)))) =
      BinaryLinearThree.W (α (j k)) (b (a (b.symm (b w))))
    rw [←hb,b.symm_apply_apply,b.symm_apply_apply,heq,hb]
    congr 2
    simp only [α,MulAut.congr_apply,MulEquiv.trans_apply,j.symm_apply_apply]
  obtain ⟨g,hg⟩ := natural_intertwiner_inner α c hc
  refine ⟨j.symm g,?_⟩
  apply (MulAut.congr j).injective
  change α = (MulAut.congr j) (MulAut.conj (j.symm g))
  rw [hg]
  apply MulEquiv.ext
  intro x
  simp [MulAut.congr_apply,MulAut.conj_apply]

/-- The inertia subgroup is exactly the preimage of the inner component
automorphisms, on the same marked natural central quotient. -/
theorem IsIrrPlusWith.natural_map_eq_iff_inner
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* BinaryLinearThree.Group)
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryLinearThree.W (j k) (l v)) :
    I.map (ρ t.val) = I ↔
      ∃ k : K, K.normalizerMonoidHom ⟨t,hI.normalizes t.property⟩ = MulAut.conj k :=
  ⟨hI.inner_of_natural_map_eq ρ t j l he,fun ⟨k,hk⟩ => hI.map_eq_of_inner ρ t k hk⟩

end Representation.BinaryOffender.Homogeneous
