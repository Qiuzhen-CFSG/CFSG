module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.Spaces
public import Theory.Representation.BinaryPermutationMulAction
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The centralizer deduction for the outer M22 quintet

A proper nonzero code subspace invariant under a maximal quintet stabilizer
has precisely that setwise stabilizer, provided the ambient representation is
irreducible. Its pointwise centralizer is then calculated using the faithful
five-point natural action on the dual cocode quotient. The proof needs both
maximality and this genuine representation marking.

This is a conditional transfer of the last paragraph of H.16.3. The source
assembly must supply maximality, irreducibility, and the quotient marking;
none of those facts is asserted here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.16.3(4), printed p.403.
-/

public section
noncomputable section
open Representation.BinaryOffender
namespace MathieuCode.M22Quintet

theorem K_le_Q : K ≤ Q := Subgroup.map_subtype_le _

theorem K_isTwoGroup : IsPGroup 2 K :=
  IsPGroup.map pCore_isPGroup Q.subtype

/-- The setwise stabilizer calculation uses ambient irreducibility in addition
to maximality; a four-dimensional invariant subspace cannot be ambient invariant. -/
theorem V4_stabilizer_eq [Representation.IsIrreducible m22OuterCodeRepresentation]
    (hmax : IsCoatom Q) (h6 : Module.finrank (ZMod 2) V6 = 6) :
    subspaceStabilizer m22OuterCodeRepresentation V4 = Q := by
  have h4 : Module.finrank (ZMod 2) V4 = 4 := by
    have h := finrank_annihilator_add V6
    change Module.finrank (ZMod 2) V4 + _ = 10 at h
    omega
  have hle : Q ≤ subspaceStabilizer m22OuterCodeRepresentation V4 :=
    le_subspaceStabilizer _ _ (fun g hg v hv => V4_invariant ⟨g, hg⟩ v hv)
  apply (hmax.ne_top_iff_eq hle).mp
  intro htop
  let W : Subrepresentation m22OuterCodeRepresentation :=
    { toSubmodule := V4
      apply_mem_toSubmodule g v hv := by
        have hg : g ∈ subspaceStabilizer m22OuterCodeRepresentation V4 := by rw [htop]; trivial
        exact (hg v).mpr hv }
  rcases (inferInstance : Representation.IsIrreducible
    m22OuterCodeRepresentation).eq_bot_or_eq_top W with hW | hW
  · have he : V4 = ⊥ := congrArg Subrepresentation.toSubmodule hW
    rw [he, finrank_bot] at h4
    omega
  · have he : V4 = ⊤ := congrArg Subrepresentation.toSubmodule hW
    rw [he, finrank_top, finrank_m22Code] at h4
    omega

variable (q : Q →* Equiv.Perm (Fin 5))
  (e : (M22Cocode ⧸ V6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
  (he : ∀ (g : Q) v, e (V6Subrepresentation.quotientRepresentation g v) =
    BinaryPermutation.naturalRepresentation (Fin 5) (q g) (e v))

include e he

/-- A marking with the actual five-point natural module detects the entire
quotient action kernel, rather than merely giving its order. -/
theorem quotient_trivial_iff (g : Q) :
    (∀ u, m22OuterCocodeRepresentation g.val u - u ∈ V6) ↔ q g = 1 := by
  constructor
  · intro hg
    have hact (v : M22Cocode ⧸ V6) : V6Subrepresentation.quotientRepresentation g v = v := by
      induction v using Submodule.Quotient.induction_on with
      | _ u =>
        change V6.mkQ (m22OuterCocodeRepresentation g.val u) = V6.mkQ u
        apply sub_eq_zero.mp
        rw [← map_sub]
        exact (Submodule.Quotient.mk_eq_zero V6).mpr (hg u)
    apply BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)
    rw [map_one]
    apply MulEquiv.ext
    intro v
    obtain ⟨w, hw⟩ := e.surjective v.toAdd
    have h := he g w
    rw [hact, hw] at h
    exact congrArg Multiplicative.ofAdd h.symm
  · intro hg u
    have hact : V6Subrepresentation.quotientRepresentation g (V6.mkQ u) = V6.mkQ u := by
      apply e.injective
      exact (he g _).trans (by rw [hg, map_one, Module.End.one_apply])
    apply (Submodule.Quotient.mk_eq_zero V6).mp
    change V6.mkQ (m22OuterCocodeRepresentation g.val u - u) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hact

/-- With the actual quotient marking, the ambient pointwise centralizer is
the intrinsic two-core. This is the faithful-action step missing from an
argument based on maximality alone. -/
theorem V4_centralizer_eq_of_natural_quotient
    (hstab : subspaceStabilizer m22OuterCodeRepresentation V4 = Q)
    (hker : q.ker = K.subgroupOf Q) :
    subspaceKernel m22OuterCodeRepresentation V4 ⊤ = K := by
  ext g
  constructor
  · rintro ⟨_, hg⟩
    have hgQ : g ∈ Q := by
      rw [← hstab]
      intro v
      constructor
      · intro hv
        have heq := hg _ hv
        have heq' := (Representation.apply_bijective m22OuterCodeRepresentation g).injective heq
        rwa [heq'] at hv
      · intro hv
        rw [hg v hv]
        exact hv
    have htr := (fixes_annihilator_iff V6 g).mp hg
    have hq := (quotient_trivial_iff q e he ⟨g, hgQ⟩).mp htr
    have hk : (⟨g, hgQ⟩ : Q) ∈ q.ker := hq
    rw [hker] at hk
    exact hk
  · intro hg
    refine ⟨Subgroup.mem_top g, ?_⟩
    apply (fixes_annihilator_iff V6 g).mpr
    apply (quotient_trivial_iff q e he ⟨g, K_le_Q hg⟩).mpr
    have hk : (⟨g, K_le_Q hg⟩ : Q) ∈ K.subgroupOf Q := hg
    rw [← hker] at hk
    exact hk

/-- Maximality supplies the setwise stabilizer when combined with ambient
irreducibility. The natural quotient marking supplies its pointwise kernel. -/
theorem V4_centralizer_eq_of_maximal_natural_quotient
    [Representation.IsIrreducible m22OuterCodeRepresentation]
    (hmax : IsCoatom Q) (h6 : Module.finrank (ZMod 2) V6 = 6)
    (hker : q.ker = K.subgroupOf Q) :
    subspaceKernel m22OuterCodeRepresentation V4 ⊤ = K :=
  V4_centralizer_eq_of_natural_quotient q e he (V4_stabilizer_eq hmax h6) hker

end MathieuCode.M22Quintet
