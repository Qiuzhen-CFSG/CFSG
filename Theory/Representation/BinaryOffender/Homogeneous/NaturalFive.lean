module

public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
public import Theory.Representation.BinaryPermutation
public import Theory.Alternating.Aut
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Normalizer invariance of a homogeneous natural A₅ section

An automorphism of A₅ is induced by a permutation, and the natural binary
module carries the action of that permutation. Correcting conjugation by
this operator gives an equivariant isomorphism between the chosen section
and its conjugate. It descends through their literal fixed-space quotients.
Homogeneity identifies those central images and hence the original sections.

This proves invariance of the specified Irr⁺ section without assuming it,
without replacing it by its orbit, and without an ambient irreducibility
hypothesis. The actual source consumer is the chosen A₅ module in
Aschbacher–Smith 13.3.2(3), p.885, with homogeneity as in A.1.40, pp.31–32.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous

namespace Representation.BinaryOffender.Homogeneous.NaturalFive
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem same_central_images (X : Subgroup G)
    (I J : Submodule (ZMod 2) V)
    (hI : X ≤ subspaceStabilizer ρ I) (hJ : X ≤ subspaceStabilizer ρ J)
    (e : I ≃ₗ[ZMod 2] J)
    (he : ∀ (x : X) v, e ((invariantSubspace ρ X I hI).toRepresentation x v) =
      (invariantSubspace ρ X J hJ).toRepresentation x (e v)) :
    SameModule (quotientImage ρ X I hI) (quotientImage ρ X J hJ) := by
  let CI := (fixedSpace ρ X).comap I.subtype
  let CJ := (fixedSpace ρ X).comap J.subtype
  have hf : CI.map e.toLinearMap = CJ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩ x
      have hv' : (invariantSubspace ρ X I hI).toRepresentation x v = v :=
        Subtype.ext (hv x)
      exact congrArg Subtype.val ((he x v).symm.trans (congrArg e hv'))
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      intro x
      have hh : (invariantSubspace ρ X I hI).toRepresentation x (e.symm w) = e.symm w := by
        apply e.injective
        exact (he x (e.symm w)).trans (by
          rw [e.apply_symm_apply]
          exact Subtype.ext (hw x))
      exact congrArg (fun u : I => (u : V)) hh
  let qE := Submodule.Quotient.equiv CI CJ e hf
  have hq (x : X) (v : centralQuotient ρ X I) :
      qE (centralQuotientRepresentation ρ X I hI x v) =
        centralQuotientRepresentation ρ X J hJ x (qE v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change Submodule.Quotient.mk (e ((invariantSubspace ρ X I hI).toRepresentation x v)) =
        Submodule.Quotient.mk ((invariantSubspace ρ X J hJ).toRepresentation x (e v))
      exact congrArg (fun u : J => (Submodule.Quotient.mk u : J ⧸ CJ)) (he x v)
  let ei := centralQuotientImageEquiv ρ X I
  let ej := centralQuotientImageEquiv ρ X J
  let E := ei.symm.trans (qE.trans ej)
  refine ⟨E, ?_⟩
  intro x v
  obtain ⟨w, rfl⟩ := ei.surjective v
  change ej (qE (ei.symm ((quotientImage ρ X I hI).toRepresentation x (ei w)))) =
    (quotientImage ρ X J hJ).toRepresentation x (ej (qE (ei.symm (ei w))))
  rw [← centralQuotientImageEquiv_equivariant, ei.symm_apply_apply,
    ei.symm_apply_apply, hq, centralQuotientImageEquiv_equivariant]

end Representation.BinaryOffender.Homogeneous.NaturalFive

namespace Representation.BinaryOffender.Homogeneous.NaturalFive
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem homogeneous_map_eq_of_twist
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (t : T) (c : I ≃ₗ[ZMod 2] I)
    (hc : ∀ (x : X) v,
      c ((invariantSubspace ρ X I hI.invariant).toRepresentation x v) =
        (invariantSubspace ρ X I hI.invariant).toRepresentation
          (X.normalizerMonoidHom ⟨(t : G)⁻¹, hI.normalizes (T.inv_mem t.property)⟩ x) (c v)) :
    I.map (ρ t.val) = I := by
  let hJ := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  let e := c.trans (Submodule.equivMapOfInjective (ρ t.val) (ρ.apply_bijective t.val).1 I)
  apply hI.eq_of_isomorphic_conjugate ρ t
  apply same_central_images ρ X I (I.map (ρ t.val)) hI.invariant hJ.choose e
  intro x v
  apply Subtype.ext
  change ρ t.val (c ((invariantSubspace ρ X I hI.invariant).toRepresentation x v)).val =
    ρ x.val (ρ t.val (c v).val)
  rw [hc]
  change ρ t.val (ρ (X.normalizerMonoidHom
    ⟨(t : G)⁻¹, hI.normalizes (T.inv_mem t.property)⟩ x).val (c v).val) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp only [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left]

open BinaryPermutation

theorem homogeneous_natural_a5_invariant
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I)
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (F : I ≃ₗ[ZMod 2] natural (Fin 5))
    (hF : ∀ (x : X) v,
      F ((invariantSubspace ρ X I hI.invariant).toRepresentation x v) =
        naturalRepresentation (Fin 5) (e (QuotientGroup.mk' (pCore 2 X) x)).val (F v)) :
    T ≤ subspaceStabilizer ρ I := by
  intro t ht
  apply (subspace_map_eq_iff ρ I t).mp
  let n := X.normalizerMonoidHom ⟨t⁻¹, hI.normalizes (T.inv_mem ht)⟩
  let φ := MulAut.congr e (quotientAut (pCore 2 X) n)
  obtain ⟨s, hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective φ
  have hsφ (a : alternatingGroup (Fin 5)) : (φ a).val = s * a.val * s⁻¹ :=
    (congrArg (fun f : MulAut (alternatingGroup (Fin 5)) => (f a).val) hs).symm
  have ha (x : X) : (e (QuotientGroup.mk' (pCore 2 X) (n x))).val =
      s * (e (QuotientGroup.mk' (pCore 2 X) x)).val * s⁻¹ := by
    have hn : φ (e (QuotientGroup.mk' (pCore 2 X) x)) =
        e (QuotientGroup.mk' (pCore 2 X) (n x)) := by
      change e (quotientAut (pCore 2 X) n
        (e.symm (e (QuotientGroup.mk' (pCore 2 X) x)))) = _
      rw [e.symm_apply_apply, quotientAut_apply_mk]
    rw [← hn]
    exact hsφ _
  let S := LinearEquiv.ofBijective (naturalRepresentation (Fin 5) s)
    ((naturalRepresentation (Fin 5)).apply_bijective s)
  let c := F.trans (S.trans F.symm)
  have hc (v : I) : F (c v) = naturalRepresentation (Fin 5) s (F v) := by
    change F (F.symm _) = _
    rw [F.apply_symm_apply]
    rfl
  apply homogeneous_map_eq_of_twist ρ hI ⟨t, ht⟩ c
  intro x v
  apply F.injective
  have hi := (hc ((invariantSubspace ρ X I hI.invariant).toRepresentation x v)).trans
    (congrArg (naturalRepresentation (Fin 5) s) (hF x v))
  have hj := (hF (n x) (c v)).trans
    (congrArg (naturalRepresentation (Fin 5)
      (e (QuotientGroup.mk' (pCore 2 X) (n x))).val) (hc v))
  apply hi.trans
  apply Eq.trans _ hj.symm
  rw [ha]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]


end Representation.BinaryOffender.Homogeneous.NaturalFive

