module
public import Theory.Representation.BinaryConjugationSection.ElementaryMaximality
public import Theory.Representation.BinaryConjugationSection.FixedNormalizerFactors

/-!
# Maximal elementary factors from the marked cubic tensor section

Restrict the literal quotient coordinates to each natural plane and invert
its natural-factor embedding. This gives the exact natural-plane action
needed for cross commutator maximality, preserving the chosen factors.
Source: Aschbacher--Smith 14.3.18(4), printed p.996.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H R V : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) S₃ W) (π : H →* S₃)
    (d : BinaryConjugationSection H R V (σ.comp π))
    (hfree : ∀w,σ cubic w=w→w=0)
    (b : Module.Basis (Fin 2) (ZMod 2) (multiplicitySpace σ))

/-- The marked preimage has its actual quotient coordinates in the standard
natural plane, with the original actor map. -/
def naturalPlaneSection (i : Fin 2) :
    BinaryConjugationSection H
      (d.invariantPreimage (naturalFactorRepresentation σ hfree b π i)) V
      ((BinaryPermutation.coreRepresentation (Fin 3)).comp π) := by
  let P := naturalFactorRepresentation σ hfree b π i
  let e : NaturalPlane ≃ₗ[ZMod 2] P.toSubmodule :=
    LinearEquiv.ofInjective (naturalFactor σ hfree b i) (naturalFactor_injective σ hfree b i)
  let a := d.invariantSection P
  let f := e.symm.toAddMonoidHom.toMultiplicative.comp a.coordinates
  refine {
    section_le := a.section_le
    kernel_le := a.kernel_le
    normalized := a.normalized
    coordinates := f
    onto := ?_
    kernel_eq := ?_
    equivariant := ?_ }
  · intro v
    obtain ⟨x,hx⟩ := a.onto (Multiplicative.ofAdd (e v.toAdd))
    refine ⟨x,?_⟩
    change Multiplicative.ofAdd (e.symm (a.coordinates x).toAdd)=v
    rw [hx]
    simp
  · ext x
    change Multiplicative.ofAdd (e.symm (a.coordinates x).toAdd)=1 ↔ (x:G)∈V
    rw [←a.coordinates_eq_one_iff x]
    constructor
    · intro hx
      apply Multiplicative.toAdd.injective
      apply e.symm.injective
      simpa only [toAdd_ofAdd, toAdd_one, map_zero] using congrArg Multiplicative.toAdd hx
    · intro hx
      rw [hx]
      simp
  · intro h x
    apply e.injective
    change e (e.symm (a.coordinates ⟨(h:G)*(x:G)*(h:G)⁻¹,_⟩).toAdd)=
      e (BinaryPermutation.coreRepresentation (Fin 3) (π h) (e.symm (a.coordinates x).toAdd))
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [a.equivariant]
    change σ (π h) (a.coordinates x).toAdd.val = _
    have he := naturalFactor_equivariant σ hfree b i (π h) (e.symm (a.coordinates x).toAdd)
    have hc : naturalFactor σ hfree b i (e.symm (a.coordinates x).toAdd)=
        (a.coordinates x).toAdd.val := congrArg Subtype.val (e.apply_symm_apply (a.coordinates x).toAdd)
    rw [hc] at he
    exact he.symm

include d in
/-- Every elementary subgroup belongs to one of the two literal preimages
of the marked tensor planes. -/
theorem natural_factor_elementary_le
    [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (d.invariantPreimage (naturalFactorRepresentation σ hfree b π 0))]
    [IsElementaryAbelian 2 (d.invariantPreimage (naturalFactorRepresentation σ hfree b π 1))]
    (hπ : Function.Surjective π) (hcentral : V≤centralizer (R:Set G))
    (hn : ¬IsMulCommutative R)
    (hfixed : ∀h:H,π h=cubic→∀v∈V,(h:G)*v*(h:G)⁻¹=v→v=1)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E≤R) :
    E≤d.invariantPreimage (naturalFactorRepresentation σ hfree b π 0) ∨
      E≤d.invariantPreimage (naturalFactorRepresentation σ hfree b π 1) := by
  have hp := naturalFactorRepresentation_isCompl σ hfree b π
  exact marked_elementary_le_factor π (d.naturalPlaneSection σ π hfree b 0)
    (d.naturalPlaneSection σ π hfree b 1) hπ
    (d.invariantPreimage_inf _ _ hp.disjoint)
    (d.invariantPreimage_sup _ _ hp.sup_eq_top)
    hcentral hn hfixed E hE

variable [Finite G]
  (C : Subgroup G) (hCR : C≤R)
  (hmark : d.imageSpace C=multiplicitySpace σ)

include d hCR hmark in
/-- Involutory fixed lifts give the actual maximal elementary factors,
including normalization by the fixed-lift normalizer. -/
theorem exists_maximal_elementary_factors_of_fixed_normalizer
    (hπ : Function.Surjective π)
    (hfree : ∀ w, σ cubic w = w → w = 0)
    (hdim : Module.finrank (ZMod 2) (multiplicitySpace σ) = 2)
    (hgen : closure {x : C | x ^ 2 = 1} = ⊤)
    [IsElementaryAbelian 2 V]
    (hn : ¬IsMulCommutative R)
    (hfixed : ∀h:H,π h=cubic→∀v∈V,(h:G)*v*(h:G)⁻¹=v→v=1)
    (hVcard : Nat.card V = 4)
    (hcentral : V ≤ centralizer (R : Set G)) (hsquare : ∀ v ∈ V, v ^ 2 = 1)
    (N : Subgroup G) (hNV : N≤normalizer (V:Set G))
    (hNH : N≤normalizer (H:Set G)) (hNC : N≤centralizer (C:Set G)) :
    ∃ A B : Subgroup G,
      A ≤ R ∧ B ≤ R ∧ V ≤ A ∧ V ≤ B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ⊓ B = V ∧ A ⊔ B = R ∧ Nat.card R = 64 ∧
      H ⊔ N ≤ normalizer (A : Set G) ∧ H ⊔ N ≤ normalizer (B : Set G) ∧
      ∀E:Subgroup G,IsElementaryAbelian 2 E→E≤R→E≤A ∨ E≤B := by
  let : Finite W := Finite.of_surjective (fun x : R => (d.coordinates x).toAdd)
    (fun w => d.onto (Multiplicative.ofAdd w))
  obtain ⟨b,hb⟩ := MonoidHom.exists_basis_with_square_one_lifts
    (d.fixedCoordinates σ π C hCR hmark) (d.fixedCoordinates_surjective σ π C hCR hmark)
    hgen 2 hdim
  choose x hx hcoord using hb
  let P := naturalFactorRepresentation σ hfree b π (0 : Fin 2)
  let Q := naturalFactorRepresentation σ hfree b π (1 : Fin 2)
  let a (i : Fin 2) : R := ⟨x i,hCR (x i).property⟩
  have ha (i : Fin 2) : a i ^ 2 = 1 :=
    Subtype.ext (show (x i : G) ^ 2 = 1 from congrArg (fun y : C => (y : G)) (hx i))
  have hac (i : Fin 2) : (d.coordinates (a i)).toAdd = (b i : W) :=
    congrArg (fun y : multiplicitySpace σ => (y : W)) (hcoord i)
  have hamem (i : Fin 2) : (d.coordinates (a i)).toAdd ∈
      (naturalFactorRepresentation σ hfree b π i).toSubmodule := by
    rw [hac]
    exact ⟨naturalFactorSeed,naturalFactor_seed σ hfree b i⟩
  have hane (i : Fin 2) : d.coordinates (a i) ≠ 1 := by
    intro he
    apply b.ne_zero i
    apply Subtype.ext
    rw [← hac,he]
    rfl
  have htrans (i : Fin 2) := naturalFactorRepresentation_transitive σ hfree b π hπ i
  obtain ⟨hAP,hBQ,hAc,hBc,hinter,hjoin,hAN,hBN⟩ :=
    d.elementary_plane_pair P Q (naturalFactorRepresentation_isCompl σ hfree b π)
      (naturalFactorRepresentation_card σ hfree b π 0)
      (naturalFactorRepresentation_card σ hfree b π 1) hVcard hcentral hsquare
      (htrans 0) (htrans 1)
      (a 0) (a 1) (ha 0) (ha 1) (hamem 0) (hamem 1) (hane 0) (hane 1)
  have hAR : d.invariantPreimage P ≤ R := d.invariantPreimage_le P
  have hBR : d.invariantPreimage Q ≤ R := d.invariantPreimage_le Q
  have hRN : d.invariantPreimage Q ≤ normalizer (d.invariantPreimage P : Set G) :=
    (hBR.trans d.section_le).trans (d.invariantPreimage_normalized P)
  have hsize := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (d.invariantPreimage P) (d.invariantPreimage Q) hRN
  rw [hAc,hBc,hinter,hjoin,hVcard] at hsize
  have hnorm (i : Fin 2) : N≤normalizer
      (d.invariantPreimage (naturalFactorRepresentation σ hfree b π i):Set G) :=
    d.normalizes_invariantPreimage_of_seed _ (htrans i) (a i) (hamem i) (hane i)
      N hNV hNH (hNC.trans (centralizer_le (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        exact hz ▸ (x i).property)))
  refine ⟨d.invariantPreimage P,d.invariantPreimage Q,hAR,hBR,
    d.kernel_le_invariantPreimage P,d.kernel_le_invariantPreimage Q,
    hAP,hBQ,hAc,hBc,hinter,hjoin,by omega,
    sup_le (d.invariantPreimage_normalized P) (hnorm 0),
    sup_le (d.invariantPreimage_normalized Q) (hnorm 1),?_⟩
  intro E hEA hE
  let := hAP
  let := hBQ
  let := hEA
  exact d.natural_factor_elementary_le σ π hfree b hπ hcentral hn hfixed E hE

end Representation.BinaryConjugationSection
