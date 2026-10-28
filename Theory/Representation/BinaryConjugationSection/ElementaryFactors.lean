module

public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.Representation.InvertedCubicTensor.NaturalFactors
public import Theory.GroupTheory.InvolutionGeneratedBasis
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Elementary factors of a doubled natural symmetric-three section

The specified fixed subgroup supplies an involutory basis of the multiplicity
space. The corresponding natural planes have elementary full preimages.
The two preimages have order sixteen, meet in the original kernel of order
four, generate the original group of order sixty-four, and are normalized
by the original actor. Any group centralizing the section normalizes both.

Source: Aschbacher–Smith 14.3.18(4), printed p.996. The action, quotient
kernel, fixed subgroup and involution-generation mark are all retained.
-/

@[expose] public section
noncomputable section
open Subgroup InvertedCubicTensor

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G] {H R V : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) S₃ W) (π : H →* S₃)
  (d : BinaryConjugationSection H R V (σ.comp π))
  (C : Subgroup G) (hCR : C ≤ R)
  (hmark : d.imageSpace C = multiplicitySpace σ)

def fixedCoordinates : C →* Multiplicative (multiplicitySpace σ) where
  toFun x := Multiplicative.ofAdd
    ⟨(d.coordinates ⟨x,hCR x.property⟩).toAdd, by
      rw [← hmark]
      exact (d.mem_imageSpace_iff C _).mpr ⟨⟨x,hCR x.property⟩,x.property,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one d.coordinates)
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul d.coordinates
      ⟨x,hCR x.property⟩ ⟨y,hCR y.property⟩)

omit [Finite G] in
theorem fixedCoordinates_surjective : Function.Surjective (d.fixedCoordinates σ π C hCR hmark) := by
  intro w
  have hw : w.toAdd.val ∈ d.imageSpace C := hmark.symm ▸ w.toAdd.property
  obtain ⟨x,hx,he⟩ := (d.mem_imageSpace_iff C _).mp hw
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

omit [Finite G] in
theorem normalizes_invariantPreimage_of_commutator (P : Subrepresentation (σ.comp π))
    (Q : Subgroup G) (hQ : ⁅R,Q⁆ ≤ V) : Q ≤ normalizer (d.invariantPreimage P : Set G) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  rw [commutator_comm]
  exact (commutator_mono (d.invariantPreimage_le P) le_rfl).trans
    (hQ.trans (d.kernel_le_invariantPreimage P))

include d hCR hmark in
/-- The two original elementary factors are constructed from the marked
fixed subgroup; neither factor nor a block classification is assumed. -/
theorem exists_elementary_factors
    (hπ : Function.Surjective π)
    (hfree : ∀ w, σ cubic w = w → w = 0)
    (hdim : Module.finrank (ZMod 2) (multiplicitySpace σ) = 2)
    (hgen : closure {x : C | x ^ 2 = 1} = ⊤)
    (hVcard : Nat.card V = 4)
    (hcentral : V ≤ centralizer (R : Set G)) (hsquare : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ A B : Subgroup G,
      A ≤ R ∧ B ≤ R ∧ V ≤ A ∧ V ≤ B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ⊓ B = V ∧ A ⊔ B = R ∧ Nat.card R = 64 ∧
      H ≤ normalizer (A : Set G) ∧ H ≤ normalizer (B : Set G) ∧
      ∀ Q : Subgroup G, ⁅R,Q⁆ ≤ V →
        Q ≤ normalizer (A : Set G) ∧ Q ≤ normalizer (B : Set G) := by
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
  obtain ⟨hAP,hBQ,hAc,hBc,hinter,hjoin,hAN,hBN⟩ :=
    d.elementary_plane_pair P Q (naturalFactorRepresentation_isCompl σ hfree b π)
      (naturalFactorRepresentation_card σ hfree b π 0)
      (naturalFactorRepresentation_card σ hfree b π 1) hVcard hcentral hsquare
      (naturalFactorRepresentation_transitive σ hfree b π hπ 0)
      (naturalFactorRepresentation_transitive σ hfree b π hπ 1)
      (a 0) (a 1) (ha 0) (ha 1) (hamem 0) (hamem 1) (hane 0) (hane 1)
  have hAR : d.invariantPreimage P ≤ R := d.invariantPreimage_le P
  have hBR : d.invariantPreimage Q ≤ R := d.invariantPreimage_le Q
  have hRN : d.invariantPreimage Q ≤ normalizer (d.invariantPreimage P : Set G) :=
    (hBR.trans d.section_le).trans (d.invariantPreimage_normalized P)
  have hsize := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (d.invariantPreimage P) (d.invariantPreimage Q) hRN
  rw [hAc,hBc,hinter,hjoin,hVcard] at hsize
  refine ⟨d.invariantPreimage P,d.invariantPreimage Q,hAR,hBR,
    d.kernel_le_invariantPreimage P,d.kernel_le_invariantPreimage Q,
    hAP,hBQ,hAc,hBc,hinter,hjoin,by omega,
    d.invariantPreimage_normalized P,d.invariantPreimage_normalized Q,?_⟩
  intro N hN
  exact ⟨d.normalizes_invariantPreimage_of_commutator σ π P N hN,
    d.normalizes_invariantPreimage_of_commutator σ π Q N hN⟩

end Representation.BinaryConjugationSection
