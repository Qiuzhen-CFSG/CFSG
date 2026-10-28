module
public import Theory.Representation.BinaryConjugationSection.ElementaryFactors
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# Natural factors preserved by the fixed-lift normalizer

A transitive natural plane has full preimage equal to the orbit span of the
kernel and one nonzero lift. Two fixed involutory lifts therefore construct
the elementary factors and prove their normalization by every actor preserving
the kernel and conjugators and centralizing the fixed subgroup.

Source: Aschbacher--Smith 14.3.18(4), printed p.996. This uses the actual
section and avoids assuming that the auxiliary actor centralizes its quotient.
-/

@[expose] public section
noncomputable section
open Subgroup InvertedCubicTensor

namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H R V : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H R V ρ)

/-- A transitive invariant plane pulls back to the span of the kernel and
any one lift of a nonzero coordinate. -/
theorem invariantPreimage_eq_conjugateSpan (P : Subrepresentation ρ)
    (htrans : ∀ u v : P.toSubmodule, u ≠ 0 → v ≠ 0 →
      ∃ h : H, P.toRepresentation h u = v)
    (a : R) (haP : (d.coordinates a).toAdd ∈ P.toSubmodule)
    (haV : d.coordinates a ≠ 1) :
    d.invariantPreimage P = conjugateSpanBy (V ⊔ zpowers (a : G)) H := by
  have haA : (a : G) ∈ d.invariantPreimage P :=
    (d.mem_invariantPreimage P a).mpr ⟨a.property,haP⟩
  have hseed : V ⊔ zpowers (a : G) ≤ d.invariantPreimage P :=
    sup_le (d.kernel_le_invariantPreimage P) (zpowers_le.mpr haA)
  have hspan : conjugateSpanBy (V ⊔ zpowers (a : G)) H ≤ d.invariantPreimage P :=
    conjugateSpanBy_le hseed (d.invariantPreimage_normalized P)
  apply le_antisymm ?_ hspan
  intro x hx
  obtain ⟨hxR,hxP⟩ := (d.mem_invariantPreimage P x).mp hx
  by_cases hxV : d.coordinates ⟨x,hxR⟩ = 1
  · exact le_conjugateSpanBy _ _
      ((show V≤V⊔zpowers (a:G) from le_sup_left) ((d.coordinates_eq_one_iff ⟨x,hxR⟩).mp hxV))
  let u : P.toSubmodule := ⟨(d.coordinates a).toAdd,haP⟩
  let v : P.toSubmodule := ⟨(d.coordinates ⟨x,hxR⟩).toAdd,hxP⟩
  have hu : u ≠ 0 := fun he => haV (congrArg (fun z : P.toSubmodule =>
    Multiplicative.ofAdd (z : W)) he)
  have hv : v ≠ 0 := fun he => hxV (congrArg (fun z : P.toSubmodule =>
    Multiplicative.ofAdd (z : W)) he)
  obtain ⟨h,hh⟩ := htrans u v hu hv
  let b : R := ⟨(h:G)*(a:G)*(h:G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized h.property) a).mp a.property⟩
  have hb : d.coordinates b=d.coordinates ⟨x,hxR⟩ :=
    Multiplicative.toAdd.injective ((d.equivariant h a).trans
      (congrArg (fun z : P.toSubmodule => (z:W)) hh))
  have hk : ((b⁻¹*⟨x,hxR⟩:R):G) ∈ V := by
    apply (d.coordinates_eq_one_iff _).mp
    rw [map_mul,map_inv,hb,inv_mul_cancel]
  have hbspan : (b:G)∈conjugateSpanBy (V ⊔ zpowers (a:G)) H :=
    subset_closure ⟨h,h.property,a,(show zpowers (a:G)≤V⊔zpowers (a:G) from le_sup_right) (mem_zpowers _),rfl⟩
  have hkspan : ((b⁻¹*⟨x,hxR⟩:R):G)∈conjugateSpanBy (V ⊔ zpowers (a:G)) H :=
    le_conjugateSpanBy _ _ ((show V≤V⊔zpowers (a:G) from le_sup_left) hk)
  have hm := (conjugateSpanBy (V ⊔ zpowers (a:G)) H).mul_mem hbspan hkspan
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hm

/-- Normalizing the orbit seed and the actor normalizes its full preimage. -/
theorem normalizes_invariantPreimage_of_seed (P : Subrepresentation ρ)
    (htrans : ∀ u v : P.toSubmodule, u ≠ 0 → v ≠ 0 →
      ∃ h : H, P.toRepresentation h u = v)
    (a : R) (haP : (d.coordinates a).toAdd ∈ P.toSubmodule)
    (haV : d.coordinates a ≠ 1)
    (N : Subgroup G) (hNV : N≤normalizer (V:Set G))
    (hNH : N≤normalizer (H:Set G)) (hNa : N≤centralizer ({(a:G)}:Set G)) :
    N≤normalizer (d.invariantPreimage P:Set G) := by
  rw [d.invariantPreimage_eq_conjugateSpan P htrans a haP haV]
  apply normalizes_conjugateSpanBy _ _ _ ?_ hNH
  apply (le_inf hNV ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hc : centralizer ({(a:G)}:Set G)=centralizer (zpowers (a:G):Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  exact (hNa.trans hc.le).trans (centralizer_le_normalizer _)

variable [Finite G]
  (σ : Representation (ZMod 2) S₃ W) (π : H →* S₃)
  (c : BinaryConjugationSection H R V (σ.comp π))
  (C : Subgroup G) (hCR : C ≤ R)
  (hmark : c.imageSpace C = multiplicitySpace σ)

include c hCR hmark in
/-- The actual fixed-space lifts construct two factors preserved by every
actor normalizing the kernel and conjugators and centralizing the lifts. -/
theorem exists_elementary_factors_of_fixed_normalizer
    (hπ : Function.Surjective π)
    (hfree : ∀ w, σ cubic w = w → w = 0)
    (hdim : Module.finrank (ZMod 2) (multiplicitySpace σ) = 2)
    (hgen : closure {x : C | x ^ 2 = 1} = ⊤)
    (hVcard : Nat.card V = 4)
    (hcentral : V ≤ centralizer (R : Set G)) (hsquare : ∀ v ∈ V, v ^ 2 = 1)
    (N : Subgroup G) (hNV : N≤normalizer (V:Set G))
    (hNH : N≤normalizer (H:Set G)) (hNC : N≤centralizer (C:Set G)) :
    ∃ A B : Subgroup G,
      A ≤ R ∧ B ≤ R ∧ V ≤ A ∧ V ≤ B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ⊓ B = V ∧ A ⊔ B = R ∧ Nat.card R = 64 ∧
      H ⊔ N ≤ normalizer (A : Set G) ∧ H ⊔ N ≤ normalizer (B : Set G) := by
  let : Finite W := Finite.of_surjective (fun x : R => (c.coordinates x).toAdd)
    (fun w => c.onto (Multiplicative.ofAdd w))
  obtain ⟨b,hb⟩ := MonoidHom.exists_basis_with_square_one_lifts
    (c.fixedCoordinates σ π C hCR hmark) (c.fixedCoordinates_surjective σ π C hCR hmark)
    hgen 2 hdim
  choose x hx hcoord using hb
  let P := naturalFactorRepresentation σ hfree b π (0 : Fin 2)
  let Q := naturalFactorRepresentation σ hfree b π (1 : Fin 2)
  let a (i : Fin 2) : R := ⟨x i,hCR (x i).property⟩
  have ha (i : Fin 2) : a i ^ 2 = 1 :=
    Subtype.ext (show (x i : G) ^ 2 = 1 from congrArg (fun y : C => (y : G)) (hx i))
  have hac (i : Fin 2) : (c.coordinates (a i)).toAdd = (b i : W) :=
    congrArg (fun y : multiplicitySpace σ => (y : W)) (hcoord i)
  have hamem (i : Fin 2) : (c.coordinates (a i)).toAdd ∈
      (naturalFactorRepresentation σ hfree b π i).toSubmodule := by
    rw [hac]
    exact ⟨naturalFactorSeed,naturalFactor_seed σ hfree b i⟩
  have hane (i : Fin 2) : c.coordinates (a i) ≠ 1 := by
    intro he
    apply b.ne_zero i
    apply Subtype.ext
    rw [← hac,he]
    rfl
  have htrans (i : Fin 2) := naturalFactorRepresentation_transitive σ hfree b π hπ i
  obtain ⟨hAP,hBQ,hAc,hBc,hinter,hjoin,hAN,hBN⟩ :=
    c.elementary_plane_pair P Q (naturalFactorRepresentation_isCompl σ hfree b π)
      (naturalFactorRepresentation_card σ hfree b π 0)
      (naturalFactorRepresentation_card σ hfree b π 1) hVcard hcentral hsquare
      (htrans 0) (htrans 1)
      (a 0) (a 1) (ha 0) (ha 1) (hamem 0) (hamem 1) (hane 0) (hane 1)
  have hAR : c.invariantPreimage P ≤ R := c.invariantPreimage_le P
  have hBR : c.invariantPreimage Q ≤ R := c.invariantPreimage_le Q
  have hRN : c.invariantPreimage Q ≤ normalizer (c.invariantPreimage P : Set G) :=
    (hBR.trans c.section_le).trans (c.invariantPreimage_normalized P)
  have hsize := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (c.invariantPreimage P) (c.invariantPreimage Q) hRN
  rw [hAc,hBc,hinter,hjoin,hVcard] at hsize
  have hnorm (i : Fin 2) : N≤normalizer
      (c.invariantPreimage (naturalFactorRepresentation σ hfree b π i):Set G) :=
    c.normalizes_invariantPreimage_of_seed _ (htrans i) (a i) (hamem i) (hane i)
      N hNV hNH (hNC.trans (centralizer_le (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        exact hz ▸ (x i).property)))
  exact ⟨c.invariantPreimage P,c.invariantPreimage Q,hAR,hBR,
    c.kernel_le_invariantPreimage P,c.kernel_le_invariantPreimage Q,
    hAP,hBQ,hAc,hBc,hinter,hjoin,by omega,
    sup_le (c.invariantPreimage_normalized P) (hnorm 0),
    sup_le (c.invariantPreimage_normalized Q) (hnorm 1)⟩

end Representation.BinaryConjugationSection
