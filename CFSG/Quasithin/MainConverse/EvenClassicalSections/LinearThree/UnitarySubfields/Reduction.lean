module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Binary
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.WholeQuotients
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Basic

/-!
# Subfield induction for PSU₃ over even fields

The envelope below consists of solvable groups, the already calculated
rank-one and small exceptional groups, proper unitary subfield models,
and explicit injections, quotients and normal extensions. Linear
parabolics also have independently proved section theorems, so they can
handle reducible unitary subgroups over the same matrix field. All leaves
are actual groups, with isomorphisms in the model predicates.

The central SU cover and the determinant quotient of GU account for PGU
without assuming a splitting. Strong induction uses the fixed-field
exponent; in the unitary sign, a subfield exponent divides it with odd
quotient. The binary endpoint is solvable, and WholeQuotients handles
simple quotients of each whole larger model.

The remaining input is an intrinsic exhaustion of proper subgroups.
This file does not assert it. In particular, the embedding of PSU₃(2ⁿ)
into PSL₃(2^(2n)) is not used to establish a recursive K hypothesis.
Sources: Hartley–Mitchell, GLS3 Theorem 6.5.3(a–i), specialized to the
unitary sign and characteristic two; Aschbacher–Smith 0.1.1(K).
The shortened GLS proof assumes ambient K and cannot supply this input.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections

open CFSG.KnownSimple Matrix
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped MatrixGroups

/-- Concrete overgroups and normal layers sufficient for the section argument.
This definition asserts no subgroup-exhaustion theorem. -/
public inductive Envelope (n : ℕ) : (H : Type) → [Group H] → Prop where
  | solvable (H : Type) [Group H] (hH : Group.IsSolvable H) : Envelope n H
  | linearTwo (H : Type) [Group H] (q : ℕ)
      (hH : ClassicalGroup.IsPSL H 2 q) : Envelope n H
  | generalLinearTwo (F : Type) [Field F] [Finite F] : Envelope n (GL (Fin 2) F)
  | binaryThree (H : Type) [Group H]
      (hH : ClassicalGroup.IsPSL H 3 2) : Envelope n H
  | alternatingSix : Envelope n (alternatingGroup (Fin 6))
  | pointParabolic (F : Type) [Field F] [Finite F] :
      Envelope n (PSL3.LinearThree.pointParabolic F)
  | lineParabolic (F : Type) [Field F] [Finite F] :
      Envelope n (PSL3.LinearThree.lineParabolic F)
  | unitarySubfield (H : Type) [Group H] (m : ℕ) (hm : 0 < m) (hmn : m < n)
      (hdiv : m ∣ n) (hodd : Odd (n / m))
      (hH : ClassicalGroup.IsPSU H 3 (2 ^ m)) : Envelope n H
  | subgroup {H L : Type} [Group H] [Group L] (i : H →* L)
      (hi : Function.Injective i) (hL : Envelope n L) : Envelope n H
  | quotient {H L : Type} [Group H] [Group L] (p : L →* H)
      (hp : Function.Surjective p) (hL : Envelope n L) : Envelope n H
  | extension {H : Type} [Group H] (N : Subgroup H) [N.Normal]
      (hN : Envelope n N) (hQ : Envelope n (H ⧸ N)) : Envelope n H

/-- A solvable kernel contributes only prime-cyclic simple sections. -/
public theorem Envelope.of_solvable_kernel {n : ℕ} {H L : Type} [Group H] [Group L]
    (p : H →* L) [Group.IsSolvable p.ker] (hL : Envelope n L) : Envelope n H := by
  let e := QuotientGroup.quotientKerEquivRange p
  exact .extension p.ker (.solvable _ inferInstance)
    (.subgroup e.toMonoidHom e.injective
      (.subgroup p.range.subtype p.range.subtype_injective hL))

/-- The kernel of the actual SU → PSU map is central and solvable. -/
public theorem Envelope.specialUnitary {n : ℕ} {F : Type} [Field F]
    (J : HermitianForm 3 F) (h : Envelope n (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Envelope n J.specialSubgroup := by
  let : Group.IsSolvable (Subgroup.center J.specialSubgroup) :=
    Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  let : Group.IsSolvable (suProjection J).ker :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (suProjection_ker_central J))
  exact h.of_solvable_kernel (suProjection J)

private def unitaryDetKernelEquiv {F : Type} [Field F] (J : HermitianForm 3 F) :
    (GeneralLinearGroup.det.comp J.unitarySubgroup.subtype).ker ≃* J.specialSubgroup where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The determinant quotient of the actual full unitary group is abelian. -/
public theorem Envelope.unitary {n : ℕ} {F : Type} [Field F]
    (J : HermitianForm 3 F) (h : Envelope n (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Envelope n J.unitarySubgroup := by
  let d : J.unitarySubgroup →* Fˣ := GeneralLinearGroup.det.comp J.unitarySubgroup.subtype
  let e := unitaryDetKernelEquiv J
  have hk : Envelope n d.ker := .subgroup e.toMonoidHom e.injective (h.specialUnitary J)
  let eq := QuotientGroup.quotientKerEquivRange d
  have hs : Group.IsSolvable (J.unitarySubgroup ⧸ d.ker) :=
    Group.isSolvable_of_isSolvable_injective (f := eq.toMonoidHom) eq.injective
  exact .extension d.ker hk (.solvable _ hs)

/-- The actual projective unitary image covers the PGU subfield alternatives. -/
public theorem Envelope.projectiveUnitary {n : ℕ} {F : Type} [Field F]
    (J : HermitianForm 3 F) (h : Envelope n (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Envelope n (J.unitarySubgroup.map ProjGenLinGroup.mk) :=
  .quotient (ProjGenLinGroup.mk.subgroupMap J.unitarySubgroup)
    (ProjGenLinGroup.mk.subgroupMap_surjective J.unitarySubgroup) (h.unitary J)

/-- All envelope leaves are discharged except strictly smaller unitary models. -/
public theorem Envelope.isKGroup {n : ℕ} {H : Type} [Group H] (h : Envelope n H)
    (hunitary : ∀ m, 0 < m → m < n → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ m) → IsKGroup IsConstructedCarrier L) :
    IsKGroup IsConstructedCarrier H := by
  induction h with
  | solvable H hs =>
      let := hs
      exact solvable_isKGroup_constructed H
  | linearTwo H q hH => exact psl2_isKGroup_constructed hH
  | generalLinearTwo F => exact LinearThreeSections.gl2_isKGroup_constructed F
  | binaryThree H hH => exact LinearThreeSections.psl3_two_isKGroup_constructed hH
  | alternatingSix => exact alternatingSix_isKGroup_constructed (MulEquiv.refl _)
  | pointParabolic F => exact LinearThreeSections.pointParabolic_isKGroup_constructed F
  | lineParabolic F => exact LinearThreeSections.lineParabolic_isKGroup_constructed F
  | unitarySubfield H m hm hmn _ _ hH => exact hunitary m hm hmn H hH
  | subgroup i hi _ ih => exact ih.of_injective i hi
  | quotient p hp _ ih => exact ih.of_surjective p hp
  | extension N _ _ ihN ihQ => exact IsKGroup.of_normal_quotient N ihN ihQ

/-- Strong induction includes the whole subgroup at every smaller exponent.
The exhaustion premise remains an independent mathematical obligation. -/
public theorem psu3_even_isKGroup_of_exhaustion
    (hexhaustion : ∀ n, 2 ≤ n → ∀ (F : Type) [Field F] [Finite F]
      (J : HermitianForm 3 F), Nat.card F = (2 ^ n) ^ 2 →
      (∀ x, J.conj x = x ^ (2 ^ n)) →
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
      ∀ U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), U ≠ ⊤ → Envelope n U)
    {G : Type*} [Group G] {n : ℕ} (hn : 0 < n)
    (hG : ClassicalGroup.IsPSU G 3 (2 ^ n)) : IsKGroup IsConstructedCarrier G := by
  have hsmall : ∀ n, 0 < n → ∀ (H : Type) [Group H],
      ClassicalGroup.IsPSU H 3 (2 ^ n) → IsKGroup IsConstructedCarrier H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn H _ hH
      by_cases h1 : n = 1
      · subst n
        exact psu3_two_isKGroup_constructed (by simpa only [pow_one] using hH)
      apply psu3_even_isKGroup_of_properK (by omega) hH
      obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hH
      obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
      let e' := e.trans (FormTransport.projectiveEquiv J C hC)
      have hp : HasProperKSubgroups IsConstructedCarrier
          (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) := by
        intro U hU
        exact (hexhaustion n (by omega) F (FormTransport.standardForm J) hcard hconj
          rfl U hU).isKGroup (fun m hm hmn L _ hL => ih m hmn hm L hL)
      exact HasProperKSubgroups.of_equiv e'.symm hp
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hG
  have hp : IsKGroup IsConstructedCarrier (ProjectiveSpecialUnitaryMatrixGroup J) :=
    hsmall n hn _ ⟨F, inferInstance, inferInstance, J, hcard, hconj, ⟨MulEquiv.refl _⟩⟩
  exact SymmetricEight.isKGroup_constructed_of_injective hp e.toMonoidHom e.injective

end CFSG.Quasithin.MainConverse.UnitaryThreeSections
