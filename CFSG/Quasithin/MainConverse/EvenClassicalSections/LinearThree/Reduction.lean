module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.ParabolicSections
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThreeBinary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Subfield induction for the degree-three section calculation

`Envelope f H` records concrete smaller models and elementary group operations.
Every model is an actual matrix group, or comes with a multiplicative
equivalence through `IsPSL` or `IsPSU`. Injections, surjections and normal
extensions keep the connection to H explicit. The degree-three parameters
strictly decrease; the other leaves have proved section theorems.

The conditional assembly below proves strong induction, including the whole
smaller PSL₃ model. Its simplicity is the intrinsic projective-transvection
theorem, and its carrier belongs to the constructed linear family. No global
classification or ambient K-group assumption is used.

Two inputs remain: an intrinsic exhaustion of proper PSL₃ subgroups into
these envelopes, and all simple sections of the unitary subfield models.
Neither input is asserted here. In particular PSU₃(2ᵇ) embeds in PSL₃(2²ᵇ),
which does not decrease the linear field when 2b = f; that embedding cannot
discharge the unitary input to this induction.

Source: Hartley–Mitchell alternatives in GLS3, Theorem 6.5.3(a–i),
`refs/KGroup/GLS3/chapter6.tex`, specialized to characteristic two and proper
subgroups. We coarsen the solvable cases and the diagonal extensions only
for the section calculation. The shortened GLS proof assumes K and cannot
prove the missing exhaustion. The target K condition is Aschbacher–Smith,
Main Hypothesis 0.1.1, printed pp.4 and 482.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open CFSG.KnownSimple Matrix Matrix.PSL3.LinearThree
open scoped MatrixGroups

/-- The whole smaller linear model contributes itself as well as its proper
sections. Simplicity and catalogue membership follow from the actual model. -/
public theorem psl3_isKGroup_of_properK {G : Type*} [Group G] {q : ℕ}
    (hG : ClassicalGroup.IsPSL G 3 q)
    (hproper : HasProperKSubgroups IsConstructedCarrier G) :
    IsKGroup IsConstructedCarrier G := by
  have hs : IsSimpleGroup G := by
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hG
    let : IsSimpleGroup PSL(3, F) := Atlas.psl_simple_high_rank 3 (by decide)
    exact e.isSimpleGroup
  let := hs
  have hpow : IsPrimePow q := by
    obtain ⟨F, _, _, hcard, _⟩ := hG
    let : Fintype F := Fintype.ofFinite F
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card F
  have hc : IsConstructedCarrier G :=
    .classical (.linear 3 q ⟨hpow, by decide, by omega⟩ hG)
  intro S _ hS U f hf
  let := hS
  by_cases hU : U = ⊤
  · subst U
    let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    exact SymmetricEight.simple_quotient_constructed hc
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)
  · let e : (⊤ : Subgroup U) ≃* U := Subgroup.topEquiv
    exact hproper U hU S hS ⊤ (f.comp e.toMonoidHom) (hf.comp e.surjective)

/-- The binary endpoint also includes simple quotients of the whole model. -/
public theorem psl3_two_isKGroup_constructed {G : Type*} [Group G]
    (hG : ClassicalGroup.IsPSL G 3 2) : IsKGroup IsConstructedCarrier G :=
  psl3_isKGroup_of_properK hG (psl3_two_properK_constructed hG)

/-- Concrete overgroups and normal layers sufficient for the Hartley–Mitchell
section argument. This definition does not assert that the cases are exhaustive. -/
public inductive Envelope (f : ℕ) : (H : Type) → [Group H] → Prop where
  | solvable (H : Type) [Group H] (hH : Group.IsSolvable H) : Envelope f H
  | linearTwo (H : Type) [Group H] (q : ℕ)
      (hH : ClassicalGroup.IsPSL H 2 q) : Envelope f H
  | binaryThree (H : Type) [Group H]
      (hH : ClassicalGroup.IsPSL H 3 2) : Envelope f H
  | alternatingSix : Envelope f (alternatingGroup (Fin 6))
  | pointParabolic (F : Type) [Field F] [Finite F] : Envelope f (pointParabolic F)
  | lineParabolic (F : Type) [Field F] [Finite F] : Envelope f (lineParabolic F)
  | linearSubfield (H : Type) [Group H] (m : ℕ) (hm : 0 < m) (hmf : m < f)
      (hH : ClassicalGroup.IsPSL H 3 (2 ^ m)) : Envelope f H
  | unitarySubfield (H : Type) [Group H] (m : ℕ) (hm : 0 < m) (hmf : m < f)
      (hH : ClassicalGroup.IsPSU H 3 (2 ^ m)) : Envelope f H
  | subgroup {H L : Type} [Group H] [Group L] (i : H →* L)
      (hi : Function.Injective i) (hL : Envelope f L) : Envelope f H
  | quotient {H L : Type} [Group H] [Group L] (p : L →* H)
      (hp : Function.Surjective p) (hL : Envelope f L) : Envelope f H
  | extension {H : Type} [Group H] (N : Subgroup H) [N.Normal]
      (hN : Envelope f N) (hQ : Envelope f (H ⧸ N)) : Envelope f H

/-- A solvable kernel adds no new nonabelian leaf to the envelope. -/
public theorem Envelope.of_solvable_kernel {f : ℕ} {H L : Type} [Group H] [Group L]
    (p : H →* L) [Group.IsSolvable p.ker] (hL : Envelope f L) : Envelope f H := by
  let e := QuotientGroup.quotientKerEquivRange p
  exact .extension p.ker (.solvable _ inferInstance)
    (.subgroup e.toMonoidHom e.injective
      (.subgroup p.range.subtype p.range.subtype_injective hL))

/-- A central linear cover is an extension by a solvable group. -/
public theorem Envelope.specialLinear {f n : ℕ} (F : Type) [Field F]
    (h : Envelope f PSL(n, F)) : Envelope f SL(n, F) := by
  have hs : Group.IsSolvable (Subgroup.center SL(n, F)) :=
    Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  exact .extension (Subgroup.center SL(n, F)) (.solvable _ hs) h

private def determinantKernelToSpecialLinear (n : ℕ) (F : Type) [Field F] :
    (GeneralLinearGroup.det : GL (Fin n) F →* Fˣ).ker →* SL(n, F) where
  toFun g := ⟨g.val.val, by
    have h := congrArg Units.val g.property
    simpa using h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The determinant quotient accounts for the diagonal linear extensions. -/
public theorem Envelope.generalLinear {f n : ℕ} (F : Type) [Field F]
    (h : Envelope f PSL(n, F)) : Envelope f (GL (Fin n) F) := by
  let d : GL (Fin n) F →* Fˣ := GeneralLinearGroup.det
  have hker : Envelope f d.ker :=
    .subgroup (determinantKernelToSpecialLinear n F) (by
      intro a b hab
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val hab) (h.specialLinear F)
  let e := QuotientGroup.quotientKerEquivRange d
  have hs : Group.IsSolvable (GL (Fin n) F ⧸ d.ker) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact .extension d.ker hker (.solvable _ hs)

/-- Passing to the scalar quotient handles PGL₂ and the PGL₃ subfield cases
without assuming that the projective diagonal extension splits. -/
public theorem Envelope.projectiveGeneralLinear {f n : ℕ} (F : Type) [Field F]
    (h : Envelope f PSL(n, F)) : Envelope f (ProjGenLinGroup (Fin n) F) :=
  .quotient ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective (h.generalLinear F)

/-- Removing the normal layers in an envelope leaves only the two explicit
subfield inputs. All other leaves are discharged by proved model calculations. -/
public theorem Envelope.isKGroup {f : ℕ} {H : Type} [Group H] (h : Envelope f H)
    (hlinear : ∀ m, 0 < m → m < f → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSL L 3 (2 ^ m) → IsKGroup IsConstructedCarrier L)
    (hunitary : ∀ m, 0 < m → m < f → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ m) → IsKGroup IsConstructedCarrier L) :
    IsKGroup IsConstructedCarrier H := by
  induction h with
  | solvable H hs =>
      let := hs
      exact solvable_isKGroup_constructed H
  | linearTwo H q hH => exact psl2_isKGroup_constructed hH
  | binaryThree H hH => exact psl3_two_isKGroup_constructed hH
  | alternatingSix => exact alternatingSix_isKGroup_constructed (MulEquiv.refl _)
  | pointParabolic F => exact pointParabolic_isKGroup_constructed F
  | lineParabolic F => exact lineParabolic_isKGroup_constructed F
  | linearSubfield H m hm hmf hH => exact hlinear m hm hmf H hH
  | unitarySubfield H m hm hmf hH => exact hunitary m hm hmf H hH
  | subgroup i hi _ ih => exact ih.of_injective i hi
  | quotient p hp _ ih => exact ih.of_surjective p hp
  | extension N _ _ ihN ihQ => exact IsKGroup.of_normal_quotient N ihN ihQ

/-- Strong induction closes the linear subfield recursion once the intrinsic
exhaustion and the independent unitary section calculation are supplied. -/
public theorem psl3_isKGroup_of_exhaustion
    (hexhaustion : ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3, F), U ≠ ⊤ → Envelope f U)
    (hunitary : ∀ m, 0 < m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ m) → IsKGroup IsConstructedCarrier L)
    {G : Type*} [Group G] {f : ℕ} (hf : 0 < f)
    (hG : ClassicalGroup.IsPSL G 3 (2 ^ f)) : IsKGroup IsConstructedCarrier G := by
  have hsmall : ∀ n, 0 < n → ∀ (H : Type) [Group H],
      ClassicalGroup.IsPSL H 3 (2 ^ n) → IsKGroup IsConstructedCarrier H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn H _ hH
      by_cases h1 : n = 1
      · subst n
        exact psl3_two_isKGroup_constructed (by simpa only [pow_one] using hH)
      apply psl3_isKGroup_of_properK hH
      obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hH
      have hp : HasProperKSubgroups IsConstructedCarrier PSL(3, F) := by
        intro U hU
        exact (hexhaustion n (by omega) F hcard U hU).isKGroup
          (fun m hm hmn L _ hL => ih m hmn hm L hL)
          (fun m hm _ L _ hL => hunitary m hm L hL)
      exact HasProperKSubgroups.of_equiv e.symm hp
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hG
  have hp : IsKGroup IsConstructedCarrier PSL(3, F) :=
    hsmall f hf _ ⟨F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩
  exact SymmetricEight.isKGroup_constructed_of_injective hp e.toMonoidHom e.injective

end CFSG.Quasithin.MainConverse.LinearThreeSections
