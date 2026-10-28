module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.OddCoreGeneration
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.QuotientGeometry
public import Glauberman.Signalizer.TwoCompletion
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The actual subgroups in the E.6.20 signalizer argument

The quotient values are the odd cores of the centralizers of the nonidentity
actors in C_G(U₀)/U₀. Their odd order, solvability, invariance and fixation
are proved here for the named conjugation action. Only balance remains an
explicit premise of the completion application; its transport from E.6.19
is a separate mathematical obligation.

The local odd closure and the local and global prime closures are actual
suprema of embedded cores. They are the groups X, Y and the right side of
(**) in the source, without any assumed order or generation properties.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.20,
printed pp.252–253 (PDF pp.263–264).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination

variable {G : Type*} [Group G] [Finite G]

/-- The exact E.6.19 input, retaining both hyperplane hypotheses. -/
def HyperplaneBalance (V : Subgroup G) : Prop :=
  ∀ W W₀ : Subgroup G, IsHyperplane V W → IsHyperplane V W₀ →
    oddCentralizer W ≤ oddCentralizer (W ⊓ W₀)

/-- The subgroup X before taking any prime core. -/
def localOddClosure (V U₀ : Subgroup G) : Subgroup G :=
  ⨆ A : {A : Subgroup G // U₀ < A ∧ A ≤ V}, oddCentralizer A.val

/-- The embedded prime core O_p(C_G(A)). -/
def primeCentralizer (p : ℕ) (A : Subgroup G) : Subgroup G :=
  (centralizer (A : Set G)).pCoreIn p

/-- The hyperplane-generated group on the right of (*) in E.6.20. -/
def localPrimeClosure (p : ℕ) (V U₀ : Subgroup G) : Subgroup G :=
  ⨆ W : {W : Subgroup G // U₀ ≤ W ∧ IsHyperplane V W}, primeCentralizer p W.val

/-- The global hyperplane-generated group on the right of (**). -/
def globalPrimeClosure (p : ℕ) (V : Subgroup G) : Subgroup G :=
  ⨆ W : {W : Subgroup G // IsHyperplane V W}, primeCentralizer p W.val

omit [Finite G] in
/-- Every generating odd core centralizes the initial subspace. -/
theorem localOddClosure_le (V U₀ : Subgroup G) :
    localOddClosure V U₀ ≤ centralizer (U₀ : Set G) := by
  exact iSup_le fun A => (oddCentralizer_le A.val).trans
    (Subgroup.centralizer_le A.property.1.le)

omit [Finite G] in
/-- A displayed local core is a subgroup of the actual closure. -/
theorem oddCentralizer_le_localOddClosure {V U₀ A : Subgroup G}
    (hA : U₀ < A) (hAV : A ≤ V) : oddCentralizer A ≤ localOddClosure V U₀ :=
  le_iSup (fun B : {B : Subgroup G // U₀ < B ∧ B ≤ V} => oddCentralizer B.val)
    ⟨A, hA, hAV⟩

omit [Finite G] in
/-- Local hyperplane generation is contained in global hyperplane generation. -/
theorem localPrimeClosure_le_global (p : ℕ) (V U₀ : Subgroup G) :
    localPrimeClosure p V U₀ ≤ globalPrimeClosure p V := by
  refine iSup_le fun W => ?_
  exact le_iSup (fun A : {A : Subgroup G // IsHyperplane V A} =>
    primeCentralizer p A.val) ⟨W.val, W.property.2⟩

/-- The embedded odd core has odd order, without an ambient solvability premise. -/
theorem oddCentralizer_odd (A : Subgroup G) : Odd (Nat.card (oddCentralizer A)) := by
  rw [oddCentralizer, Subgroup.card_map_of_injective (centralizer (A : Set G)).subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

omit [Finite G] in
/-- Normality is used only inside the defining centralizer. -/
theorem centralizer_le_normalizer_oddCentralizer (A : Subgroup G) :
    centralizer (A : Set G) ≤ normalizer (oddCentralizer A : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro g hg x ⟨y, hy, rfl⟩
  let c : centralizer (A : Set G) := ⟨g, hg⟩
  exact ⟨c * y * c⁻¹, (inferInstance : (pPrimeCore 2 (centralizer (A : Set G))).Normal).conj_mem y hy c, rfl⟩

variable (V U₀ : Subgroup G)

/-- The actual value O(C_{H₀/U₀}(a)), also defined at the identity for convenience. -/
def quotientValue (a : quotientActor V U₀) : Subgroup (CentralizerQuotient U₀) :=
  oddCentralizer (zpowers (a : CentralizerQuotient U₀))

/-- The quotient closure is independent of the proof of balance. -/
def quotientClosure : Subgroup (CentralizerQuotient U₀) :=
  ⨆ a : {a : quotientActor V U₀ // a ≠ 1}, quotientValue V U₀ a.val

/-- Balance for the actual odd-core values, expressed with intrinsic centralizers. -/
def QuotientBalance : Prop :=
  ∀ a b : {a : quotientActor V U₀ // a ≠ 1},
    quotientValue V U₀ a.val ⊓
      centralizer (zpowers (b.val : CentralizerQuotient U₀) : Set (CentralizerQuotient U₀)) ≤
        quotientValue V U₀ b.val

omit [Finite G] in
/-- Conjugation fixation is exactly centralization in the actual quotient group. -/
theorem quotient_fixed_eq_centralizer (a : quotientActor V U₀) :
    letI := quotientAction V U₀
    FixedPoints.subgroup (zpowers a) (CentralizerQuotient U₀) =
      centralizer (zpowers (a : CentralizerQuotient U₀) : Set (CentralizerQuotient U₀)) := by
  let _ := quotientAction V U₀
  ext x
  constructor
  · intro hx
    have hax := hx (⟨a, mem_zpowers a⟩ : zpowers a)
    have hcomm : Commute (a : CentralizerQuotient U₀) x := by
      exact mul_inv_eq_iff_eq_mul.mp hax
    rintro y ⟨n, rfl⟩
    exact (hcomm.zpow_left n).eq
  · intro hx b
    change ((b.val : quotientActor V U₀) : CentralizerQuotient U₀) * x *
      ((b.val : quotientActor V U₀) : CentralizerQuotient U₀)⁻¹ = x
    apply mul_inv_eq_iff_eq_mul.mpr
    obtain ⟨n, hn⟩ := b.property
    have hb := congrArg (fun c : quotientActor V U₀ => (c : CentralizerQuotient U₀)) hn
    exact hx _ (hb ▸ (zpowers (a : CentralizerQuotient U₀)).zpow_mem (mem_zpowers _) n)

/-- Oddness follows from the definition of O, then solvability from Feit–Thompson. -/
theorem quotientValue_odd (a : quotientActor V U₀) :
    Odd (Nat.card (quotientValue V U₀ a)) := oddCentralizer_odd _

theorem quotientValue_solvable (a : quotientActor V U₀) :
    Group.IsSolvable (quotientValue V U₀ a) :=
  odd_order_theorem _ (quotientValue_odd V U₀ a)

omit [Finite G] in
/-- The indexing actor fixes its whole odd-core value. -/
theorem quotientValue_le_fixed (a : quotientActor V U₀) :
    letI := quotientAction V U₀
    quotientValue V U₀ a ≤ FixedPoints.subgroup (zpowers a) (CentralizerQuotient U₀) := by
  rw [quotient_fixed_eq_centralizer]
  exact oddCentralizer_le _

variable [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- All actors lie in each actor centralizer, so relative normality gives invariance. -/
theorem quotientValue_invariant (hU : U₀ ≤ V) (a : quotientActor V U₀) :
    @IsInvariant (quotientActor V U₀) (CentralizerQuotient U₀) _
      (quotientAction V U₀).toMulAction.toSMul (quotientValue V U₀ a) := by
  let _ := quotientAction V U₀
  let _ := quotientActor_elementary V U₀ hU
  let _ : SMul (quotientActor V U₀) (CentralizerQuotient U₀) :=
    (quotientAction V U₀).toMulAction.toSMul
  refine { invariant := ?_ }
  intro b x
  have hb : (b : CentralizerQuotient U₀) ∈
      centralizer (zpowers (a : CentralizerQuotient U₀) : Set (CentralizerQuotient U₀)) := by
    have hcomm : Commute (a : CentralizerQuotient U₀) (b : CentralizerQuotient U₀) :=
      congrArg Subtype.val (mul_comm' a b)
    rintro y ⟨n, rfl⟩
    exact (hcomm.zpow_left n).eq
  exact mem_normalizer_iff.mp (centralizer_le_normalizer_oddCentralizer _ hb) x

/-- The odd-core signalizer for the named quotient action; only balance is pending. -/
def quotientSignalizer (hU : U₀ ≤ V) (hbal : QuotientBalance V U₀) :
    letI := quotientAction V U₀
    Theory.GroupTheory.TwoSignalizerFamily (quotientActor V U₀) (CentralizerQuotient U₀) := by
  let _ := quotientAction V U₀
  exact {
    subgroup := fun a => quotientValue V U₀ a.val
    odd := fun a => quotientValue_odd V U₀ a.val
    solvable := fun a => quotientValue_solvable V U₀ a.val
    invariant := fun a => quotientValue_invariant V U₀ hU a.val
    le_fixed := fun a => quotientValue_le_fixed V U₀ a.val
    balance := fun a b => by
      rw [quotient_fixed_eq_centralizer]
      exact hbal a b }

/-- Genuine signalizer completion at corank three for the actual quotient action. -/
theorem quotientSignalizer_complete (hU : U₀ ≤ V)
    (hc : subgroupCorank V U₀ = 3) (hbal : QuotientBalance V U₀) :
    letI := quotientAction V U₀
    (quotientSignalizer V U₀ hU hbal).IsComplete := by
  let _ := quotientAction V U₀
  let _ := quotientActor_elementary V U₀ hU
  exact Glauberman.solvable_two_signalizer_complete _
    (by rw [quotientActor_card_eight V U₀ hU hc])

/-- The completion has odd order and recovers every actual odd-core value. -/
theorem quotientClosure_odd_and_fixed (hU : U₀ ≤ V)
    (hc : subgroupCorank V U₀ = 3) (hbal : QuotientBalance V U₀) :
    Odd (Nat.card (quotientClosure V U₀)) ∧
      ∀ a : {a : quotientActor V U₀ // a ≠ 1},
        quotientClosure V U₀ ⊓
          centralizer (zpowers (a.val : CentralizerQuotient U₀) : Set (CentralizerQuotient U₀)) =
            quotientValue V U₀ a.val := by
  let _ := quotientAction V U₀
  have hcpl := quotientSignalizer_complete V U₀ hU hc hbal
  refine ⟨hcpl.1, fun a => ?_⟩
  have hf := hcpl.fixed_eq a
  rw [quotient_fixed_eq_centralizer] at hf
  exact hf

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
