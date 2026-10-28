module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.Reduction
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.RecognitionInput
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.Quasisimple

/-!
# Perfect rank-two actions

The actual relative centralizer is the kernel of H's conjugation action on
P/Φ(P). Its quotient is a nontrivial perfect subgroup of SL₂(p), with p > 3.
The proved Dickson recognition theorem then gives actual isomorphisms,
establishing A.1.29(1) with no additional input. For the quasisimple clause,
the exact prime-field cover rigidity identifies this kernel with the odd
core and proves two-rank one. Only that universal-cover input remains
explicit in A.1.29(2); the parent assembly must discharge it from I.1.3.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.29, printed p.27.
-/

namespace CFSG.Quasithin.ChapterA.RankActions
open Subgroup

/-- Assemble A.1.29(1) once its independent perfect-subgroup recognition
is available. The kernel and all action hypotheses are the source ones. -/
public theorem perfectAction_models_of_recognition
    (hrecognize : PrimePerfectSL2Recognition)
    {G : Type*} [Group G] [Finite G] (P H : Subgroup G) [P.Normal]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hP : IsPGroup p P)
    (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥) :
    Nonempty ((H ⧸ frattiniCentralizer P H) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∨
      ((p % 5 = 1 ∨ p % 5 = 4) ∧
        Nonempty ((H ⧸ frattiniCentralizer P H) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  obtain ⟨f, hf⟩ := quotient_embeds_SL P H hp2 hP ho hc hr
  let : Nontrivial (H ⧸ frattiniCentralizer P H) :=
    frattiniQuotient_nontrivial P H hP hPH
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let e := MonoidHom.ofInjective hf
  let : Nontrivial f.range := e.injective.nontrivial
  rcases hrecognize p (three_lt_of_perfect_action P H hp2 hP ho hc hr hPH)
      f.range inferInstance inferInstance with hfull | hexception
  · obtain ⟨j⟩ := hfull
    exact Or.inl ⟨e.trans j⟩
  · obtain ⟨hmod, ⟨j⟩⟩ := hexception
    exact Or.inr ⟨hmod, ⟨e.trans j⟩⟩

universe u

/-- Apply the cover deduction to an actual isomorphism of the Frattini-action
quotient. No ambient normality of H is needed. -/
public theorem oddCore_eq_frattiniCentralizer_of_SL2
    (hrigid : PrimeSL2CoverRigidity.{u})
    {G : Type u} [Group G] [Finite G] (P H : Subgroup G) [P.Normal]
    [Theory.GroupTheory.IsQuasisimple (H ⧸ pPrimeCore 2 H)]
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (e : (H ⧸ frattiniCentralizer P H) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :
    pPrimeCore 2 H = frattiniCentralizer P H ∧ primeRank 2 H = 1 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (frattiniCentralizer P H))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = frattiniCentralizer P H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  simpa only [hk] using oddCore_eq_kernel_of_quasisimple_SL2_image hrigid hr f hf

/-- Assemble A.1.29(2) from independent linear recognition and the explicitly
permitted prime-field universal-cover input. All action premises are discharged
from the source hypotheses. -/
public theorem perfectAction_quasisimple_of_recognition
    (hrecognize : PrimePerfectSL2Recognition) (hrigid : PrimeSL2CoverRigidity.{u})
    {G : Type u} [Group G] [Finite G] (P H : Subgroup G) [P.Normal]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hP : IsPGroup p P)
    (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥)
    [Theory.GroupTheory.IsQuasisimple (H ⧸ pPrimeCore 2 H)] :
    pPrimeCore 2 H = frattiniCentralizer P H ∧ primeRank 2 H = 1 := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  rcases perfectAction_models_of_recognition hrecognize P H hp hP ho hc hr hPH
      with hfull | hexception
  · obtain ⟨e⟩ := hfull
    exact oddCore_eq_frattiniCentralizer_of_SL2 hrigid P H
      (three_lt_of_perfect_action P H hp2 hP ho hc hr hPH) e
  · obtain ⟨_, ⟨e⟩⟩ := hexception
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact oddCore_eq_frattiniCentralizer_of_SL2 hrigid P H (by decide) e

end CFSG.Quasithin.ChapterA.RankActions

namespace CFSG.Quasithin.ChapterA
open Subgroup RankActions

/-- A.1.29(1): the quotient by the relative centralizer of P/Φ(P) is
SL₂(p), or SL₂(5) with p congruent to ±1 modulo five. This uses the
actual conjugation action and has no independent recognition premise. -/
public theorem lemma_A_1_29_1
    {G : Type*} [Group G] [Finite G] (P H : Subgroup G) [P.Normal]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hP : IsPGroup p P)
    (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥) :
    Nonempty ((H ⧸ frattiniCentralizer P H) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∨
      ((p % 5 = 1 ∨ p % 5 = 4) ∧
        Nonempty ((H ⧸ frattiniCentralizer P H) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) :=
  perfectAction_models_of_recognition primePerfectSL2Recognition P H hp hP ho hc hr hPH

universe u

/-- A.1.29(2), conditional only on the prime-field universal-cover consequence
of I.1.3: for quasisimple H/O(H), the actual relative centralizer is O(H)
and H has two-rank one. The parent assembly retains discharge of the exact
`PrimeSL2CoverRigidity` input; this is not the unconditional source clause. -/
public theorem lemma_A_1_29_2_of_coverRigidity
    (hrigid : PrimeSL2CoverRigidity.{u})
    {G : Type u} [Group G] [Finite G] (P H : Subgroup G) [P.Normal]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hP : IsPGroup p P)
    (ho : omega₁ P (p := p) = ⊤)
    (hc : _root_.commutator P ≤ center P) (hr : primeRank p P = 2)
    [Group.IsPerfect H] (hPH : ⁅P, H⁆ ≠ ⊥)
    [Theory.GroupTheory.IsQuasisimple (H ⧸ pPrimeCore 2 H)] :
    pPrimeCore 2 H = frattiniCentralizer P H ∧ primeRank 2 H = 1 :=
  perfectAction_quasisimple_of_recognition primePerfectSL2Recognition hrigid
    P H hp hP ho hc hr hPH

end CFSG.Quasithin.ChapterA
