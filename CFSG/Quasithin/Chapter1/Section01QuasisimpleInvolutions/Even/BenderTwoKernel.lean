module

public import Theory.GroupTheory.PerfectCentralCoverSylowRigidityTwoKernel
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.CoverReduction
public import GorensteinWalter.LinearRingEquiv

/-!
# The Bender-family source branch through central two-kernel rigidity

The original marked involution is inner by the proved model Sylow-fixer
calculations. Its inversion of the odd core makes the center a two-group.
If this center were nontrivial, the actual projection L → L/Z(L), together
with the double-cover rigidity theorem and its central two-kernel extension,
would force the original automorphism to be the identity. Its prescribed
order two excludes this. The center-free source constructor then supplies
the original ModelAction115, with every Bender family and field guard retained.

The sole earlier input is the universal pointwise double-cover rigidity
implication, owned by qt-i68-zd-central-cover-rigidity. No multiplier,
universal-cover kernel or new action witness is an input.

Source: Aschbacher--Smith 1.1.5(3), printed pp.501--503; GLS4, Chapter 4,
Lemma 2.8(c) supplies the earlier double-cover theorem.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
universe u

/-- Convert the existing Bender catalogue using actual field and Hermitian
form equivalences, preserving its nonabelian simple parameter ranges. -/
theorem isSimpleBenderGroup_of_benderModel
    {B : Type u} [Group B] [Finite B] (h : IsBenderModel B) :
    BenderSuzuki.IsSimpleBenderGroup B := by
  classical
  cases h with
  | linear n hn iso =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
      let : Fintype F := Fintype.ofFinite F
      let : Fintype (BinaryGaloisField n) := Fintype.ofFinite _
      let eF : F ≃+* BinaryGaloisField n := FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
        symm
        exact GaloisField.card 2 n (by omega))
      exact .isPSL2 ⟨n, hn, ⟨e.trans (GorensteinWalter.psl2RingEquiv eF)⟩⟩
  | unitary n hn iso =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := iso
      have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
        (by omega) hF hconj
      obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
        J (2 ^ n) hF hfixed
      exact .isPSU3 ⟨n, hn, F, inferInstance, inferInstance,
        HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J,
        rfl, hF, hfixed, ⟨e.trans eJ⟩⟩
  | suzuki m hm e => exact .isSuzuki ⟨m, hm, e⟩

variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The genuine double-cover theorem excludes the whole nontrivial
two-primary center in the marked Bender source application. -/
theorem MarkedInvolution.bender_center_eq_bot_of_doubleCoverRigidity
    (d : MarkedInvolution α P) (h : IsBenderModel (L ⧸ center L))
    (rigidity : BenderSuzuki.ZD.DoubleCoverSylowRigidity.{u}) :
    center L = ⊥ := by
  have hi := d.bender_inner h
  have hz := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi d.inverts_odd_core
  have hp : IsPGroup 2 (center L) := hz ▸ pCore_isPGroup
  by_contra hne
  let f := centralQuotientCover (MulEquiv.refl (L ⧸ center L))
  have hfker : f.toMonoidHom.ker = center L := centralQuotientCover_ker _
  have hfp : IsPGroup 2 f.toMonoidHom.ker := by rw [hfker]; exact hp
  have hfn : f.toMonoidHom.ker ≠ ⊥ := by rwa [hfker]
  have hB := isSimpleBenderGroup_of_benderModel h
  have hd : DoubleCoverSylowRigidityAt.{u, u} (L ⧸ center L) := by
    intro E₀ _ _ c hc Q a hfix
    exact rigidity E₀ (L ⧸ center L) hB c hc Q a hfix
  have ha : α = 1 := f.fixingSylow_eq_one_of_nontrivial_twoKernel hd
    hfp hfn
    P α (fun x => d.fixes x x.property)
  have ho := d.order_two
  rw [ha, orderOf_one] at ho
  norm_num at ho

/-- The complete 1.1.5 Bender-family implication retains the original
automorphism and all model guards; only the genuine earlier rigidity
theorem remains to be supplied by its existing owner. -/
theorem MarkedInvolution.bender_modelAction_of_doubleCoverRigidity
    (d : MarkedInvolution α P) (h : IsBenderModel (L ⧸ center L))
    (rigidity : BenderSuzuki.ZD.DoubleCoverSylowRigidity.{u}) :
    ModelAction115 L α :=
  d.lie_of_center_eq_bot (Or.inl h) (d.bender_inner h)
    (d.bender_center_eq_bot_of_doubleCoverRigidity h rigidity)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
