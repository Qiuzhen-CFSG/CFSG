module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.OddBender
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
/-!
# Excluding Bender models for the original A₈ quotient

The A₈ Sylow group contains two noncommuting involutions. Binary PSL₂
Sylows are abelian, and all involutions in a binary PSU₃ Sylow are central.
The remaining Suzuki family is excluded by divisibility of |A₈| by three.
The arbitrary unitary form is transported to the antidiagonal model before
applying the actual first-omega calculation.

For the local section application, the proved Bender equality first makes
B the whole simple group. Its two-core is then trivial, since otherwise
the given A₈ quotient would be trivial. Thus the original quotient marking
lifts and the exact-model exclusion applies.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 15.3.32(3), p.1133.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
open Theory.SpecificGroups.SymmetricEight.CentralPair
open BenderSuzuki.MatrixGroups.HermitianForm
variable {G : Type*} [Group G]
private noncomputable def linearFourAlternatingEquiv
    (h4 : ClassicalGroup.IsPSL G 4 2) : G ≃* alternatingGroup (Fin 8) :=
  Classical.choice <| by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h4
    let := Fintype.ofFinite F
    let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    exact ⟨(e.trans (Atlas.fieldEquivPSL 4 k)).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩

/-- None of the actual Bender models is PSL₄(2). -/
theorem not_linearFourTwo_bender_model (hm : ClassificationModels.IsBenderModel G)
    (h4 : ClassicalGroup.IsPSL G 4 2) : False := by
  let e8 := linearFourAlternatingEquiv h4
  have hm8 := hm.of_mulEquiv e8.symm
  obtain ⟨x,y,hx,hy,hxy⟩ := _root_.AlternatingEight.exists_noncommuting_sylow_involutions evenTreeSylow
  cases hm8 with
  | linear n hn hmodel =>
    obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hmodel
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hK)
    let := Theory.PSL2.binary_sylow_commutative_of_injective eK.toMonoidHom eK.injective evenTreeSylow
    exact hxy (IsMulCommutative.is_comm.comm x y)
  | unitary n hn hmodel =>
    obtain ⟨K,_,_,J,hK,hconj,⟨eK⟩⟩ := hmodel
    have hfixed : Nat.card {a : K // J.conj a = a} = 2 ^ n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
    obtain ⟨d⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hK hfixed
    let J' := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    have hOmega := (SylowOmega.omega_of_projective_equiv J' hn hK hfixed rfl
      (eK.trans d) evenTreeSylow).1
    have hxc : (x : A8) ∈ (center evenTreeSylow).map (evenTreeSylow : Subgroup A8).subtype :=
      (omegaOneAmbient_le_iff _ _).mp hOmega.le x x.property (congrArg Subtype.val hx)
    obtain ⟨z,hz,hzx⟩ := hxc
    have hz' : z = x := Subtype.ext hzx
    subst z
    exact hxy (mem_center_iff.mp hz y).symm
  | suzuki m hm he =>
    obtain ⟨d⟩ := he
    have hcard : Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) = 20160 := by
      rw [← Nat.card_congr d.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
      (by rw [hcard]; decide)

/-- The local A₈ two-core section cannot lie in a simple Bender containing
model when normalized by the original full Sylow two-subgroup. -/
theorem not_linearFourTwo_section_of_bender_model [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hm : ClassificationModels.IsBenderModel G) : False := by
  have ht := eq_top_of_bender_model S B hB hn hm
  let eB : B ≃* G := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsSimpleGroup B := eB.isSimpleGroup
  have hcore : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · have hcard := Nat.card_congr (linearFourAlternatingEquiv hsection).toEquiv
      rw [nat_card_alternatingGroup, Nat.card_fin] at hcard
      norm_num [Nat.factorial] at hcard
      rw [hc] at hcard
      simp at hcard
  let q : B ≃* B ⧸ pCore 2 B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hcore.symm)
  exact not_linearFourTwo_bender_model (hm.of_mulEquiv eB) (hsection.of_mulEquiv q)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
