module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddRanks
public import Theory.GroupTheory.TwoRankFourthPower
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.Alternating.PrimeRank
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.Eight
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.Mathieu.M11.Properties.Order
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSporadic

/-!
# Model exclusions for the original placed binary-three component

The whole doubled orbit has rank six in the component central quotient.
In each of J₂, J₃ and McL, a literal element with nontrivial fourth power
lies in a Sylow group of order 128. An elementary subgroup of order at least
64 would have index one or two, forcing every fourth power to be trivial.
This gives the sufficient rank bound five. The established Mathieu and HS
bounds then leave exactly M₂₄, J₄, He and Ru from the sporadic catalogue.
The exact alternating rank and actual PSL₄(2)-to-A₈ equivalence exclude
the alternating rows and the binary four-dimensional linear row.

The original residual also supplies an SL₃(2) section of the same component
quotient. Binary PSL₂ has abelian Sylow two-subgroups, while this section has
a dihedral Sylow group of order eight. Suzuki has order prime to three.
Thus only the unitary row remains among the Bender models. The final model
inspection combines these exclusions with the established odd-model bounds.
NonFFSourceDoubledBinaryPlacedModels applies it to the original H-star actor,
whole orbit, full central quotient and unchanged residual homomorphism.

The proof-only import reuses the certified J₃ and McL words and evaluations;
it introduces no new finite-group enumeration. Their ATLAS realizations are
J3G1-p6156B0 and McLG1-p275B0, with the composition conventions and source
attribution in the imported modules and LICENSES/ATLAS.txt. J₂ uses its
existing certified order-eight word. Source: Aschbacher--Smith 4.4.12 and
the following model inspection, printed p.622, as consumed by 7.3.4 and
7.6.1, printed pp.699,702, refs/quasithin.pdf. Remaining Lie and sporadic
geometric exclusions are not asserted by this model reduction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedModels
open DoubledBinaryOddSporadic

/-- The fourth power of the product of the two original J₃ Sylow generators
is detected at letter zero, excluding an elementary subgroup of order 64. -/
theorem janko_three_twoRank_le_five : primeRank 2 Sporadic.Janko3.Model ≤ 5 := by
  let S : Sylow 2 Sporadic.Janko3.Model := Sporadic.Janko3.TwoLocal.sylowCandidate_isPGroup.toSylow (by
    have hc := Sporadic.Janko3.TwoLocal.sylowCandidate.index_mul_card
    rw [Sporadic.Janko3.TwoLocal.sylowCandidate_card,Sporadic.Janko3.model_card] at hc
    omega)
  rw [S.primeRank_eq]
  apply twoRank_le_of_card_pow_and_fourth_ne 5 Janko.card_P (Janko.g 1 * Janko.g 2)
  intro he
  have hh := congrArg Janko.point he
  exact (by decide +kernel : Janko.point ((Janko.g 1 * Janko.g 2)^4) ≠ Janko.point 1) hh

/-- The fourth power of the original McL three-generator word is detected
at the two stored letters, giving the sufficient bound five. -/
theorem mcl_twoRank_le_five : primeRank 2 Sporadic.LeechRelated.McL.Carrier ≤ 5 := by
  rw [McLaughlin.sylow.primeRank_eq]
  apply twoRank_le_of_card_pow_and_fourth_ne 5 McLaughlin.card_P
    (McLaughlin.g 0 * McLaughlin.g 1 * McLaughlin.g 2)
  intro he
  have hh := congrArg McLaughlin.point he
  exact (by decide +kernel :
    McLaughlin.point ((McLaughlin.g 0 * McLaughlin.g 1 * McLaughlin.g 2)^4) ≠
      McLaughlin.point 1) hh

/-- Conjugate the certified J₂ order-eight word into the actual Sylow
subgroup of order 128; its nontrivial fourth power gives the bound five. -/
theorem janko_two_twoRank_le_five : primeRank 2 Sporadic.LeechRelated.J2.Carrier ≤ 5 := by
  let S := Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.sylow
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁
  obtain ⟨y,hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow
    (show orderOf Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.eight = 2^3 from
      Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.orderOf_eight)
  have hyo : orderOf y = 8 := by
    rw [←orderOf_injective (S : Subgroup Sporadic.LeechRelated.J2.Carrier).subtype
      (S : Subgroup Sporadic.LeechRelated.J2.Carrier).subtype_injective]
    change orderOf (y : Sporadic.LeechRelated.J2.Carrier) = 8
    obtain ⟨c,hc⟩ := isConj_iff.mp hy
    rw [←hc]
    change orderOf (MulAut.conj c Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.eight) = 8
    rw [MulEquiv.orderOf_eq,
      Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.orderOf_eight]
  rw [S.primeRank_eq]
  apply twoRank_le_of_card_pow_and_fourth_ne 5
    (Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.card_sylow _) y
  intro he
  have hh := orderOf_dvd_of_pow_eq_one he
  rw [hyo] at hh
  norm_num at hh

/-- Every alternating row of Theorem B has two-rank at most four. -/
theorem alternating_twoRank_le_four {n : ℕ} (hn : n ≤ 9) :
    primeRank 2 (alternatingGroup (Fin n)) ≤ 4 := by
  rw [(GLS3.Chapter5.PRank.alternating_hasPRank_two n).primeRank_eq Nat.prime_two]
  omega

/-- The actual field transport and exceptional equivalence give the
binary PSL₄ bound, retaining the literal full projective quotient. -/
theorem binary_linear_four_twoRank_le_four {Q : Type*} [Group Q] [Finite Q]
    (hm : ClassicalGroup.IsPSL Q 4 2) : primeRank 2 Q ≤ 4 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let b := e.trans ((Atlas.fieldEquivPSL 4 a).trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  rw [primeRank_equiv 2 b]
  exact alternating_twoRank_le_four (by decide)

open ClassificationModels ChapterA.Section02

private theorem small_sporadic_twoRank_le_five (name : SporadicName)
    (h24 : name ≠ .m24) (h4 : name ≠ .j4) (hh : name ≠ .he) (hr : name ≠ .ru) :
    primeRank 2 name.Carrier ≤ 5 := by
  cases name with
  | m11 =>
      change primeRank 2 Sporadic.Mathieu.M11 ≤ 5
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Sporadic.Mathieu.m11_order]
      norm_num
  | m12 => exact Sporadic.Mathieu.m12_twoRank_le_three.trans (by decide)
  | m22 => exact Sporadic.Mathieu.m22_twoRank_le_four.trans (by decide)
  | m23 => exact Sporadic.Mathieu.m23_twoRank_le_four.trans (by decide)
  | m24 => exact (h24 rfl).elim
  | j2 => exact janko_two_twoRank_le_five
  | j3 => exact janko_three_twoRank_le_five
  | j4 => exact (h4 rfl).elim
  | hs => exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  | he => exact (hh rfl).elim
  | ru => exact (hr rfl).elim

/-- The whole rank-six orbit leaves precisely these four possible sporadic
carriers, each retaining its actual group equivalence. -/
theorem sporadic_remaining_of_rank_six {Q : Type*} [Group Q] [Finite Q]
    (hr : 6 ≤ primeRank 2 Q) (hm : IsTheoremBSporadicModel Q) :
    ∃ name : SporadicName, (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
      Nonempty (Q ≃* name.Carrier) := by
  rcases hm with ⟨name,⟨e⟩⟩ | hs
  · by_cases h24 : name = .m24
    · exact ⟨name,Or.inl h24,⟨e⟩⟩
    by_cases h4 : name = .j4
    · exact ⟨name,Or.inr (Or.inl h4),⟨e⟩⟩
    by_cases hh : name = .he
    · exact ⟨name,Or.inr (Or.inr (Or.inl hh)),⟨e⟩⟩
    by_cases hru : name = .ru
    · exact ⟨name,Or.inr (Or.inr (Or.inr hru)),⟨e⟩⟩
    let : Finite name.Carrier := Finite.of_equiv Q e.toEquiv
    rw [primeRank_equiv 2 e] at hr
    have := small_sporadic_twoRank_le_five name h24 h4 hh hru
    omega
  · rcases hs with hj | hm
    · obtain ⟨e⟩ := hj
      rw [primeRank_equiv 2 e] at hr
      have hb : primeRank 2 Janko1.Model ≤ 3 := by
        apply primeRank_le_of_prime_pow_not_dvd
        rw [Janko1.card_model]
        norm_num
      omega
    · obtain ⟨e⟩ := hm
      rw [primeRank_equiv 2 e] at hr
      have := mcl_twoRank_le_five
      omega

/-- A subgroup section of binary PSL₂ has abelian Sylow two-subgroups,
so it cannot be the original binary-three residual quotient. -/
theorem binary_linear_two_no_section {Q : Type*} [Group Q] [Finite Q]
    {n : ℕ} (hm : ClassicalGroup.IsPSL Q 2 (2^n))
    (U : Subgroup Q) (f : U →* BinaryLinearThree.Group) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let g := Matrix.PSL3Two.equiv.toMonoidHom.comp f
  have hg : Function.Surjective g := Matrix.PSL3Two.equiv.surjective.comp hf
  let R : Sylow 2 Matrix.PSL3Two.PSL := default
  obtain ⟨P,hP⟩ := Sylow.mapSurjective_surjective hg 2 R
  let : IsMulCommutative P := Theory.PSL2.binary_sylow_commutative_of_injective
    (e.toMonoidHom.comp U.subtype) (e.injective.comp U.subtype_injective) P
  have hc : IsMulCommutative ((P : Subgroup U).map g) := map_isMulCommutative _ _
  have he : (P : Subgroup U).map g = (R : Subgroup Matrix.PSL3Two.PSL) :=
    congrArg (fun S : Sylow 2 Matrix.PSL3Two.PSL => (S : Subgroup Matrix.PSL3Two.PSL)) hP
  let : IsMulCommutative R := he ▸ hc
  obtain ⟨a⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral R
  have hh := congrArg a (mul_comm (a.symm (.sr (0 : ZMod 4))) (a.symm (.sr 1)))
  simp only [map_mul,MulEquiv.apply_symm_apply] at hh
  exact (by decide : (DihedralGroup.sr (0 : ZMod 4)) * .sr 1 ≠ .sr 1 * .sr 0) hh

/-- The original SL₃(2) section forces three to divide the ambient order,
excluding every positive-parameter Suzuki carrier. -/
theorem suzuki_no_section {Q : Type*} [Group Q] [Finite Q]
    {m : ℕ} (hm : 0 < m) (e : Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (U : Subgroup Q) (f : U →* BinaryLinearThree.Group) : ¬ Function.Surjective f := by
  intro hf
  have hd : 3 ∣ Nat.card Q := by
    apply dvd_trans ?_ ((card_dvd_of_surjective f hf).trans U.card_subgroup_dvd_card)
    rw [Matrix.PSL3Two.card_SL]
    decide
  rw [Nat.card_congr e.toEquiv] at hd
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm hd

/-- Only the unitary Bender row can retain the actual binary-three section. -/
theorem bender_unitary_of_section {Q : Type*} [Group Q] [Finite Q]
    (hm : IsBenderModel Q) (U : Subgroup Q) (f : U →* BinaryLinearThree.Group)
    (hf : Function.Surjective f) :
    ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU Q 3 (2^n) := by
  cases hm with
  | linear n hn he => exact (binary_linear_two_no_section he U f hf).elim
  | unitary n hn he => exact ⟨n,hn,he⟩
  | suzuki m hm he => exact (suzuki_no_section (by omega) he.some U f hf).elim

/-- Actual model markings surviving the rank and residual-section exclusions. -/
inductive RemainingPlacedModel (Q : Type*) [Group Q] : Prop
  | unitary_three (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSU Q 3 (2^n))
  | rank_two (f : ℕ) (iso : IsRankTwoModel Q f)
  | linear_five (iso : ClassicalGroup.IsPSL Q 5 2)
  | symplectic_six (iso : ClassicalGroup.IsPSp Q 3 2)
  | sporadic (name : SporadicName)
      (row : name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru)
      (iso : Nonempty (Q ≃* name.Carrier))

/-- Inspect the full Theorem B list using the whole rank-six orbit and
the actual residual section. Every surviving row retains its model marking. -/
theorem remaining_placed_models {Q : Type*} [Group Q] [Finite Q]
    (hr : 6 ≤ primeRank 2 Q) (hm : IsTheoremBModel Q)
    (hs : ∃ U : Subgroup Q, ∃ f : U →* BinaryLinearThree.Group, Function.Surjective f) :
    RemainingPlacedModel Q := by
  cases hm with
  | alternating n hn he =>
      obtain ⟨e⟩ := he
      rw [primeRank_equiv 2 e] at hr
      have := alternating_twoRank_le_four hn
      omega
  | odd hm => exact (DoubledBinaryOddRanks.no_odd_model_of_rank_six hr hm).elim
  | bender hm =>
      obtain ⟨U,f,hf⟩ := hs
      obtain ⟨n,hn,he⟩ := bender_unitary_of_section hm U f hf
      exact .unitary_three n hn he
  | rank_two f hm => exact .rank_two f hm
  | linear_binary n hn hm =>
      rcases hn with rfl | rfl
      · have := binary_linear_four_twoRank_le_four hm
        omega
      · exact .linear_five hm
  | symplectic_binary hm => exact .symplectic_six hm
  | sporadic hm =>
      obtain ⟨name,hn,he⟩ := sporadic_remaining_of_rank_six hr hm
      exact .sporadic name hn he

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedModels
