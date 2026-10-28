module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.G2Even.TwoRank.Elementary
public import Theory.SpecificGroups.G2Even.BinaryDerivedAutomorphismRank
public import Theory.SpecificGroups.PSL5Two.TwoRank
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# Small exceptional ranks in the enlargement sieve

The plane radical in Sp₄(4), the three commuting root groups in G₂(4),
and the 2-by-3 block transvections in PSL₅(2) give rank at least six.
All transports use the actual field and group equivalences in the source
model predicates. The genuine binary derived symplectic group is identified
with A₆ by the polar representation. The genuine PSU₃(3)–G₂(2)′ comparison
supplies the other smaller endpoint's automorphism bound. Faithful descent
through the centers handles perfect central covers, completing all three
rank-six contradictions. The required bounds concern two-rank; the printed
three-rank assertion is not used.

Source: Aschbacher–Smith, 16.1.4 and 16.1.7(3a,e), printed pp.1171–1172,
and the exceptional paragraph of 16.3.9, printed p.1180.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.SmallExceptions

namespace SymplecticFour

/-- The rank-six plane-radical witness in the actual projective group. -/
theorem psp4_four_two_rank {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) : 6 ≤ primeRank 2 (ClassicalGroup.PSp 2 F) :=
  (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.projective_rank
    (n := 2) hF (by decide)).ge

theorem psp4_four_two_rank_of_equiv {M F : Type*} [Group M] [Finite M]
    [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : M ≃* ClassicalGroup.PSp 2 F) : 6 ≤ primeRank 2 M := by
  rw [primeRank_equiv 2 e]
  exact psp4_four_two_rank hF

end SymplecticFour

namespace G2

/-- Three commuting root groups in the actual octonion model. -/
theorem g2_four_two_rank {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) : 6 ≤ primeRank 2 (Atlas.G2.Model F) :=
  Atlas.G2.EvenTwoRank.rank_ge F (n := 2) hF

theorem g2_four_two_rank_of_equiv {M F : Type*} [Group M] [Finite M]
    [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : M ≃* Atlas.G2.Model F) : 6 ≤ primeRank 2 M := by
  rw [primeRank_equiv 2 e]
  exact g2_four_two_rank hF

end G2

namespace PSL5

/-- The block-transvection witness in the actual binary projective group. -/
theorem psl5_two_rank :
    6 ≤ primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
  Theory.SpecificGroups.PSL5Two.six_le_primeRank

theorem psl5_two_rank_of_equiv {M F : Type*} [Group M] [Finite M]
    [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) :
    6 ≤ primeRank 2 M := by
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.PSL5Two.six_le_primeRank_of_card_two hF

end PSL5

variable {M : Type*} [Group M] [Finite M]

/-- Transport through the source's symplectic field witness. -/
theorem symplectic_four_rank (hM : ClassicalGroup.IsPSp M 2 4) :
    6 ≤ primeRank 2 M := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM
  exact SymplecticFour.psp4_four_two_rank_of_equiv hF e

/-- Transport through the source's octonion field witness. -/
theorem g2_four_rank (hM : ClassificationModels.IsG2At M 4) :
    6 ≤ primeRank 2 M := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM
  exact G2.g2_four_two_rank_of_equiv hF e

/-- Transport through the source's binary linear field witness. -/
theorem linear_five_rank (hM : ClassicalGroup.IsPSL M 5 2) :
    6 ≤ primeRank 2 M := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM
  exact PSL5.psl5_two_rank_of_equiv hF e

/-- The full automorphism group of A₆ has two-rank at most three. -/
theorem alternating_six_automorphism_two_rank :
    primeRank 2 (MulAut (alternatingGroup (Fin 6))) ≤ 3 :=
  CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank

theorem alternating_six_automorphism_two_rank_of_equiv
    (e : M ≃* alternatingGroup (Fin 6)) : primeRank 2 (MulAut M) ≤ 3 := by
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact alternating_six_automorphism_two_rank

/-- Faithful descent handles an actual perfect central cover of A₆. -/
theorem alternating_six_cover_automorphism_two_rank [IsQuasisimple M]
    (e : (M ⧸ center M) ≃* alternatingGroup (Fin 6)) :
    primeRank 2 (MulAut M) ≤ 3 :=
  CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.cover_automorphism_two_rank e

omit [Finite M] in
/-- Restrict the actual projective symplectic equivalence to commutators;
the polar representation identifies this derived group with A₆. -/
theorem symplectic_binary_derived_equiv (hM : ClassicalGroup.IsPSp M 2 2) :
    Nonempty (commutator M ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card (f := 1) hF
  let f := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  let d : commutator M ≃* commutator (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    (f.subgroupMap _).trans (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective, ← commutator_def]))
  exact ⟨d.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF)⟩

/-- The source's actual smaller derived symplectic endpoint, including its
permitted central cover, satisfies the required automorphism bound. -/
theorem symplectic_binary_derived_cover_automorphism_two_rank
    {D : Type*} [Group D] (hD : ClassicalGroup.IsPSp D 2 2) [IsQuasisimple M]
    (e : (M ⧸ center M) ≃* commutator D) : primeRank 2 (MulAut M) ≤ 3 := by
  obtain ⟨d⟩ := symplectic_binary_derived_equiv hD
  exact alternating_six_cover_automorphism_two_rank (e.trans d)

omit [Finite M] in
/-- Coefficient transport restricts to the actual binary G₂ commutator,
without identifying that proper subgroup with the full group. -/
theorem g2_binary_derived_equiv (hM : ClassificationModels.IsG2At M 2) :
    Nonempty (commutator M ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM
  let ef := Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F hF
  let f := e.trans (Atlas.G2.fieldEquiv ef)
  exact ⟨(f.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective, ← commutator_def]))⟩

/-- The actual binary G₂ commutator, via its genuine PSU₃(3) comparison. -/
theorem g2_binary_derived_automorphism_two_rank :
    primeRank 2 (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) ≤ 3 :=
  Atlas.G2.binary_derived_automorphism_two_rank_le_three

/-- Transfer a binary-derived automorphism bound to the source's perfect
central cover, using the intrinsic bound above in the next theorem. -/
theorem g2_binary_derived_cover_automorphism_two_rank_of_bound
    (hAut : primeRank 2 (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) ≤ 3)
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2) [IsQuasisimple M]
    (e : (M ⧸ center M) ≃* commutator D) : primeRank 2 (MulAut M) ≤ 3 := by
  obtain ⟨d⟩ := g2_binary_derived_equiv hD
  have hr := automorphism_primeRank_le_quotient_center (E := M) 2
  rw [primeRank_equiv 2 (MulAut.congr (e.trans d))] at hr
  exact hr.trans hAut

/-- Every source-permitted perfect central cover of G₂(2)′ inherits the
proved automorphism two-rank bound. -/
theorem g2_binary_derived_cover_automorphism_two_rank
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2) [IsQuasisimple M]
    (e : (M ⧸ center M) ≃* commutator D) : primeRank 2 (MulAut M) ≤ 3 :=
  g2_binary_derived_cover_automorphism_two_rank_of_bound
    g2_binary_derived_automorphism_two_rank hD e

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The Sp₄(4) exceptional case is impossible once its actual A₆ quotient
identification is supplied by the field-pair classification. -/
theorem exclude_symplectic_four
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : ClassicalGroup.IsPSp (enlargement t L) 2 4)
    (eL : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) : False := by
  let := h.localSetup.component.quasisimple
  exact exclude_rank_six h hs (symplectic_four_rank hK)
    (alternating_six_cover_automorphism_two_rank eL)

/-- Same exclusion with the smaller endpoint retained literally as the
derived group of the source's binary projective symplectic model. -/
theorem exclude_symplectic_four_field_pair
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : ClassicalGroup.IsPSp (enlargement t L) 2 4)
    {D : Type*} [Group D] (hD : ClassicalGroup.IsPSp D 2 2)
    (eL : (L ⧸ center L) ≃* commutator D) : False := by
  obtain ⟨d⟩ := symplectic_binary_derived_equiv hD
  exact exclude_symplectic_four h hs hK (eL.trans d)

/-- The PSL₅(2), A₆ graph pair of 16.1.7(3e) is excluded. -/
theorem exclude_linear_five
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : ClassicalGroup.IsPSL (enlargement t L) 5 2)
    (eL : L ≃* alternatingGroup (Fin 6)) : False :=
  exclude_rank_six h hs (linear_five_rank hK)
    (alternating_six_automorphism_two_rank_of_equiv eL)

/-- The G₂(4) field-pair exclusion with its numerical input explicit. -/
theorem exclude_g2_four_field_pair_of_bound
    (hAut : primeRank 2 (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) ≤ 3)
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : ClassificationModels.IsG2At (enlargement t L) 4)
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2)
    (eL : (L ⧸ center L) ≃* commutator D) : False := by
  let := h.localSetup.component.quasisimple
  exact exclude_rank_six h hs (g2_four_rank hK)
    (g2_binary_derived_cover_automorphism_two_rank_of_bound hAut hD eL)

/-- The G₂(4) field pair is excluded by the proved intrinsic ranks of its
actual octonion group and binary derived endpoint. -/
theorem exclude_g2_four_field_pair
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : ClassificationModels.IsG2At (enlargement t L) 4)
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2)
    (eL : (L ⧸ center L) ≃* commutator D) : False :=
  exclude_g2_four_field_pair_of_bound g2_binary_derived_automorphism_two_rank
    h hs hK hD eL

omit [Finite G] in
private theorem centerless_of_simple_component
    (hK : IsCentralizerComponent t (enlargement t L))
    [IsSimpleGroup (enlargement t L)] : center (enlargement t L) = ⊥ := by
  let := hK.quasisimple
  rcases (inferInstance : (center (enlargement t L)).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative (enlargement t L)
      (center_eq_top_iff.mp ht)).elim

/-- A simple enlargement is genuinely equivalent to its central quotient;
this supplies the whole-group model required by the rank calculation. -/
theorem exclude_simple_symplectic_four_quotient
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    [IsSimpleGroup (enlargement t L)]
    (hmodel : ClassicalGroup.IsPSp
      (enlargement t L ⧸ center (enlargement t L)) 2 4)
    {D : Type*} [Group D] (hD : ClassicalGroup.IsPSp D 2 2)
    (eL : (L ⧸ center L) ≃* commutator D) : False := by
  let e := (QuotientGroup.quotientMulEquivOfEq
    (centerless_of_simple_component hK)).trans QuotientGroup.quotientBot
  exact exclude_symplectic_four_field_pair h hs (hmodel.of_mulEquiv e.symm) hD eL

/-- The same centerless quotient transport for G₂(4), with the numerical
input explicit. -/
theorem exclude_simple_g2_four_quotient_of_bound
    (hAut : primeRank 2 (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) ≤ 3)
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    [IsSimpleGroup (enlargement t L)]
    (hmodel : ClassificationModels.IsG2At
      (enlargement t L ⧸ center (enlargement t L)) 4)
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2)
    (eL : (L ⧸ center L) ≃* commutator D) : False := by
  let e := (QuotientGroup.quotientMulEquivOfEq
    (centerless_of_simple_component hK)).trans QuotientGroup.quotientBot
  exact exclude_g2_four_field_pair_of_bound hAut h hs (hmodel.of_mulEquiv e.symm) hD eL

/-- The simple G₂(4) central-quotient case, with both intrinsic rank bounds
discharged and the smaller derived carrier retained literally. -/
theorem exclude_simple_g2_four_quotient
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    [IsSimpleGroup (enlargement t L)]
    (hmodel : ClassificationModels.IsG2At
      (enlargement t L ⧸ center (enlargement t L)) 4)
    {D : Type*} [Group D] (hD : ClassificationModels.IsG2At D 2)
    (eL : (L ⧸ center L) ≃* commutator D) : False :=
  exclude_simple_g2_four_quotient_of_bound g2_binary_derived_automorphism_two_rank
    h hs hK hmodel hD eL

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.SmallExceptions
