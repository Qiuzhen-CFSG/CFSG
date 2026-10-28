module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels.Rows
public import Theory.Representation.HexacodeAction.CoverRecognition
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.Quasithin.Rank

/-!
# Recognition after exceptional-core exhaustion

Exhaustion makes the central-omega action faithful modulo O₂(M). The actual
component image is the marked perfect triple cover of A₆, hence the even
hexacode group. Apply the complete projective-line version of B.5.1 on the
best-offender subgroup. The existing order-1080 row comparison gives Irr+
and dimension six on the full moved space; its central denominator is zero.
The canonical moved-space equivalence transfers these conclusions to blockU.

Only the graph-theoretic exhaustion equality remains an input. Neither a
block predicate nor an assumed core dimension enters recognition.
Source: Aschbacher--Smith B.5.1, C.1.22, C.1.31--32 and K.1.3,
pp.99--103,129,135--136,453; MS93 Main Theorem (6), (3.2), (3.6).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Exceptional
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
universe u

/-- Recognition supplies irreducibility and dimension on the full moved space,
with the offender restriction transported through its literal inclusion. -/
private theorem moved_facts_of_ff
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    [(C).Normal] [IsQuasisimple C]
    (eC : C ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hquot : IsPGroup 2 (D ⧸ C)) (hcore : pCore 2 D = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ C) = 6 := by
  obtain ⟨hCJ, ⟨c⟩⟩ := SourceCompletion.ff_quasisimple_source_conclusion
    ρ C hquot hcore hsq hf hff
  let eB := (subgroupOfEquivOfLe hCJ).trans eC
  obtain ⟨hi, _, _, _, _, _⟩ := source_tripleSix _ c eB
  have hspace : c.sectionData.space.toSubmodule = subspaceCommutator ρ ⊤ C := by
    rw [c.sectionData.space_eq]
    change moved (ρ.comp (offenderSubgroup ρ).subtype)
      (C.subgroupOf (offenderSubgroup ρ)) = moved ρ C
    rw [moved_comp_map, map_subgroupOf_eq_of_le hCJ]
  have hi' := (IsIrrPlus.subgroupOf_iff ρ C (offenderSubgroup ρ) hCJ _).mp hi
  rw [hspace] at hi'
  refine ⟨hi', ?_⟩
  exact ((LinearEquiv.ofEq _ _ hspace).finrank_eq).symm.trans
    (source_moved_finrank _ c eB)

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "X" => centralOmega L R
local notation "C" => componentImage L R

include h e hz

/-- The given central marking is retained in the concrete triple-cover isomorphism. -/
theorem exists_quotient_hexacode_equiv :
    ∃ f : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      Atlas.Codes.hexEvenCoordinate.comp f.toMonoidHom =
        (SmallMSPair.alternatingCentralQuotientEquiv e).toMonoidHom.comp
          (QuotientGroup.mk' (center (L ⧸ pCore 2 L))) := by
  let := h.component_perfect
  let a := SmallMSPair.alternatingCentralQuotientEquiv e
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (center (L ⧸ pCore 2 L)))
  have hk : f.ker = center (L ⧸ pCore 2 L) := by
    ext x
    change a (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [← a.map_one, a.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  exact Hexacode.triple_cover_equiv f
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le (hk ▸ hz)

/-- Every module clause of the exceptional branch follows from the one source
exhaustion equality. The entire core, including its possible fixed layer, is counted. -/
theorem core_facts_of_exhaustion (hx : CoreExhaustion L R) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L := by
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  let q := QuotientGroup.mk' Q
  let ρ := initialAction h hx
  let : (C).Normal := (inferInstance : (K).Normal).map q (QuotientGroup.mk'_surjective Q)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component)
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  obtain ⟨a, _⟩ := exists_quotient_hexacode_equiv h e hz
  let eC : C ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (cComponentTwoCoreQuotientEquiv h.component).symm.trans
      ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans a)
  have hsup : C ⊔ (R.subgroupOf (L ⊔ R)).map q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q x
    obtain ⟨k, hk, r, hr, rfl⟩ := h.relative_product g
    rw [map_mul]
    exact mul_mem (mem_sup_left (mem_map_of_mem q hk))
      (mem_sup_right (mem_map_of_mem q hr))
  have hquot := isPGroup_quotient_of_sup_eq_top C
    ((R.subgroupOf (L ⊔ R)).map q) (h.relative_radical.isPGroup.map q) hsup
  have hsq : IsSQTK KnownSimple.IsKnownSimple (M ⧸ Q) := by
    refine ⟨?_, h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho Q pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  obtain ⟨hi, hd⟩ := moved_facts_of_ff ρ C eC hquot (pCore_quotient_pCore_eq_bot 2)
    (hsq.subgroup C) (initialAction_faithful h hx) (initialAction_isFFModule h hx)
  have hker : q.ker = centralizer (X : Set M) :=
    (QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h hx).symm
  have he := relative_core_eq h hx
  have hKi : BlockModuleIrreducible K :=
    BlockMovingSection.irreducible_of_moving X K q (QuotientGroup.mk'_surjective Q) hker he hi
  have hKe : IsElementaryAbelian 2 (blockU K) :=
    IsElementaryAbelian.of_le (relative_core_le_centralOmega h hx)
  have hKc : blockU K ≤ centralizer (pCore 2 K : Set K) := by
    intro k hk
    exact ((mem_omegaCenterIn_iff _ _).mp (relative_core_le_centralOmega h hx hk)).2.1
  have hs : IsShort K := ⟨inferInstance, h.relative_twoPerfect, relative_fitting h,
    hKe, hKc, Or.inl inferInstance, hKi⟩
  have hL := hs.of_mulEquiv f
  have hcardK : Nat.card (blockU K) = 2 ^ 6 := by
    let s := MovedSection.ofNormal ρ C
    let c := BlockMovingSection.coreEquiv X K q (QuotientGroup.mk'_surjective Q) hker he
    calc
      Nat.card (blockU K) = Nat.card (Multiplicative s.space.toSubmodule) := Nat.card_congr c.toEquiv
      _ = Nat.card s.space.toSubmodule := rfl
      _ = 2 ^ 6 := by
        rw [Module.natCard_eq_pow_finrank («K» := ZMod 2), Nat.card_zmod]
        exact congrArg (fun n => 2 ^ n) hd
  have hmap : (blockU K).map f.toMonoidHom = blockU L := by
    rw [blockU, blockU, map_commutator, pCore_map_iso, map_top_of_surjective _ f.surjective]
  have hcard : Nat.card (blockU L) = 2 ^ 6 := by
    rw [← hmap, card_map_of_injective f.injective, hcardK]
  exact ⟨hL.elementary, hL.central, hL.irreducible, hcard,
    le_antisymm (core_centralizer_le h) (le_centralizer_iff.mp hL.central)⟩

end AlternatingSixReconstruction.Exceptional
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
