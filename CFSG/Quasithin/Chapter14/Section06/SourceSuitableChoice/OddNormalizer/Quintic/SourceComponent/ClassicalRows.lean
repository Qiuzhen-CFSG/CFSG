module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.SmallSieve
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import Theory.SpecificGroups.Classical.QuinticRankOne

/-!
# Field and small-automorphism restrictions on the escaping component

The literal first-factor action has order five on the C.2.7 star component.
This excludes G₂(2)′, whose full automorphism group has order 12096. Transport
of the actual five-rank bound through each classical marking restricts the
field degree. In the symplectic row we also identify the original intersection
with a full point or plane parabolic. In the G₂ row the same quintic actor has
field component of order five, and the original component has five-rank zero.

The reduced catalogue retains every other marked action and the full six-clause
B.5.1 conclusion. The terminal classical and small outer comparisons, exchanged
module geometry and final p=3 assembly remain with qt-e-14615-quintic-exclusion.
Earlier-source 14.6.12--14 discharge remains with qt-e-suitable-odd-normalizer.
No ordinary-centralizer residual identity is used.
Source: Aschbacher--Smith 14.6.15, printed p.1035, using B.5.1 and C.2.7.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))


/-- The binary derived G₂ model has no automorphism of order five. -/
theorem source_no_binary_g2_star
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : False := by
  obtain ⟨k,_,_,ha⟩ := source_component_star_quintic s d j
    (source_component_input s d j).normalizes
  have hd := ha ▸ orderOf_dvd_natCard (starComponentAction j.J (Mc.pCoreIn 2) k)
  rw [Nat.card_congr (MulAut.congr e).toEquiv] at hd
  have hc : Nat.card (MulAut (commutator (Atlas.G2.Model (ZMod 2)))) = 12096 :=
    (Nat.card_congr Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.toEquiv).symm.trans
      Atlas.G2.LieAutomorphismExtensions.card_binaryFull
  rw [hc] at hd
  norm_num at hd


/-- Five-rank is retained by the literal core-to-star quotient. -/
theorem source_component_star_rank_le_one :
    primeRank 5 (starImage j.J (Mc.pCoreIn 2) j.J) ≤ 1 := by
  rw [source_component_star_five_rank s d j (source_component_input s d j).normalizes]
  exact j.quintic_rank

/-- The actual linear-three row cannot have field degree divisible by four. -/
theorem source_component_linear_degree (F : BinaryField)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* SL(3,F.Carrier)) :
    ¬4 ∣ F.degree := by
  apply Theory.SpecificGroups.Classical.QuinticRankOne.linear_degree F.card_eq
  rw [←primeRank_congr 5 e]
  exact source_component_star_rank_le_one s d j

/-- The symplectic row has odd degree and its original intersection is a full
point or plane parabolic under the same component marking. -/
theorem source_component_symplectic_marked_parabolic (F : BinaryField)
    (hlarge : 1 < F.degree)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) :
    Odd F.degree ∧
      ∃ g : Matrix.symplecticGroup (Fin 2) F.Carrier,
        (((starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf
          (starImage j.J (Mc.pCoreIn 2) j.J)).map e.toMonoidHom).map
            (MulAut.conj g).toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointParabolic ∨
        (((starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf
          (starImage j.J (Mc.pCoreIn 2) j.J)).map e.toMonoidHom).map
            (MulAut.conj g).toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeParabolic := by
  constructor
  · apply Theory.SpecificGroups.Classical.QuinticRankOne.symplectic_degree F.card_eq
    rw [←primeRank_congr 5 e]
    exact source_component_star_rank_le_one s d j
  · apply star_symplectic_marked_parabolic_from_source (source_component_input s d j) e
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hlarge

/-- A nonbinary G₂ row has rank zero at five. The original first-factor
quintic has field component of order five on this literal model, forcing
an odd field degree divisible by five. -/
theorem source_component_g2_quintic_field (F : BinaryField)
    (hlarge : 1 < F.degree)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* Atlas.G2.Model F.Carrier) :
    Odd F.degree ∧ 5 ∣ F.degree ∧ primeRank 5 j.J = 0 ∧
      ∃ (hq : 2 < Nat.card F.Carrier)
        (k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G)),
        (k : G) ∈ d.K1 ∧ orderOf k = 5 ∧
        orderOf (Atlas.G2.LieAutomorphismExtensions.fieldComponent hq
          (MulAut.congr e (starComponentAction j.J (Mc.pCoreIn 2) k))) = 5 := by
  have hi := source_component_input s d j
  obtain ⟨k,hk,ho,ha⟩ := source_component_star_quintic s d j hi.normalizes
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hh : 2^2 ≤ 2^F.degree := Nat.pow_le_pow_right (by decide) hlarge
    omega
  have hr : primeRank 5 (Atlas.G2.Model F.Carrier) ≤ 1 := by
    rw [←primeRank_congr 5 e]
    exact source_component_star_rank_le_one s d j
  have ha' : orderOf (MulAut.congr e (starComponentAction j.J (Mc.pCoreIn 2) k)) = 5 :=
    ((MulAut.congr e).orderOf_eq _).trans ha
  obtain ⟨hn,hd,hf⟩ := Theory.SpecificGroups.Classical.QuinticRankOne.g2_quintic_field
    F.card_eq hq hr _ ha'
  refine ⟨hn,hd,?_,hq,k,hk,ho,hf⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [←source_component_star_five_rank s d j hi.normalizes,primeRank_congr 5 e]
  exact PrimeRank.eq_zero_iff_not_dvd_card.mpr
    (Theory.SpecificGroups.Classical.QuinticRankOne.g2_five_not_dvd F.card_eq hn)


/-- The remaining actual moved-section models, now with their necessary
field restrictions. The small outer rows retain the full action markings. -/
inductive ClassicalQuinticRow {D : Type*} [Group D]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop
  | linearThree (F : BinaryField) (degree : ¬4 ∣ F.degree) (e : L ≃* SL(3,F.Carrier))
  | symplectic (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | symplecticTwo (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
      (symplecticNatural (k := ZMod 2) 2)
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
  | g2 (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (field_five : 5 ∣ F.degree) (e : L ≃* Atlas.G2.Model F.Carrier)
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7 ∨ n = 8)
      (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
        (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
  | binaryFive (e : L ≃* SL(5,ZMod 2))

private theorem classical_rows {D : Type*} [Group D]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (h : RemainingQuinticRow ρ L)
    (hl : ∀ F : BinaryField, (L ≃* SL(3,F.Carrier)) → ¬4 ∣ F.degree)
    (hs : ∀ F : BinaryField, 1 < F.degree →
      (L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) → Odd F.degree)
    (hg : ∀ F : BinaryField, 1 < F.degree →
      (L ≃* Atlas.G2.Model F.Carrier) → Odd F.degree ∧ 5 ∣ F.degree)
    (hb : (L ≃* commutator (Atlas.G2.Model (ZMod 2))) → False) :
    ClassicalQuinticRow ρ L := by
  cases h with
  | linearThree F e => exact .linearThree F (hl F e) e
  | symplectic F hF e => exact .symplectic F hF (hs F hF e) e
  | symplecticTwo e => exact .symplecticTwo e
  | g2 F hF e => exact .g2 F hF (hg F hF e).1 (hg F hF e).2 e
  | g2Two e => exact (hb e.subgroupEquiv).elim
  | symmetric n hn e => exact .symmetric n hn e
  | binaryFive e => exact .binaryFive e

/-- Apply the field and automorphism restrictions to the same full source
conclusion, without replacing its marked small outer alternatives. -/
theorem source_component_classical_row_reduction
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation j.J (Mc.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) :
    ClassicalQuinticRow c.sectionData.action
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  apply classical_rows _ _ (source_component_moved_row_reduction s d j hCJ c)
  · intro F e
    exact source_component_linear_degree s d j F ((subgroupOfEquivOfLe hCJ).symm.trans e)
  · intro F hl e
    exact (source_component_symplectic_marked_parabolic s d j F hl
      ((subgroupOfEquivOfLe hCJ).symm.trans e)).1
  · intro F hl e
    have hh := source_component_g2_quintic_field s d j F hl
      ((subgroupOfEquivOfLe hCJ).symm.trans e)
    exact ⟨hh.1,hh.2.1⟩
  · intro e
    exact source_no_binary_g2_star s d j ((subgroupOfEquivOfLe hCJ).symm.trans e)

/-- The literal escaping component supplies this restricted catalogue and
all six B.5.1 source clauses. No model-selection premise is added. -/
theorem source_component_classical_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
      ClassicalQuinticRow c.sectionData.action
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  have hi := source_component_input s d j
  have hc := star_moved_section_from_source hi
  let c := Classical.choice hc.2
  exact ⟨hc.1,c,source_component_classical_row_reduction s d j hc.1 c⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
