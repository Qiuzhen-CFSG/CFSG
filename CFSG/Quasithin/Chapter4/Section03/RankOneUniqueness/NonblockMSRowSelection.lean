module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockMovedCenter
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSRadicalInequality

/-!
# Selecting the surviving original nonblock MS rows

For the exact five alternatives of C.1.34, a natural whole core makes the
original component a block. A natural moved center forces the whole fixed
factor to vanish in the original ambient configuration, excluding row (4)
without its ambient-centrality clause. The initial Sylow-omega calculation
excludes row (5). Thus only the doubled whole core and row (3) remain, with
the supplied full SL₃ marking and literal Sylow radical inequality retained.

The row-(3) consumer constructs MSData and simultaneous original parabolic
and Sylow markings. A nonabelian Q excludes the doubled row, and the final
application selects the actual normal secondary component and its quadratic
core layer. Neither a full MS classification nor nonabelianity is assumed
proved by these conditional reductions. The original doubled-row exclusion,
strict secondary-core enlargement and final nonblock assembly remain with
qt-d-1222-rankone-uniqueness-nonblock. Whole-core classification retains the
existing qt-c134-nonbinary-linear-three-source producer.

Source: Aschbacher--Smith C.1.34(1)--(5), pp.136--137, original 4.3.8--10,
pp.616--617, and the secondary-component construction in 4.3.11--14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- The exact original alternatives reduce to the two whole-section rows,
without any parabolic-placement or fixed-factor-centrality premise. -/
theorem source_module_alternatives_two_or_three
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    {n : ℕ} (hn : 1 < n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F e) :
    (HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)) ∧
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P) ∨
    (HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3) ∧
      HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
        ((Representation.specialLinearNatural (k := F) 3).dual.prod
          (Representation.specialLinearNatural (k := F) 3).dual) ∧
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  rcases hm with h₁ | h₂ | h₃ | h₄ | h₅
  · exact (hb (ms_block_of_natural_core c D hf n hn hF e (by
      simpa only [ms_commutator_eq] using h₁.2.2))).elim
  · exact Or.inl (by simpa only [ms_commutator_eq] using h₂)
  · exact Or.inr (by simpa only [ms_commutator_eq,
      show SourceInterface.centerIn (Q c) = U c from rfl] using h₃)
  · have hmoved : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := F) 3) := by
      simpa only [ms_commutator_eq,show SourceInterface.centerIn (Q c) = U c from rfl]
        using h₄.2.2.2.2.2.1
    have hcard : Nat.card (Q c ⊓ centralizer (K c : Set G) : Subgroup G) = 2^(2*n) := by
      simpa only [ms_commutator_eq] using h₄.2.1
    exact (MovedCenter.fixed_factor_card_ne D hf hn hF e hmoved hcard).elim
  · exact (ms_sylowOmega_not_central c D hf n hn hF e P hP h₅.2.2.2.1).elim

/-- The third surviving row supplies the original MS witness and both
markings. Its radical inequalities are derived for every eligible Sylow. -/
theorem source_doubled_or_msData
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) :
    (HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).prod
        (Representation.specialLinearNatural (k := F.Carrier) 3)) ∧
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P) ∨
    (∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) := by
  have hF : Nat.card F.Carrier = 2^n := F.card_eq.trans (congrArg (2^·) hdegree)
  rcases source_module_alternatives_two_or_three D hf hb hn hF e P hP hm with hd | ht
  · exact Or.inl hd
  · exact Or.inr (exists_msData_of_whole_caseThree D hf n hn F hdegree e ht.1 ht.2.1)

omit [Finite G] in
private theorem whole_section_commutative
    {B A F : Type*} [Group B] [AddCommGroup A] [Field F] [Module F A]
    {X Y : Subgroup G} {a : X →* B} {ρ : Representation F B A}
    (hm : HasSectionModel X Y ⊥ a ρ) : IsMulCommutative Y := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,e,_⟩ := hm
  let := hn
  let f : Y ≃* Multiplicative A := QuotientGroup.quotientBot.symm.trans e
  exact ⟨⟨fun x y => f.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩

/-- Nonabelianity of the actual Q selects row (3) and constructs its MS
data. Both the classification and nonabelianity remain explicit inputs. -/
theorem source_msData_of_nonabelian_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e)
    (hna : ¬ IsMulCommutative (Q c)) :
    ∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier := by
  exact (source_doubled_or_msData D hf hb n hn F hdegree e P hP hm).resolve_left
    (fun hd => hna (whole_section_commutative hd.1))

/-- Apply the selected row to the actual root normalizer and its original
normal component, retaining both subtype maps and the quadratic orbit. -/
theorem source_component_of_nonabelian_alternatives
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e)
    (hna : ¬ IsMulCommutative (Q c)) :
    ∃ B : Subgroup (rootNormalizer c),
      B.IsCComponent ∧ B.Normal ∧ IsQuasisimple (B ⧸ pCore 2 B) ∧
      secondary c < B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) ∧
      U c < rootCoreLayer c ∧
      rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ∧
      (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c ∧
      (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c ∧
      ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c := by
  obtain ⟨d,_,hL,_⟩ := source_msData_of_nonabelian_alternatives D hf hb n hn F hdegree
    e P hP hm hna
  exact d.exists_sourceComponent_of_line_marking hn D h hL

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
