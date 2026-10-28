module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SmallAlphaExclusions

/-!
# Small alpha exclusions in the original reduced Chapter 11 geometry

The literal reduced triple and Borel Sylow supply the generic alpha
index-two obstruction. Thus the alpha local quotient cannot be D10,
and a supplied PSL2(2^n) marking has n > 1. The D10 exclusion also holds
for the image of that local group in the original completion: its
actual two-core quotient is transported by the induced isomorphism.

Earlier local data and the beta rank-one catalogue input remain explicit.
These results select neither the remaining alpha rows nor the full
Chapter 11 profiles, and impose no new beta-center order assumption.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(f), (11.5), printed pp.169--172; reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

private theorem linear_coordinates_card {H : Type*} [Group H] {n : ℕ}
    (hM : ClassicalGroup.IsPSL H 2 (2 ^ n)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      Nat.card k = 2^n ∧ Nonempty (H ≃* SL(2,k)) := by
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := hM
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact ⟨k,hk,hfin,inferInstance,hcard,⟨e.trans f.symm⟩⟩

/-- The dihedral-ten alpha quotient is excluded on the actual reduced
source geometry, with no linear-alpha hypothesis or center-order premise. -/
theorem reduced_alpha_dihedral_exclusion (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* DihedralGroup 5) : False :=
  source_alpha_dihedral_exclusion (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac Mb ea

/-- A genuine alpha PSL2(2^n) marking has n > 1 in the commuting-one
branch. The exponent is the parameter of the supplied quotient marking. -/
theorem reduced_alpha_linear_parameter_gt_one (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (n : ℕ) (hn : 0 < n)
    (ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2 ^ n)) :
    1 < n := by
  obtain ⟨k,hk,hfin,hchar,hcard,⟨ea⟩⟩ := linear_coordinates_card ha
  have hne := source_alpha_linear_field_card_ne_two (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hcomm hbc hac Mb ea
  have hn1 : n ≠ 1 := by
    intro he
    apply hne
    simpa only [he,pow_one] using hcard
  omega

/-- The same dihedral exclusion after the literal inclusion of the local
source group into the original completion; the two-core quotient is transported
by its induced group isomorphism. -/
theorem reduced_original_alpha_dihedral_exclusion (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (((d.localGroup a).map (G₀).subtype) ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) ≃* DihedralGroup 5) : False := by
  let eL := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eq := QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  exact reduced_alpha_dihedral_exclusion h d hc hb hcomm hbc hac Mb (eq.trans ea)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
