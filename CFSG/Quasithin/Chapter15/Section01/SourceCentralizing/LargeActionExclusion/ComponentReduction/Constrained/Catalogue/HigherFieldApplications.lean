module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeparation
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.G2
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Triality

/-!
# Original G₂ and triality exclusions from the actual nonblock residuals

The original rank-one nonblock theorem is transported from SL₂ to the
literal PSL₂ core quotients of the constructed parabolic residuals. Their
non-short property excludes chi-blocks; the marked residual escaping M_Z
therefore contradicts nonblock placement.

Both original G₂ alternatives are excluded, including the retained G₂(4)
central covers, and the triality residual of field degree n or 3n gives the
same contradiction. These applications use the independently constructed
parabolics, their local-family membership and their exact quotient maps.
They retain the original pre-exclusion prime; no exchanged selection is used.
Source: Aschbacher--Smith 15.1.20(3), printed p.1096. The model constructions
and exceptional-family assembly belong to qt-e-15122-ordinary-pre-exclusion;
the common nonblock theorem belongs to this constrained catalogue.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels Triality.Standard
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The PSL₂ form consumed by the actual higher-field residual constructions. -/
theorem localFamily_nonshort_PSL2_le_MZ (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hf : generalizedFitting K = pCore 2 K) (hnot : ¬ ChapterC.IsShort K)
    (n : ℕ) (hn : 1 < n) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n)) :
    K ≤ d.MZ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 3 < Nat.card F := by
    rw [hF]
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    omega
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toIsPerfect := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hfour
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega) }
  let e0 : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  have hq : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e0.symm
  exact d.localFamily_nonblock_le_MZ hG hempty hM hJ hu h hK hq hf
    (fun hb => hnot hb.short) F e0

variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}

/-- Exclude both ordinary higher-field G₂ rows, including the central G₂(4) cover,
using the literal parabolic residual furnished by the original source. -/
theorem PreExclusionSource.not_higherField_G2
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (n : ℕ) (hn : 1 < n) :
    ¬ (IsG2At d.L (2^n) ∨ IsG2At (d.L ⧸ pCore 2 d.L) (2^n)) := by
  intro hm
  obtain ⟨P,K,_,_,_,_,hK,hf,hnot,hout,hq⟩ :=
    s.g2_escaping_nonblock (h := h) hG hL n hn hm
  exact hout (d.localFamily_nonshort_PSL2_le_MZ hG hempty hM hJ hu h hK hf hnot n hn hq)

/-- The actual triality residual of degree n or 3n contradicts original nonblock placement. -/
theorem PreExclusionSource.not_higherField_triality
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (n : ℕ) (hn : 1 < n) :
    ¬ IsTrialityGroupAt (2^n) d.L := by
  intro hm
  obtain ⟨P,K,_,_,_,hK,hf,hnot,hout,m,hm,hq⟩ :=
    s.triality_escaping_nonblock (h := h) hG hL n hn hm
  exact hout (d.localFamily_nonshort_PSL2_le_MZ hG hempty hM hJ hu h hK hf hnot m hm hq)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
