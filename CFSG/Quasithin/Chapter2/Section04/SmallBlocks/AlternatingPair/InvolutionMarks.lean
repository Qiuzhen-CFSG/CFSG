module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Projection
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Centers

/-! The actual nontrivial Phi normalizer satisfies all hypotheses of 1.1.5.
The beta barrier places an ambient Sylow overgroup in the original M; its
central involution and uniqueness of M provide 1.1.6 with no extra marks.
Source: Aschbacher–Smith 2.4.25, printed p.542. -/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.phi_involution_marks
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∃ (P : Sylow 2 GI) (z : G), Chapter1.Lemma115Hypotheses GI P M z := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let F := Phi S L
  let GI := normalizer (F : Set G)
  have hb := (c.stabilizer_base hG T hM hTM hu hST hSM hMT hi).2.2.2
  have hRG : SI S L ≤ GI :=
    (normalizer_Phi_eq c.marked₁ c.marked₂).ge.trans inf_le_right
  obtain ⟨P,hRP,hPb⟩ := beta_exists_sylow hb hRG
  obtain ⟨R,hPR⟩ := (P.isPGroup'.map GI.subtype).exists_le_sylow
  have hRM : (R : Subgroup G) ≤ M := beta_overgroup_le hPb hPR R.isPGroup'
  have hFp : IsPGroup 2 F := c.marked₁.twoGroup.to_le
    (inf_le_left.trans ((P_le_I S L).trans (inf_le_left.trans inf_le_left)))
  have hF : F ≠ ⊥ := Phi_ne_bot c.marked₁ c.marked₂
  have hFR : F ≤ (R : Subgroup G) :=
    ((le_pCoreIn_of_normalizes hFp F.le_normalizer le_rfl).trans
      (pCoreIn_le_sylow GI P)).trans hPR
  have hR : (R : Subgroup G) ≠ ⊥ := fun he => hF (le_bot_iff.mp (hFR.trans he.le))
  let : Nontrivial (R : Subgroup G) := (nontrivial_iff_ne_bot _).mpr hR
  let : Nontrivial (center (R : Subgroup G)) := R.isPGroup'.center_nontrivial
  have hd : 2 ∣ Nat.card (center (R : Subgroup G)) := by
    rcases (R.isPGroup'.to_subgroup (center (R : Subgroup G))).card_eq_or_dvd with hh|hh
    · exact (ne_of_gt R.isPGroup'.bot_lt_center (Subgroup.card_eq_one.mp hh)).elim
    · exact hh
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G:=center (R:Subgroup G)) 2 hd
  have hz2 : orderOf ((z:(R:Subgroup G)):G) = 2 := by simpa only [orderOf_coe] using hz
  have hzc : ∀ x ∈ (R:Subgroup G), x * (z:G) = (z:G) * x := by
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp z.property ⟨x,hx⟩)
  have hCM : centralizer ({(z:G)}:Set G) ≤ M :=
    centralizer_le_of_M_central_involution T hTM hu hz2 (R.subtype hRM) (by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRM] using hzc)
  refine ⟨P,z,Chapter1.lemma_1_1_6 hF hFp F.le_normalizer
    (Subgroup.centralizer_le_normalizer _) le_rfl P R hPR hz2 z.val.property hzc hM hCM ?_⟩
  intro N hN hRN
  exact Chapter1.mem_He_iff.mpr (hG.evenCharacteristic R N hN hRN)

end CFSG.Quasithin.Chapter2
