module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CardinalControl

/-!
# The actual cores in the cubic A₅ branch

Mutual containment would generate Zα from two conjugate beta centers of
order at most four, contrary to |Zα| = 8 |Zβ|. Thus Zβ escapes a conjugate
beta core. Both it and the neighboring-core intersection have index two
over their identical intersection with that core. This proves Iβ = Zβ;
the existing cardinal comparison then proves Qα = Zα.

The source seed-generation identity consequently gives Qβ = Vβ. Its
Frattini and derived subgroups coincide and lie in Zβ, so Qβ has class at
most two. These conclusions no longer assume vanishing of the remaining
center layer. They do not yet prove |Zβ| = 2 or the full Chapter 11 profiles.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3), (11.6), (11.7)(e), printed pp.168--175.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem card_sup_le_mul (A B : Subgroup G) [Finite A] [Finite B]
    (hn : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  let m : A × B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.property p.2.property⟩
  have hs : Function.Surjective m := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hn]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext he⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective m hs

/-- Some conjugate beta core fails to contain the actual beta center. -/
theorem source_cubic_a5_center_escape (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    ∃ t ∈ stabilizer (family P) a, t • b ≠ b ∧ ¬ Z (family P) b ≤ Q (family P) (t • b) := by
  classical
  let := finite_endpoints h
  let : Finite (Z (family P) b) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  let : Finite (Z (family P) (g • b)) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ (g • b))) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hga' : g • a = a := hga
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [hga'] at hh
  have hbc' : (graph (family P)).Adj (g • b) (g • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc
  have hac' : a ≠ g • c := by
    intro he
    apply hac
    have hh := congrArg (fun v => g⁻¹ • v) he
    rwa [←hga',inv_smul_smul,inv_smul_smul] at hh
  by_cases hf : Z (family P) b ≤ Q (family P) (g • b)
  · refine ⟨g⁻¹,inv_mem hga,?_,?_⟩
    · intro he
      apply hgb
      have hh := congrArg (fun v => g • v) he
      simpa using hh.symm
    · intro hr
      have hback := map_mono (f := (MulAut.conj g).toMonoidHom) hr
      rw [←Z_translate,←Q_translate,smul_inv_smul] at hback
      have hspan := source_cubic_a5_center_pair_span_of_mutual h hB hS hc hb hcomm
        hbc hac hcard e g hga hgb hf hback
      have hZI := source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm
      have hJ := (source_cubic_a5_intersection_layer h hB hS hc hb hcard e hab'
        (Ne.symm hgb) hbc' hac').2
      let : Finite (neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) : Subgroup G) :=
        Finite.of_injective (inclusion (inf_le_right.trans (Q_le_stabilizer _ (g • b))))
          (inclusion_injective _)
      have hsmall : Nat.card (Z (family P) b) ≤ 4 :=
        (Nat.card_le_card_of_injective (inclusion (le_inf hZI hf)) (inclusion_injective _)).trans hJ
      have hZba := source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
      have hZb'a : Z (family P) (g • b) ≤ Z (family P) a := by
        have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hZba
        rwa [←Z_translate,←Z_translate,hga'] at hh
      have hnorm : Z (family P) (g • b) ≤ normalizer (Z (family P) b : Set G) :=
        ((hZb'a.trans ((source_Z_Q_U h a).1.trans (map_subtype_le _))).trans
          ((source_core_centralizes_center h a).trans (centralizer_le hZba))).trans
          (Subgroup.centralizer_le_normalizer _)
      have hbound := card_sup_le_mul (Z (family P) b) (Z (family P) (g • b)) hnorm
      rw [←hspan,Z_translate,card_map_of_injective (MulAut.conj g).injective] at hbound
      have hratio := source_cubic_a5_center_card_ratio h hB hS hc hb hcomm hbc hac hcard e
      have hpos : 0 < Nat.card (Z (family P) b) := Nat.card_pos
      nlinarith
  · exact ⟨g,hga,hgb,hf⟩

/-- The neighboring-core intersection equals Zβ without a layer-vanishing premise. -/
theorem source_cubic_a5_neighbor_intersection_eq_center (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b = Z (family P) b := by
  let := finite_endpoints h
  obtain ⟨t,hta,htb,hesc⟩ := source_cubic_a5_center_escape h hB hS hc hb hcomm hbc hac hcard e
    g hga hgb
  let I := neighborCoreIntersection (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (t • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) t).map_adj_iff.mpr hab
    change (graph (family P)).Adj (t • a) (t • b) at hh
    rwa [show t • a = a from hta] at hh
  have hcard' : Nat.card ((graph (family P)).neighborSet (t • b)) = 3 :=
    (Nat.card_congr ((Subgroup.CosetGeometry.translationGraphIso (family P) t).mapNeighborSet b)).symm.trans hcard
  have hZI := source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm
  have hIa : I ≤ Q (family P) a := neighborCoreIntersection_le _ hab
  have hpI : IsPGroup 2 I := (isPGroup_pCoreIn 2 _).to_le hIa
  have hpZ : IsPGroup 2 (Z (family P) b) := hpI.to_le hZI
  have hIG : I ≤ stabilizer (family P) (t • b) := hIa.trans ((source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab').trans inf_le_right))
  have hSyl := source_kernel_sylow h hB hS (t • b)
  have hescZ : ¬ Z (family P) b ≤ U (family P) (t • b) := fun hh =>
    hesc (CommutingTrivial.two_subgroup_le_Q (family P) (t • b) hSyl hpZ hh)
  have hescI : ¬ I ≤ U (family P) (t • b) := fun hh => hescZ (hZI.trans hh)
  have hiZ := source_cubic_two_subgroup_index h (t • b) (Z (family P) b) hpZ
    (hZI.trans hIG) hescZ hcard' hSyl
  have hiI := source_cubic_two_subgroup_index h (t • b) I hpI hIG hescI hcard' hSyl
  have he : I ⊓ Q (family P) (t • b) = Z (family P) b ⊓ Q (family P) (t • b) :=
    le_antisymm (le_inf (source_cubic_a5_layer_le_center h hB hS hc hb hbc hac hcard e t hta htb)
      inf_le_right) (inf_le_inf_right _ hZI)
  rw [he] at hiI
  have hind := relIndex_mul_relIndex (Z (family P) b ⊓ Q (family P) (t • b))
    (Z (family P) b) I inf_le_left hZI
  rw [hiI,hiZ] at hind
  exact le_antisymm ((relIndex_eq_one).mp (by omega : (Z (family P) b).relIndex I = 1)) hZI

/-- The alpha core is exactly its elementary center layer. -/
theorem source_cubic_a5_core_eq_center (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Q (family P) a = Z (family P) a :=
  source_cubic_a5_core_eq_center_of_intersection h hB hS hc hb hcomm hbc hac hcard e
    (source_cubic_a5_neighbor_intersection_eq_center h hB hS hc hb hcomm hbc hac hcard e g hga hgb)

/-- The corrected Vβ is the entire beta core, with its actual Frattini and derived layers. -/
theorem source_cubic_a5_beta_core_structure (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ∧
      betaSpan (stabilizer (family P) b) (Z (family P) a) = Q (family P) b ∧
      (frattini (Q (family P) b)).map (Q (family P) b).subtype =
        ⁅Q (family P) b,Q (family P) b⁆ ∧
      ⁅Q (family P) b,Q (family P) b⁆ ≤ Z (family P) b ∧
      ⁅⁅Q (family P) b,Q (family P) b⁆,Q (family P) b⁆ = ⊥ := by
  let := finite_endpoints h
  let : Finite (Q (family P) b) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  let := source_center_elementary h a
  let := source_center_elementary h c
  have hQa := source_cubic_a5_core_eq_center h hB hS hc hb hcomm hbc hac hcard e g hga hgb
  have hgen := source_cubic_a5_core_generation h hB hS hc hb hbc hac hcard e
  have hpair := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _ hgen hQa
  have hab := source_critical_one_adjacent hc hb
  have hs := pairSpan_commutator_frattini (Z (family P) a) (Z (family P) c) (Q (family P) b)
    (isPGroup_pCoreIn 2 _) (source_adjacent_core_normalizes_center h hab)
    (source_adjacent_core_normalizes_center h hbc.symm)
  rw [←hpair] at hs
  exact ⟨hpair,source_betaSpan_eq_core_of_pairSpan h hab hbc hpair.symm,
    hs.2.1.trans hs.1.symm,hs.2.2.1.trans
      (source_cubic_a5_center_intersection h hB hS hc hb hcomm hbc hac hcard e).le,hs.2.2.2⟩

/-- Cubic escape bounds the beta center by eight and the alpha center by 64. -/
theorem source_cubic_a5_center_card_bounds (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (Z (family P) b) ≤ 8 ∧ Nat.card (Z (family P) a) ≤ 64 := by
  let := finite_endpoints h
  obtain ⟨t,hta,htb,hesc⟩ := source_cubic_a5_center_escape h hB hS hc hb hcomm hbc hac hcard e
    g hga hgb
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (t • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) t).map_adj_iff.mpr hab
    change (graph (family P)).Adj (t • a) (t • b) at hh
    rwa [show t • a = a from hta] at hh
  have hbc' : (graph (family P)).Adj (t • b) (t • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) t).map_adj_iff.mpr hbc
  have hac' : a ≠ t • c := by
    intro he
    apply hac
    have hh := congrArg (fun v => t⁻¹ • v) he
    rwa [←show t • a = a from hta,inv_smul_smul,inv_smul_smul] at hh
  have hcard' : Nat.card ((graph (family P)).neighborSet (t • b)) = 3 :=
    (Nat.card_congr ((Subgroup.CosetGeometry.translationGraphIso (family P) t).mapNeighborSet b)).symm.trans hcard
  have hZi := source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm
  have hp : IsPGroup 2 (Z (family P) b) := (isPGroup_pCoreIn 2 _).to_le
    (hZi.trans (neighborCoreIntersection_le _ hab))
  have hZG : Z (family P) b ≤ stabilizer (family P) (t • b) :=
    (hZi.trans (neighborCoreIntersection_le _ hab)).trans ((source_Z_Q_U h a).2.trans
      ((ballKernel_one_le_edge _ hab').trans inf_le_right))
  have hSyl := source_kernel_sylow h hB hS (t • b)
  have hindex := source_cubic_two_subgroup_index h (t • b) (Z (family P) b) hp hZG
    (fun hh => hesc (CommutingTrivial.two_subgroup_le_Q (family P) (t • b) hSyl hp hh)) hcard' hSyl
  have hlayer := (source_cubic_a5_intersection_layer h hB hS hc hb hcard e hab'
    (Ne.symm htb) hbc' hac').2
  rw [source_cubic_a5_neighbor_intersection_eq_center h hB hS hc hb hcomm hbc hac hcard e
    g hga hgb] at hlayer
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b ⊓ Q (family P) (t • b))
    (Z (family P) b) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex] at hcount
  have hratio := source_cubic_a5_center_card_ratio h hB hS hc hb hcomm hbc hac hcard e
  constructor <;> omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
