module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonquadraticSeeds

/-!
# Escape of the beta center on an arbitrary alpha turn

The original beta center generates Z_alpha under the earlier local alpha
group, by common edge Sylows and Sylow-center generation. If two beta centers
on an alpha turn both lie in the opposite cores, the mixed intersection
identities make their join invariant under both opposite seeds and Q_alpha.
The local generation theorem therefore identifies this join with Z_alpha.

The opposite seed would then have all displacement on Z_alpha in Z_beta,
which it centralizes. This contradicts the proved nonquadratic action.
Consequently either the turn or its inverse gives an escaping beta center.
No cubic-degree assumption, center order or layer-vanishing premise is used.
The earlier local data and actual linear alpha marking remain explicit;
all beta catalogue rows are retained. Source: Delgado--Goldschmidt--
Stellmacher, Groups and Graphs (1985), proof of (11.6), printed p.173,
using (11.3)(f) and (11.5).
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem center_local_seed_span (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥) :
    conjugateSpanBy (Z (family P) b) (d.localGroup a) = Z (family P) a := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨T,R,hTR⟩ := d.common_sylow a b hab
  have hseed : omegaCenterIn ((T : Subgroup (stabilizer (family P) a)).map
      (stabilizer (family P) a).subtype) ≤ Z (family P) b := by
    rw [hTR]
    exact le_iSup (fun R : Sylow 2 (stabilizer (family P) b) => omegaCenterIn
      ((R : Subgroup (stabilizer (family P) b)).map (stabilizer (family P) b).subtype)) R
  have hZb := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    (d.localGroup b) (d.sylow_or_center b)
  have hZba : Z (family P) b ≤ Z (family P) a := by
    rw [hZb]
    exact local_omega_le_neighbor_Z h d hab.symm
  apply le_antisymm
  · exact conjugateSpanBy_le hZba ((d.local_le a).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a)))
  · have he := sylowCenterSpan_eq_conjugateSpan (stabilizer (family P) a)
      (d.localGroup a) (d.local_le a) (d.sylow_le a) T
    change Z (family P) a = _ at he
    rw [he]
    exact conjugateSpanBy_mono hseed le_rfl

private theorem core_le_neighbor (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    Q (family P) a ≤ stabilizer (family P) b :=
  (source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)

private theorem center_normalized (h : LocallyRankOneTriple P B) (a : Vertex (family P)) :
    stabilizer (family P) a ≤ normalizer (Z (family P) a : Set G) := by
  let := finite_endpoints h
  exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a)


/-- Mutual core containment forces the two beta centers to generate the alpha center. -/
theorem source_linear_rankOne_center_pair_span_of_mutual (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hforward : Z (family P) b ≤ Q (family P) (g • b))
    (hback : Z (family P) (g • b) ≤ Q (family P) b) :
    Z (family P) a = Z (family P) b ⊔ Z (family P) (g • b) := by
  let := finite_endpoints h
  have hi := (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).2.2.1
  obtain ⟨hp,hcore⟩ := source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea
  have hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
    rw [sup_comm]
    exact alpha_supplement_of_pair_generation _ _ _ _ _ hp hcore
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  let N := Z (family P) b ⊔ Z (family P) (g • b)
  let C := Z (family P) c ⊓ Q (family P) b
  let D := Z (family P) (g • c) ⊓ Q (family P) (g • b)
  have hab := source_critical_one_adjacent hc hb
  have hga' : g • a = a := hga
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [hga'] at hh
  have hZba := hi.ge.trans inf_le_left
  have hZb'a : Z (family P) (g • b) ≤ Z (family P) a := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hZba
    rwa [←Z_translate,←Z_translate,hga'] at hh
  have hNa : N ≤ Z (family P) a := sup_le hZba hZb'a
  have hCga : C ≤ stabilizer (family P) a := inf_le_right.trans (core_le_neighbor h hab.symm)
  have hDga : D ≤ stabilizer (family P) a := inf_le_right.trans (core_le_neighbor h hab'.symm)
  have hcross : ⁅Z (family P) (g • b),C⁆ ≤ Z (family P) b := by
    have h₁ : ⁅Z (family P) (g • b),C⁆ ≤ Z (family P) a :=
      (commutator_mono hZb'a le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hCga.trans (center_normalized h a)))
    have h₂ : ⁅Z (family P) (g • b),C⁆ ≤ Z (family P) c :=
      (commutator_mono hback inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp (source_adjacent_core_normalizes_center h hbc.symm))
    exact (le_inf h₁ h₂).trans hi.le
  have hcross' : ⁅Z (family P) b,D⁆ ≤ Z (family P) (g • b) := by
    have h₁ : ⁅Z (family P) b,D⁆ ≤ Z (family P) a :=
      (commutator_mono hZba le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hDga.trans (center_normalized h a)))
    have h₂ : ⁅Z (family P) b,D⁆ ≤ Z (family P) (g • c) :=
      (commutator_mono hforward inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp (source_adjacent_core_normalizes_center h
          ((Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc).symm))
    have he := congrArg (map (MulAut.conj g).toMonoidHom)
      hi
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Z_translate,←Z_translate,hga'] at he
    exact (le_inf h₁ h₂).trans he.le
  have hCN : C ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal N _ _ C N N.le_normalizer le_sup_left le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans ((Q_le_stabilizer _ b).trans (center_normalized h b)))).trans le_sup_left
    · exact hcross.trans le_sup_left
  have hDN : D ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal N _ _ D N N.le_normalizer le_sup_left le_sup_right
    · exact hcross'.trans le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans ((Q_le_stabilizer _ (g • b)).trans (center_normalized h (g • b))))).trans le_sup_right
  have hQaN : Q (family P) a ≤ normalizer (N : Set G) :=
    ((source_core_centralizes_center h a).trans (centralizer_le hNa)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnorm : d.localGroup a ≤ normalizer (N : Set G) := by
    rw [←source_rankOne_opposite_seed_generation h hB d hc hb hbc hac Ma Mb hsupp g hga hgb]
    exact sup_le (sup_le hCN hDN) hQaN
  apply le_antisymm _ hNa
  rw [←center_local_seed_span h d hc hb hcomm]
  exact conjugateSpanBy_le le_sup_left hnorm


/-- On every alpha turn, at least one orientation has the beta center
escaping the opposite beta core. This is the escape step in (11.6). -/
theorem source_linear_rankOne_center_escape (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    ∃ t ∈ stabilizer (family P) a, t • b ≠ b ∧
      ¬ Z (family P) b ≤ Q (family P) (t • b) := by
  classical
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  by_cases hf : Z (family P) b ≤ Q (family P) (g • b)
  · refine ⟨g⁻¹,inv_mem hga,?_,?_⟩
    · intro he
      apply hgb
      have hh := congrArg (fun v => g • v) he
      simpa using hh.symm
    · intro hr
      have hback := map_mono (f := (MulAut.conj g).toMonoidHom) hr
      rw [←Z_translate,←Q_translate,smul_inv_smul] at hback
      have hspan := source_linear_rankOne_center_pair_span_of_mutual h hB d hc hb hcomm
        hbc hac Ma Mb ea g hga hgb hf hback
      have hi := (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).2.2.1
      have hZba := hi.ge.trans inf_le_left
      have hZga : Z (family P) (g • b) ≤ Z (family P) a := by
        have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hZba
        rwa [←Z_translate,←Z_translate,show g • a = a from hga] at hh
      let C := Z (family P) c ⊓ Q (family P) b
      have hCga : C ≤ stabilizer (family P) a := inf_le_right.trans (core_le_neighbor h hab.symm)
      have hcross : ⁅Z (family P) (g • b),C⁆ ≤ Z (family P) b := by
        have h₁ : ⁅Z (family P) (g • b),C⁆ ≤ Z (family P) a :=
          (commutator_mono hZga le_rfl).trans
            (le_normalizer_iff_commutator_le_left.mp (hCga.trans (center_normalized h a)))
        have h₂ : ⁅Z (family P) (g • b),C⁆ ≤ Z (family P) c :=
          (commutator_mono hback inf_le_left).trans
            (le_normalizer_iff_commutator_le_right.mp
              (source_adjacent_core_normalizes_center h hbc.symm))
        exact (le_inf h₁ h₂).trans hi.le
      have hdisp : ⁅Z (family P) a,C⁆ ≤ Z (family P) b := by
        rw [hspan]
        have hn : Z (family P) a ≤ normalizer (Z (family P) b : Set G) :=
          (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
            ((source_core_centralizes_center h a).trans (centralizer_le hZba))).trans
              (Subgroup.centralizer_le_normalizer _)
        apply commutator_sup_le_of_relative_normal (Z (family P) a)
          _ _ _ (Z (family P) b) hn hZba hZga
        · exact (commutator_eq_bot_iff_le_centralizer.mpr
            (le_centralizer_iff.mp (inf_le_right.trans (source_core_centralizes_center h b)))).le.trans bot_le
        · exact hcross
      apply source_linear_rankOne_seed_nonquadratic h hB d hc hb hcomm hbc hac Ma Mb ea
      exact commutator_eq_bot_iff_le_centralizer.mpr
        (hdisp.trans (le_centralizer_iff.mp (inf_le_right.trans (source_core_centralizes_center h b))))
  · exact ⟨g,hga,hgb,hf⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
