module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphSeeds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood

/-!
# The index of a seed at a cubic Chapter 11 vertex

A critical center has nontrivial two-group image on the three neighbors,
so that image has order two. Its intersection with the full action kernel
is a two-group; the actual normal Sylow of that kernel identifies this
intersection with the intersection with Qβ. The relative-index formula
therefore gives [Zα : Zα ∩ Qβ] = 2. The same argument applies to the
edge radical and its subgroup Zα Qβ, proving their equality by index
multiplicativity. Thus the cubic case of (11.4) follows directly.

This is the cubic seed-index assertion used in (11.3) and (11.6), with
only the earlier (6.2)(d) kernel-Sylow input left explicit. The reduced
F1.11 application supplies that input on the literal source graph.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(6.2)(d), p.119; (11.2)--(11.3), pp.168--171; (11.6), pp.172--174.
-/

public noncomputable section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph

private theorem cubic_image_card {X : Type*} (hcard : Nat.card X = 3)
    (A : Subgroup (Equiv.Perm X)) (hp : IsPGroup 2 A) (hne : A ≠ ⊥) : Nat.card A = 2 := by
  classical
  let := Nat.finite_of_card_ne_zero (show Nat.card X ≠ 0 by omega)
  let := Fintype.ofFinite X
  have hc : Nat.card (Equiv.Perm X) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hcard]
    decide
  have hd : Nat.card A ∣ 6 := hc ▸ A.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) 3 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card A ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
  · exact (hne (Subgroup.card_eq_one.mp h1)).elim
  · exact h2

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Every two-subgroup moving the cubic star has core intersection of index two. -/
theorem source_cubic_two_subgroup_index (h : LocallyRankOneTriple P B)
    (b : Vertex (family P)) (A₀ : Subgroup G) (hp : IsPGroup 2 A₀)
    (haM : A₀ ≤ stabilizer (family P) b) (hesc : ¬ A₀ ≤ U (family P) b)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (hSyl : ∃ T : Sylow 2 (U (family P) b),
      (T : Subgroup (U (family P) b)).map (U (family P) b).subtype = Q (family P) b) :
    (A₀ ⊓ Q (family P) b).relIndex A₀ = 2 := by
  let := finite_endpoints h
  have hi : A₀ ⊓ Q (family P) b = A₀ ⊓ U (family P) b := by
    apply le_antisymm (inf_le_inf_left _ (source_Z_Q_U h b).2)
    apply le_inf inf_le_left
    exact CommutingTrivial.two_subgroup_le_Q (family P) b hSyl
      (hp.of_injective (inclusion inf_le_left) (inclusion_injective _)) inf_le_right
  let M := stabilizer (family P) b
  let A := A₀.subgroupOf M
  let f := localAction (family P) b
  have hm : A.map f ≠ ⊥ := by
    intro he
    have hle := (Subgroup.map_eq_bot_iff _).mp he
    apply hesc
    intro z hz
    have hk := hle (show (⟨z,haM hz⟩ : M) ∈ A from hz)
    rw [←U_eq_localAction_kernel] at hk
    exact hk
  have hci := cubic_image_card hcard (A.map f) (hp.comap_subtype.map f) hm
  have hk : f.ker.map M.subtype = U (family P) b := by
    rw [←U_eq_localAction_kernel, map_subgroupOf_eq_of_le (U_le_stabilizer _ b)]
  have he := relIndex_map_map_of_injective (f := M.subtype) f.ker A M.subtype_injective
  rw [hk, map_subgroupOf_eq_of_le haM, relIndex_ker, hci] at he
  rw [hi, inf_relIndex_left]
  exact he

/-- The actual center/core intersection has index two, retaining the full kernel Sylow. -/
theorem source_cubic_seed_index (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (hSyl : ∃ T : Sylow 2 (U (family P) b),
      (T : Subgroup (U (family P) b)).map (U (family P) b).subtype = Q (family P) b) :
    (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = 2 := by
  let := source_center_elementary h a
  have hab := source_critical_one_adjacent hc hb
  exact source_cubic_two_subgroup_index h b (Z (family P) a)
    (IsElementaryAbelian.isPGroup 2 _)
    (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)))
    hc.2 hcard hSyl

/-- At a cubic vertex the edge radical is the product Zα Qβ.
Both factors lie in that radical, and both it and their join have index two
over Qβ. This strengthens the cubic case of (11.4), proved below.
The full local kernel remains distinct from Qβ. -/
theorem source_cubic_edge_core_eq_center_sup_core (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (hSyl : ∃ T : Sylow 2 (U (family P) b),
      (T : Subgroup (U (family P) b)).map (U (family P) b).subtype = Q (family P) b) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Z (family P) a ⊔ Q (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let R := E.pCoreIn 2
  have hab := source_critical_one_adjacent hc hb
  have haE : Z (family P) a ≤ E := le_inf (Z_le_stabilizer _ a)
    (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)))
  have haR : Z (family P) a ≤ R := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 _) haE
    (inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp
      (Z_normal _ a)))
  have hqE : Q (family P) b ≤ E := le_inf
    ((source_Z_Q_U h b).2.trans ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right))
    (Q_le_stabilizer _ b)
  have hqR : Q (family P) b ≤ R := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 _) hqE
    (inf_le_right.trans (CommutingTrivial.stabilizer_normalizes_Q (family P) b))
  have hR2 : IsPGroup 2 R := isPGroup_pCoreIn 2 _
  have hRM : R ≤ stabilizer (family P) b := (pCoreIn_le 2 E).trans inf_le_right
  have hRindex := source_cubic_two_subgroup_index h b R hR2 hRM
    (fun he => hc.2 (haR.trans he)) hcard hSyl
  rw [inf_eq_right.mpr hqR] at hRindex
  let W := Z (family P) a ⊔ Q (family P) b
  have hWR : W ≤ R := sup_le haR hqR
  have hWindex := source_cubic_two_subgroup_index h b W
    (hR2.of_injective (inclusion hWR) (inclusion_injective _))
    (hWR.trans hRM) (fun he => hc.2 (le_sup_left.trans he)) hcard hSyl
  rw [inf_eq_right.mpr (show Q (family P) b ≤ W from le_sup_right)] at hWindex
  have hindices := relIndex_mul_relIndex (Q (family P) b) W R le_sup_right hWR
  rw [hRindex, hWindex] at hindices
  have hWR' : R ≤ W := (relIndex_eq_one).mp (by omega : W.relIndex R = 1)
  exact le_antisymm hWR' hWR

/-- Source (11.4) at a cubic beta vertex: the two adjacent cores generate
the edge radical. No alpha-core equality or later profile is assumed. -/
theorem source_cubic_edge_core_eq_cores (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (hSyl : ∃ T : Sylow 2 (U (family P) b),
      (T : Subgroup (U (family P) b)).map (U (family P) b).subtype = Q (family P) b) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b := by
  have hab := source_critical_one_adjacent hc hb
  have hgen := source_cubic_edge_core_eq_center_sup_core h hc hb hcard hSyl
  have haR : Q (family P) a ≤
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      (le_inf (Q_le_stabilizer _ a)
        ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)))
      (inf_le_left.trans (CommutingTrivial.stabilizer_normalizes_Q (family P) a))
  exact le_antisymm
    (hgen.le.trans (sup_le_sup ((source_Z_Q_U h a).1.trans (map_subtype_le _)) le_rfl))
    (sup_le haR (hgen ▸ le_sup_right))

/-- The actual edge radical modulo Qβ has order two and is elementary.
The normality witness is relative to that radical, not to the ambient group. -/
theorem source_cubic_edge_core_quotient (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (hSyl : ∃ T : Sylow 2 (U (family P) b),
      (T : Subgroup (U (family P) b)).map (U (family P) b).subtype = Q (family P) b) :
    let R := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
    ∃ hN : ((Q (family P) b).subgroupOf R).Normal,
      letI := hN
      Nat.card (R ⧸ (Q (family P) b).subgroupOf R) = 2 ∧
        IsElementaryAbelian 2 (R ⧸ (Q (family P) b).subgroupOf R) := by
  let R := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  have hgen : R = Z (family P) a ⊔ Q (family P) b :=
    source_cubic_edge_core_eq_center_sup_core h hc hb hcard hSyl
  have hqR : Q (family P) b ≤ R := hgen ▸ le_sup_right
  have hRM : R ≤ stabilizer (family P) b := (pCoreIn_le 2 _).trans inf_le_right
  have hn : ((Q (family P) b).subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hqR).mpr
      (hRM.trans (CommutingTrivial.stabilizer_normalizes_Q (family P) b))
  refine ⟨hn, ?_⟩
  let := hn
  have hi := source_cubic_two_subgroup_index h b R (isPGroup_pCoreIn 2 _)
    hRM (fun he => hc.2 ((hgen ▸ le_sup_left).trans he)) hcard hSyl
  rw [inf_eq_right.mpr hqR] at hi
  have hquot : Nat.card (R ⧸ (Q (family P) b).subgroupOf R) = 2 := hi
  let : IsCyclic (R ⧸ (Q (family P) b).subgroupOf R) := isCyclic_of_prime_card hquot
  refine ⟨hquot, { exponent_dvd_p := ?_ }⟩
  simpa only [hquot] using (Group.exponent_dvd_nat_card
    (G := R ⧸ (Q (family P) b).subgroupOf R))


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
