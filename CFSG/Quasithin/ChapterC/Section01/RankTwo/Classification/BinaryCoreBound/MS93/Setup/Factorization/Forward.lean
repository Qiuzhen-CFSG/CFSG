module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Basic

/-!
# Forward nonnormality on a critical path

For a critical pair (a,a') and c two steps after a, Z_a X_c lies in G_c.
If it were normal there, its containment in the intervening edge group
would place it in Q_c. This first excludes critical distance two. Local
transitivity then moves the intervening neighbor to the next neighbor on
the path. Normality preserves the product, while its moved Z-generator
and its X-factor both lie in Q_a' by critical minimality. This contradicts
the defining noncontainment of the critical pair.

Containment is part of the conclusion so that relative normality cannot
silently replace the asserted product by its intersection with G_c.

Source: Meierfrankenfeld--Stellmacher (1993), 2.2(iv), pp.856--857.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

/-- Source 2.2(iv), for every actual critical pair and its second path vertex. -/
theorem critical_nonnormal_forward (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    (a' : Vertex R) (hcrit : CriticalPair R a a' (g.exists_critical a ha))
    (c : Vertex R) (hac : (cosetGraph R).dist a c = 2)
    (hpath : (cosetGraph R).dist c a' + 2 = (cosetGraph R).dist a a') :
    Z R a ⊔ X R c ≤ stabilizer R c ∧
      ¬ ((Z R a ⊔ X R c).subgroupOf (stabilizer R c)).Normal := by
  have hNc : Z R a ⊔ X R c ≤ stabilizer R c :=
    sup_le (Z_le_stabilizer_of_dist_two R g a ha hb c hac)
      ((omegaCenter_le (Q R c)).trans (fun _ hx => hx.1))
  refine ⟨hNc, ?_⟩
  intro hNorm
  have hccol : color R c = false :=
    (color_eq_of_dist_even R a c (by rw [hac]; decide)).symm.trans ha
  have heven := g.even a ha
  have htwo : 2 ≤ criticalDistance R a (g.exists_critical a ha) := by
    obtain ⟨n, hn⟩ := heven
    omega
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hac
  have hZt : Z R a ≤ Q R t := Z_le_Q_of_dist_lt R a (g.exists_critical a ha) (by
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    omega)
  have hNt : Z R a ⊔ X R c ≤ stabilizer R t :=
    sup_le (hZt.trans (fun _ hx => hx.1))
      ((omegaCenter_le (Q R c)).trans (fun _ hx => hx.2 t hct))
  have hNQ := le_Q_of_normal_edge R c t hct (Z R a ⊔ X R c) (le_inf hNc hNt) hNorm
  have hlarge : 2 < criticalDistance R a (g.exists_critical a ha) := by
    by_contra hn
    have heq : c = a' := (cosetGraph_connected R).dist_eq_zero_iff.mp (by
      have hh := hcrit.1
      omega)
    exact hcrit.2 (heq ▸ le_sup_left.trans hNQ)
  obtain ⟨u, hcu, hua'⟩ := exists_adjacent_dist_sub_one R c a' (by
    have hh := hcrit.1
    omega)
  obtain ⟨f, hfc, hft⟩ := stabilizer_transitive_neighbors R c hct hcu
  have hfa : Adjacent R (act R f a) u := by
    rw [← hft]
    exact (adjacent_act_iff R f a t).mpr hat
  have hfdist : (cosetGraph R).dist (act R f a) a' <
      criticalDistance R (act R f a) (g.exists_critical _ (by rwa [action_preserves_color])) := by
    rw [g.distance_constant _ (by rwa [action_preserves_color]), ← g.distance_constant a ha]
    have htri := (cosetGraph_connected R).dist_triangle
      (u := act R f a) (v := u) (w := a')
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hfa)
    have hh := hcrit.1
    omega
  have hZimage : Z R (act R f a) ≤ Q R a' :=
    Z_le_Q_of_dist_lt R _ (g.exists_critical _ (by rwa [action_preserves_color])) hfdist
  have hXc : X R c ≤ Q R a' := X_le_Q_of_dist_lt R g hC c hccol a' (by
    rw [g.distance_constant c hccol, ← g.distance_constant a ha]
    have hh := hcrit.1
    omega)
  have hn := (normal_subgroupOf_iff_le_normalizer hNc).mp hNorm
  have hmap := mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R c).inv_mem hfc))
  have hfix : act R f c = c := hfc
  have hsup : (Z R a ⊔ X R c).map (MulAut.conj f⁻¹).toMonoidHom =
      Z R (act R f a) ⊔ X R c := by
    rw [Subgroup.map_sup, ← Z_act, ← X_act, hfix]
  apply hcrit.2
  calc
    Z R a ≤ Z R a ⊔ X R c := le_sup_left
    _ = (Z R a ⊔ X R c).map (MulAut.conj f⁻¹).toMonoidHom := hmap.symm
    _ = Z R (act R f a) ⊔ X R c := hsup
    _ ≤ Q R a' := sup_le hZimage hXc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
