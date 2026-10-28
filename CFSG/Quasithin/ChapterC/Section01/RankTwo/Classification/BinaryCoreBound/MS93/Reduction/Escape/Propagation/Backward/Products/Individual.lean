module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Residual

/-!
# Individual products from one selected backward span

The starting vertex stabilizer transports the common edge of a prescribed
reverse-moving neighbor to the selected edge. Covariance places its radius
group in the selected W(t), so the residual estimate transports back to that
individual radius group. The residual normalizes its product with V_a;
the common edge kernel normalizes both factors. Those two groups generate
G_a, proving relative normality of the individual product.

This supplies the passage from W(t)V_a to every V_dV_a in MS93 (4.3.7)(i).
It uses neither symmetry of moving neighbors nor far propagation.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : Geometry R}

/-- A residual estimate at one incident edge controls every reverse-moving
neighbor, using an actual conjugator in the vertex stabilizer. -/
theorem individual_residual_le (hb : 2 < geometry.b R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hW : ⁅backwardSpan geometry a t, Ltilde R a⁆ ≤ Vcirc R a)
    (d : Vertex R) (hd : a ∈ movingNeighbors geometry d) :
    ⁅V R d, Ltilde R a⁆ ≤ Vcirc R a := by
  have hdist : (cosetGraph R).dist a d = 2 := by
    rw [SimpleGraph.dist_comm]
    exact hd.1
  have hdcol : color R d = false :=
    (color_eq_of_dist_even R d a (hd.1.symm ▸ (by decide : Even 2))).trans ha
  obtain ⟨s, has, hds⟩ := exists_common_neighbor_of_dist_two R a d hdist
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R a has hat
  have hga : act R g a = a := hg
  have hgdt : Adjacent R (act R g d) t := by
    rw [← hgs]
    exact (adjacent_act_iff R g d s).mpr hds
  have hmove : a ∈ movingNeighbors geometry (act R g d) := by
    have h := (PairingControl.FirstPairing.movingNeighbors_act_iff hb g d a hdcol).mpr hd
    simpa only [hga] using h
  have hres : ⁅V R (act R g d), Ltilde R (act R g a)⁆ ≤ Vcirc R (act R g a) := by
    rw [hga]
    exact (commutator_mono (V_le_backwardSpan hgdt hmove) le_rfl).trans hW
  rwa [V_act, Ltilde_act, Vcirc_act, ← map_commutator,
    map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective] at hres

/-- The individual product is normal relative to G_a once its residual
commutator is bounded. The edge kernel supplies the other local generator. -/
theorem individual_product_normal (source : LocalSource L R)
    {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2)
    (hc : ⁅V R d, Ltilde R a⁆ ≤ Vcirc R a) :
    ((V R d ⊔ V R a).subgroupOf (stabilizer R a)).Normal := by
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R a d hd
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hQta : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hQtd : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have hgen : Ltilde R a ⊔ Q R t = stabilizer R a := by
    apply le_antisymm (sup_le (Ltilde_le_stabilizer a) hQta)
    rw [← source.local_generation a ha]
    exact sup_le_sup_left (Q_le_adjacent_h R ht hat) _
  have hVcirc : Vcirc R a ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  apply normal_subgroupOf_of_le_normalizer
  rw [← hgen]
  apply sup_le
  · rw [sup_comm (V R d)]
    exact PairingControl.Geometry.LocalProducts.normalizes_sup_of_commutator_le _ _ _
      ((Ltilde_le_stabilizer a).trans (V_normalized a)) (hc.trans hVcirc)
  · exact (le_inf (hQtd.trans (V_normalized d)) (hQta.trans (V_normalized a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- All three clauses for each individual product follow from a selected
edge with W(t) contained in the kernel two before the critical endpoint. -/
theorem products_of_selected_edge (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R) (initial : InitialFacts p)
    (t : Vertex R) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c)
    (d : Vertex R) (hd : (cosetGraph R).dist p.a d = 2)
    (hmove : p.a ∈ movingNeighbors geometry d) :
    V R d ⊔ V R p.a ≤ stabilizer R p.a ∧
      ((V R d ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal ∧
      ⁅V R d, Ltilde R p.a⁆ ≤ Vcirc R p.a := by
  have hres := individual_residual_le (by omega) p.color_a hat
    (backwardSpan_residual_le source p hb initial t hgen hW) d hmove
  exact ⟨(product_le_Q p.color_a hb hd).trans (fun _ hx => hx.1),
    individual_product_normal source p.color_a hd hres, hres⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
