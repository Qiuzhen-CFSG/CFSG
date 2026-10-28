module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FaithfulSection

/-!
# The actor used in the normal-radius contradiction

The moving-product equality transports the endpoint's noncontainment to
mu. Faithfulness of the actual natural section proves that noncontainment;
it is not an extra field assumed of ForwardFacts.

These three product arguments are adapted from the accepted
RadiusFour/Forward/Products.lean proof (fleet task
qt-c01-ms93-escape-forward-products, snapshot a10c879b26dc346e42af4b61bdc689a0e8829224).
That independently completed module is outside this task's source snapshot
and ownership. Its original source is preserved; this module retains only
the actor argument needed by the kernel proof, under the Kernel namespace.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.889, second paragraph
of (4.3.8), used in the following normal-radius contradiction.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The printed moving-product equality uses the specified first
conjugator in G_c, with normality relative to that actual stabilizer. -/
private theorem moving_product_eq (source : LocalSource L R) (hb : 2 < geometry.b R)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (w : CentralOrbitWitnesses p d t₃ t₅) :
    Vcirc R w.mu ⊔ Vcirc R p.c = Vcirc R p.a' ⊔ Vcirc R p.c := by
  obtain ⟨q, hq⟩ := counterexample_at_vertex p (by omega) p.c p.before_color
  have hm := (backward.moving_symmetric q p.a').mp
    (show p.a' ∈ movingNeighbors geometry q.a by
      simpa only [hq] using Forward.Reversal.critical_endpoint_moving source hb p.color_a p.critical p.before)
  have hp := backward.product_normal q p.a' (by simpa only [hq] using p.before.1) hm
  rw [hq] at hp
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hn := PairingControl.Geometry.LocalProducts.moving_product_normal_of_residual source
    p.before_color (p.before.adjacent (geometry := geometry) ht) ht.endpoint_adjacent hp.2.2
  have hlocal : Vcirc R p.c ⊔ Vcirc R p.a' ≤ stabilizer R p.c :=
    (sup_le_sup (PairingControl.Geometry.Vcirc_le_V _) (PairingControl.Geometry.Vcirc_le_V _)).trans
      ((sup_comm _ _).trans_le hp.1)
  have hnorm := (normal_subgroupOf_iff_le_normalizer hlocal).mp hn
  have heq := mem_normalizer_iff_map_conj_eq.mp
    (hnorm ((stabilizer R p.c).inv_mem w.first_local))
  change (Vcirc R p.c ⊔ Vcirc R p.a').map
    (MulAut.conj w.first_conjugator⁻¹).toMonoidHom = _ at heq
  have hfix : act R w.first_conjugator p.c = p.c := w.first_local
  rw [Subgroup.map_sup, ← Vcirc_act, ← Vcirc_act, hfix, w.first_image] at heq
  simpa only [sup_comm] using heq

/-- The moving group at the critical endpoint escapes the product of the
predecessor moving group with the starting kernel. Faithfulness of its actual
natural section detects the critical action of Z_alpha. -/
private theorem endpoint_moving_not_le_product (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (p : Counterexample geometry) :
    ¬ Vcirc R p.a' ≤ Vcirc R p.c ⊔ Q R p.a := by
  obtain ⟨hi⟩ := initial p
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hm := Forward.Reversal.critical_endpoint_moving source hb p.color_a p.critical p.before
  have hH : H R p.c = radiusCommutator p.a p.a' :=
    (moving_edge_eq_at p (by omega) control p.c t p.a' p.before_color
      (p.before.adjacent (geometry := geometry) ht) ht.endpoint_adjacent hm).2.trans
      (hi.radius_eq_edge t ht).symm
  have hBlocal : Vcirc R p.c ≤ stabilizer R p.a := by
    apply (PairingControl.Geometry.Vcirc_le_V _).trans
    apply PairingControl.Geometry.V_le_stabilizer_of_distance p.before_color
    rw [SimpleGraph.dist_comm]
    have hp := p.before.2
    rw [p.distance_eq_b] at hp
    exact hp.le
  have hcomm : ⁅Z R p.a, Vcirc R p.c ⊔ Q R p.a⁆ = ⁅Z R p.a, Vcirc R p.c⁆ :=
    (commutator_eq_of_centralizing_sup (sup_comm _ _)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes p.a p.color_a)))
      (hBlocal.trans (Z_normalized R p.a))).symm
  intro hle
  have hbound : ⁅Vcirc R p.a', Z R p.a⁆ ≤ Z R p.a' := by
    rw [commutator_comm]
    apply (commutator_mono le_rfl hle).trans
    rw [hcomm, commutator_comm]
    apply (commutator_mono le_rfl ((Z_le_VBall R p.a 2).trans p.trapped)).trans
    change H R p.c ≤ Z R p.a'
    rw [hH]
    exact p.radius_le_end
  obtain ⟨q, hq⟩ := counterexample_at_vertex p (by omega) p.a' p.end_color
  obtain ⟨hqi⟩ := initial q
  have hsection : NaturalSectionAt p.a' (V R p.a') (Z R p.a') := by
    simpa only [hq] using hqi.natural_section
  exact p.critical.2 (PairingControl.actor_le_Q source p.end_color hsection (Z R p.a)
    (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).1 hbound)

/-- The literal printed noncontainment, transported through the actual
first conjugator by the moving-product equality. -/
theorem first_moving_not_le_product (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (w : CentralOrbitWitnesses p d t₃ t₅) :
    ¬ Vcirc R w.mu ≤ Vcirc R p.c ⊔ Q R p.a := by
  intro hle
  apply endpoint_moving_not_le_product source hb initial control p
  have hprod : Vcirc R w.mu ⊔ Vcirc R p.c ≤ Vcirc R p.c ⊔ Q R p.a :=
    sup_le hle le_sup_left
  rw [moving_product_eq source hb backward p w] at hprod
  exact le_sup_left.trans hprod

/-- The first output of ProductFacts follows from the stronger printed
moving-subgroup noncontainment. -/
theorem first_radius_not_le (source : LocalSource L R) (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (w : CentralOrbitWitnesses p d t₃ t₅) :
    ¬ V R w.mu ≤ Q R p.a := by
  intro hle
  exact first_moving_not_le_product source hb initial control backward p w
    ((PairingControl.Geometry.Vcirc_le_V _).trans (hle.trans le_sup_right))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel
