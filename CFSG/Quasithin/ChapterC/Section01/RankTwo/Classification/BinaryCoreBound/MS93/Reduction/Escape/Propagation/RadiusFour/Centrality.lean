module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges

/-!
# Centrality of the radius commutator at the second predecessor

The edge displacement bound puts R₀ inside Z at the vertex two before the
critical endpoint. Transported (4.3.2) also puts R₀ in the fixed core there.
It therefore centralizes both the local two-core and the local residual;
these generate the stabilizer. Local conjugation consequently preserves R₀.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.8), printed p.888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

theorem localCenter_eq (a : Vertex R) :
    localCenter a = stabilizer R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y y.property)

variable [Finite M]

theorem radius_central_at_two (source : LocalSource L R) (hb : 2 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (p : Counterexample geometry) : radiusCommutator p.a p.a' ≤ localCenter p.c := by
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hct := p.before.adjacent (geometry := geometry) ht
  have hZ : radiusCommutator p.a p.a' ≤ Z R p.c :=
    ((Initial.radius_le_edge p t ht).trans
      (edge_le_Z p hb control edge p.a' t p.end_color ht.endpoint_adjacent)).trans
      (EdgeTransfer.edge_Z_le p.c t p.before_color hct)
  have hV : Z R p.a' ≤ V R p.c := by
    apply le_iSup_of_le p.a'
    apply le_iSup_of_le (show (cosetGraph R).dist p.a' p.c ≤ 2 by
      rw [SimpleGraph.dist_comm, p.before.1])
    exact le_rfl
  have hfixed : radiusCommutator p.a p.a' ≤ fixedCore R p.c := by
    rw [radiusCommutator, commutator_comm]
    exact (commutator_mono hV p.trapped).trans
      (commutator_le_fixed_at p (by omega) control p.c p.before_color)
  rw [localCenter_eq]
  refine le_inf (p.radius_le_kernel.trans (fun _ hx => hx.1)) ?_
  apply le_centralizer_iff.mpr
  rw [← source.local_generation p.c p.before_color]
  exact sup_le (le_centralizer_iff.mp (hfixed.trans inf_le_right))
    (le_centralizer_iff.mp
      (hZ.trans (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p.c p.before_color))))

omit [Finite M] in
theorem map_eq_of_le_localCenter (A : Subgroup (FreeAmalgam R)) (v : Vertex R)
    (hA : A ≤ localCenter v) (g : FreeAmalgam R) (hg : g ∈ stabilizer R v) :
    A.map (MulAut.conj g⁻¹).toMonoidHom = A := by
  have hAc : A ≤ centralizer (stabilizer R v : Set (FreeAmalgam R)) := by
    rw [localCenter_eq] at hA
    exact hA.trans inf_le_right
  exact mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hAc ((stabilizer R v).inv_mem hg)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
