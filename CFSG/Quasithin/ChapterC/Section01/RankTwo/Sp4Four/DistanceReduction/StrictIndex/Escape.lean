module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.Backward

/-!
# The nonkernel actor in the strict-index argument

The critical witness selected by reversed source (5.8) is closer to the
original vertex than the critical distance, so its full Z-layer lies in
that vertex kernel. Its centralization of the original fixed intersection
therefore puts it in the literal subgroup T₀ used by (5.9). Criticality at
the two-step vertex proves that T₀ escapes its kernel. The same escape is
preserved under the source's right conjugation by that vertex stabilizer.

The centralization premise is the local-module step on printed p.922; it
is not inferred from the critical pair's distance. The final bound (5.9)
is not asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), pp.920--922.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
variable {M : Type*} [Group M] {R : Subgroup M} (geometry : Geometry R)

/-- The source centralizer T₀, retaining the original U- and B-layers. -/
noncomputable def kernelCentralizer (a c : Vertex R) : Subgroup (FreeAmalgam R) :=
  Q R a ⊓ centralizer ((U R c ⊓ B R a (geometry.Z_normal a) :
    Subgroup (FreeAmalgam R)) : Set _)

/-- The source subgroup H = [U_c,T0], before its fixed-core containment. -/
noncomputable def kernelCommutator (a c : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅U R c,kernelCentralizer geometry a c⁆

/-- The literal H2 obtained by the source's right conjugation. -/
noncomputable def conjugatedKernelCommutator (a c : Vertex R) (y : FreeAmalgam R) :
    Subgroup (FreeAmalgam R) :=
  (kernelCommutator geometry a c).map (MulAut.conj y⁻¹).toMonoidHom

/-- The original edge containment for H transports to H2 <= Z_c under
the same local source conjugator. -/
theorem conjugated_kernel_commutator_le_next_seed
    (hb : 2 ≤ geometry.b R) {a e : Vertex R}
    (p : CriticalPath R geometry a e) (y : FreeAmalgam R)
    (hy : y ∈ stabilizer R (p.walk.getVert 2))
    (hH : kernelCommutator geometry a (p.walk.getVert 2) ≤ Z R (p.walk.getVert 1)) :
    conjugatedKernelCommutator geometry a (p.walk.getVert 2) y ≤
      Z R (p.walk.getVert 2) := by
  have hlen : 2 ≤ p.walk.length := by rwa [p.length_eq_b]
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color hlen).mpr (by decide)
  have hct : Adjacent R (p.walk.getVert 2) (act R y (p.walk.getVert 1)) := by
    have hh := (adjacent_act_iff R y _ _).mpr (adjacent_symm R
      ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega : 1 < p.walk.length))))
    rwa [show act R y (p.walk.getVert 2) = p.walk.getVert 2 from hy] at hh
  have hm := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hH
  rw [←Z_act] at hm
  exact hm.trans (adjacent_Z_le R hc hct)

/-- The reversed critical witness belongs to the original T₀. -/
theorem witness_seed_le_kernelCentralizer
    (hb : 2 ≤ geometry.b R) {a c xi : Vertex R}
    (hxi : color R xi = false)
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hc : Z R xi ≤ centralizer ((Z R c ⊓ B R a (geometry.Z_normal a) :
      Subgroup (FreeAmalgam R)) : Set _)) :
    Z R xi ≤ kernelCentralizer geometry a c := by
  apply le_inf
  · apply Z_le_Q_of_dist_lt R xi (geometry.exists_critical xi hxi)
    rw [geometry.distance_constant xi hxi,hd]
    change geometry.b R - 2 < geometry.b R
    omega
  · exact hc.trans (centralizer_le (inf_le_inf_right _ (U_le_Z c)))

/-- The original T₀ escapes Q_c because it contains the same critical seed. -/
theorem kernelCentralizer_not_le_of_critical
    (hb : 2 ≤ geometry.b R) {a c xi : Vertex R}
    (w : CriticalPath R geometry xi c)
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hc : Z R xi ≤ centralizer ((Z R c ⊓ B R a (geometry.Z_normal a) :
      Subgroup (FreeAmalgam R)) : Set _)) :
    ¬ kernelCentralizer geometry a c ≤ Q R c := by
  intro h
  exact w.critical.2 ((witness_seed_le_kernelCentralizer geometry hb
    w.start_color hd hc).trans h)

/-- Right conjugation by the actual c-stabilizer preserves nonkernel escape. -/
theorem kernelCentralizer_conjugate_not_le
    (hb : 2 ≤ geometry.b R) {a c xi : Vertex R}
    (w : CriticalPath R geometry xi c)
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hc : Z R xi ≤ centralizer ((Z R c ⊓ B R a (geometry.Z_normal a) :
      Subgroup (FreeAmalgam R)) : Set _))
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R c) :
    ¬ (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom ≤ Q R c := by
  intro h
  have hfix : act R y c = c := hy
  have hQ : (Q R c).map (MulAut.conj y⁻¹).toMonoidHom = Q R c := by
    rw [← Q_act,hfix]
  rw [←hQ] at h
  exact kernelCentralizer_not_le_of_critical geometry hb w hd hc
    ((map_le_map_iff_of_injective (MulAut.conj y⁻¹).injective).mp h)

/-- At the actual two-step vertex, T₀ and its source conjugate are local actors. -/
theorem kernelCentralizer_conjugate_le_stabilizer [Finite M]
    {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hb : 2 ≤ geometry.b R) (y : FreeAmalgam R)
    (hy : y ∈ stabilizer R (p.walk.getVert 2)) :
    (kernelCentralizer geometry a (p.walk.getVert 2)).map
      (MulAut.conj y⁻¹).toMonoidHom ≤ stabilizer R (p.walk.getVert 2) := by
  have hlen : 2 ≤ p.walk.length := by rw [p.length_eq_b]; exact hb
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color hlen).mpr (by decide)
  have hT : kernelCentralizer geometry a (p.walk.getVert 2) ≤
      stabilizer R (p.walk.getVert 2) :=
    inf_le_left.trans (Q_le_stabilizer_of_dist_le_two a (p.walk.getVert 2)
      p.start_color hc (p.dist_start hlen).le)
  have hn := (stabilizer R (p.walk.getVert 2)).le_normalizer
    ((stabilizer R (p.walk.getVert 2)).inv_mem hy)
  have hm := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hT
  have he : (stabilizer R (p.walk.getVert 2)).map (MulAut.conj y⁻¹).toMonoidHom =
      stabilizer R (p.walk.getVert 2) := mem_normalizer_iff_map_conj_eq.mp hn
  rwa [he] at hm

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
