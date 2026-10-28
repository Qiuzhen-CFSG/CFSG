module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Escape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.AlmostSimpleAction

/-!
# The terminal contradiction of MS93 (5.9)

The reversed critical witness puts the literal T₀ outside Q at the two-step
vertex. Its right conjugate acts locally there and retains that escape. The
normal-section action theorem fixes the source invariant span modulo Z.
The span contains the conjugated starting seed; that seed lies in the radius
group, so it lies in B. The same local conjugator returns the original starting
seed to B. This contradicts the earlier reciprocal source (5.8) moving index.

The preceding source (5.9) conjugate-span invariance and displacement, and
the local centralization used to place the critical witness in T₀, remain
explicit mathematical inputs. They are not asserted by the graph geometry.
Source: Meierfrankenfeld--Stellmacher (1993), pp.920--922.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geometry : Geometry R)

/-- Only the selected seed, rather than the entire source span, needs to lie
in the radius group at the two-step vertex. -/
theorem start_seed_le_B_of_span_commutator
    (hb : 2 < geometry.b R) {a e : Vertex R}
    (p : CriticalPath R geometry a e)
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R (p.walk.getVert 2))
    (F : Subgroup (FreeAmalgam R)) (hseed : Z R (act R y a) ≤ F)
    (hcomm : ⁅F,Ltilde R (p.walk.getVert 2)⁆ ≤ Z R (p.walk.getVert 2)) :
    Z R a ≤ B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2)) := by
  have hlen : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  have hcol : color R (p.walk.getVert 2) = false :=
    (p.vertex_color hlen).mpr (by decide)
  have hdist : (cosetGraph R).dist (act R y a) (p.walk.getVert 2) ≤ 2 := by
    have hh := dist_act R y a (p.walk.getVert 2)
    rw [show act R y (p.walk.getVert 2) = p.walk.getVert 2 from hy,
      p.dist_start hlen] at hh
    exact hh.le
  have hrad : Z R (act R y a) ≤ V R (p.walk.getVert 2) :=
    le_iSup_of_le _ (le_iSup_of_le hdist le_rfl)
  have hZ := radius_le_B_of_commutator geometry hb hcol _ hrad
    ((commutator_mono hseed le_rfl).trans hcomm)
  have hB : (B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2))).map
      (MulAut.conj y⁻¹).toMonoidHom =
      B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2)) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := geometry) hb
        (p.walk.getVert 2) hcol ((stabilizer R (p.walk.getVert 2)).inv_mem hy))
  rw [Z_act,←hB] at hZ
  exact (map_le_map_iff_of_injective (MulAut.conj y⁻¹).injective).mp hZ

/-- Source (5.9)'s actual normal span and escaping actor force the original
starting Z-layer into the two-step vertex's B-layer. -/
theorem start_seed_le_B_of_normal_span
    (hb : 4 < geometry.b R) {a e xi : Vertex R}
    (p : CriticalPath R geometry a e)
    (w : CriticalPath R geometry xi (p.walk.getVert 2))
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hc : Z R xi ≤ centralizer ((Z R (p.walk.getVert 2) ⊓
      B R a (geometry.Z_normal a) : Subgroup (FreeAmalgam R)) : Set _))
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R (p.walk.getVert 2))
    {S : Type*} [Group S] [IsSimpleGroup S]
    (q : stabilizer R (p.walk.getVert 2) →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R (p.walk.getVert 2)).subgroupOf (stabilizer R (p.walk.getVert 2)))
    (hp : IsPGroup 2 (Q R (p.walk.getVert 2)))
    (F : Subgroup (FreeAmalgam R)) (hF : F ≤ V R (p.walk.getVert 2))
    (hn : stabilizer R (p.walk.getVert 2) ≤ normalizer (F : Set _))
    (hseed : Z R (act R y a) ≤ F)
    (hdisp : ⁅F,(kernelCentralizer geometry a (p.walk.getVert 2)).map
      (MulAut.conj y⁻¹).toMonoidHom⁆ ≤ Z R (p.walk.getVert 2)) :
    Z R a ≤ B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2)) := by
  have hlen : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  have hcol : color R (p.walk.getVert 2) = false :=
    (p.vertex_color hlen).mpr (by decide)
  have hFB := normal_radius_le_B_of_kernel_escape geometry (by omega) hcol q hq hk hp
    F ((kernelCentralizer geometry a (p.walk.getVert 2)).map (MulAut.conj y⁻¹).toMonoidHom)
    hF hn (kernelCentralizer_conjugate_le_stabilizer geometry p (by omega) y hy)
    (kernelCentralizer_conjugate_not_le geometry (by omega) w hd hc y hy) hdisp
  have hZ := hseed.trans hFB
  have hB : (B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2))).map
      (MulAut.conj y⁻¹).toMonoidHom =
      B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2)) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := geometry) (by omega)
        (p.walk.getVert 2) hcol ((stabilizer R (p.walk.getVert 2)).inv_mem hy))
  rw [Z_act,←hB] at hZ
  exact (map_le_map_iff_of_injective (MulAut.conj y⁻¹).injective).mp hZ

/-- The original terminal span contradicts the genuine earlier moving index;
no strict-index (5.9) conclusion is assumed. -/
theorem normal_span_contradicts_source58
    (hb : 4 < geometry.b R) {a e xi : Vertex R}
    (p : CriticalPath R geometry a e)
    (w : CriticalPath R geometry xi (p.walk.getVert 2))
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hc : Z R xi ≤ centralizer ((Z R (p.walk.getVert 2) ⊓
      B R a (geometry.Z_normal a) : Subgroup (FreeAmalgam R)) : Set _))
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R (p.walk.getVert 2))
    {S : Type*} [Group S] [IsSimpleGroup S]
    (q : stabilizer R (p.walk.getVert 2) →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R (p.walk.getVert 2)).subgroupOf (stabilizer R (p.walk.getVert 2)))
    (hp : IsPGroup 2 (Q R (p.walk.getVert 2)))
    (F : Subgroup (FreeAmalgam R)) (hF : F ≤ V R (p.walk.getVert 2))
    (hn : stabilizer R (p.walk.getVert 2) ≤ normalizer (F : Set _))
    (hseed : Z R (act R y a) ≤ F)
    (hdisp : ⁅F,(kernelCentralizer geometry a (p.walk.getVert 2)).map
      (MulAut.conj y⁻¹).toMonoidHom⁆ ≤ Z R (p.walk.getVert 2))
    (h58 : 4 ≤ (B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2))).relIndex
      (U R a)) : False := by
  have hZ := start_seed_le_B_of_normal_span geometry hb p w hd hc y hy
    q hq hk hp F hF hn hseed hdisp
  have hi := relIndex_eq_one.mpr ((U_le_Z a).trans hZ)
  omega

/-- The exact local-span version of the source conclusion. The whole local
quotient may have an outer part, and the span need not lie in the radius group. -/
theorem start_seed_le_B_of_local_normal_span
    (hb : 4 < geometry.b R) {a e xi : Vertex R}
    (p : CriticalPath R geometry a e)
    (w : CriticalPath R geometry xi (p.walk.getVert 2))
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hc : Z R xi ≤ centralizer ((Z R (p.walk.getVert 2) ⊓
      B R a (geometry.Z_normal a) : Subgroup (FreeAmalgam R)) : Set _))
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R (p.walk.getVert 2))
    {J : Type*} [Group J]
    (q : stabilizer R (p.walk.getVert 2) →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R (p.walk.getVert 2)).subgroupOf (stabilizer R (p.walk.getVert 2)))
    (hp : IsPGroup 2 (Q R (p.walk.getVert 2)))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R (p.walk.getVert 2))).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R (p.walk.getVert 2))).map q : Set J) = ⊥)
    (F : Subgroup (FreeAmalgam R)) (hF : F ≤ stabilizer R (p.walk.getVert 2))
    (hn : stabilizer R (p.walk.getVert 2) ≤ normalizer (F : Set _))
    (hseed : Z R (act R y a) ≤ F)
    (hdisp : ⁅F,(kernelCentralizer geometry a (p.walk.getVert 2)).map
      (MulAut.conj y⁻¹).toMonoidHom⁆ ≤ Z R (p.walk.getVert 2)) :
    Z R a ≤ B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2)) := by
  apply start_seed_le_B_of_span_commutator geometry (by omega) p y hy F hseed
  exact normal_local_commutator_of_monolithic_kernel_escape q hq hk hp hS hC F
    ((kernelCentralizer geometry a (p.walk.getVert 2)).map (MulAut.conj y⁻¹).toMonoidHom)
    hF hn (kernelCentralizer_conjugate_le_stabilizer geometry p (by omega) y hy)
    (kernelCentralizer_conjugate_not_le geometry (by omega) w hd hc y hy) hdisp

/-- The exact local span and original quotient give the source5.8 contradiction. -/
theorem local_normal_span_contradicts_source58
    (hb : 4 < geometry.b R) {a e xi : Vertex R}
    (p : CriticalPath R geometry a e)
    (w : CriticalPath R geometry xi (p.walk.getVert 2))
    (hd : (cosetGraph R).dist xi a = geometry.b R - 2)
    (hc : Z R xi ≤ centralizer ((Z R (p.walk.getVert 2) ⊓
      B R a (geometry.Z_normal a) : Subgroup (FreeAmalgam R)) : Set _))
    (y : FreeAmalgam R) (hy : y ∈ stabilizer R (p.walk.getVert 2))
    {J : Type*} [Group J]
    (q : stabilizer R (p.walk.getVert 2) →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R (p.walk.getVert 2)).subgroupOf (stabilizer R (p.walk.getVert 2)))
    (hp : IsPGroup 2 (Q R (p.walk.getVert 2)))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R (p.walk.getVert 2))).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R (p.walk.getVert 2))).map q : Set J) = ⊥)
    (F : Subgroup (FreeAmalgam R)) (hF : F ≤ stabilizer R (p.walk.getVert 2))
    (hn : stabilizer R (p.walk.getVert 2) ≤ normalizer (F : Set _))
    (hseed : Z R (act R y a) ≤ F)
    (hdisp : ⁅F,(kernelCentralizer geometry a (p.walk.getVert 2)).map
      (MulAut.conj y⁻¹).toMonoidHom⁆ ≤ Z R (p.walk.getVert 2))
    (h58 : 4 ≤ (B R (p.walk.getVert 2) (geometry.Z_normal (p.walk.getVert 2))).relIndex
      (U R a)) : False := by
  have hZ := start_seed_le_B_of_local_normal_span geometry hb p w hd hc y hy
    q hq hk hp hS hC F hF hn hseed hdisp
  have hi := relIndex_eq_one.mpr ((U_le_Z a).trans hZ)
  omega

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
