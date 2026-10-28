module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ReciprocalEven

/-!
# The critical conjugate lies in the original LT two-core

Conjugating the span ball kernel by the original critical transporter
puts Uα in the ball of radius b−1 about the terminal H vertex. The source
rechoice identifies vertex two with the base LT vertex; the remaining
path has length b−2. Thus Uα lies in the radius-one kernel there, and the
natural point-label argument places that kernel in Q=O₂(LT). Restriction
of the two-core then supplies the required R₁ containment.

The image equality and relative Sylow conclusions preceding 14.7.66
remain their precise earlier source inputs. The placement field is now
constructed uniformly for the original CriticalPath.
Source: Aschbacher–Smith Notation 14.7.1 and 14.7.66.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The stronger placement in the literal two-core Q. -/
theorem Data.source_critical_le_Q (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) : c.Uα ≤ Q T L := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let r : K := inclusion (le_sup_right : F.H ≤ K) c.rechoice
  let k : K := c.gammaConjugator*r
  let w := k⁻¹ • base Ω true
  have hb := c.three_le
  have hd : (graph Ω).dist w (base Ω false) ≤ c.b-2 := by
    have hh := SimpleGraph.dist_le (c.path.drop 2)
    rw [SimpleGraph.Walk.drop_length,c.length] at hh
    have hw : w = r⁻¹ • (c.gammaConjugator⁻¹ • base Ω true) := by
      simp only [w,k,mul_inv_rev,mul_smul]
    rw [hw,←c.alignment,CosetGeometry.RankTwo.dist_smul,SimpleGraph.dist_comm]
    exact hh
  have hle := ChapterF.Section07.Track.ballKernel_le_of_dist_add_le Ω
    (ChapterF.Section07.Geometry.family_generates _ _) (m:=1) (n:=c.b-1)
    (show (graph Ω).dist w (base Ω false)+1 ≤ c.b-1 by omega)
  intro x hx
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨u',hu',hu'e⟩ := d.source_span_ballKernel c hu
  have hk : k⁻¹*u'*k ∈ ballKernel Ω w (c.b-1) := by
    simpa only [inv_inv] using (conj_mem_ballKernel_iff Ω k⁻¹ u' (base Ω true) (c.b-1)).mpr hu'
  have hQ := d.base_kernel_le_Q structural
    (mem_map_of_mem K.subtype (hle hk))
  have heq : K.subtype (k⁻¹*u'*k) = x := by
    rw [←he]
    change (c.conjugator)⁻¹ * (u':G) * c.conjugator =
      (MulAut.conj c.conjugator⁻¹) u
    rw [←hu'e]
    simp
  exact heq ▸ hQ

/-- The source R₁ placement follows by restricting the original two-core. -/
theorem Data.source_critical_le_Ri (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) : c.Uα ≤ F.Ri L 1 := by
  have hQT : Q T L ≤ (T:Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hle : F.Li L 1 ⊔ (T:Subgroup G) ≤ L ⊔ (T:Subgroup G) :=
    sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
  exact (d.source_critical_le_Q structural c).trans
    ((le_inf (hQT.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle))

/-- The placement field is constructed from the path; only the earlier global
quotient/Sylow facts remain. -/
theorem Data.source_earlierImages (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F)
    (himage : star F (Q T L) = star F (F.Ri L 1))
    (hsylow : Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F))) :
    c.EarlierImages := ⟨d.source_critical_le_Ri structural c,himage,hsylow⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
