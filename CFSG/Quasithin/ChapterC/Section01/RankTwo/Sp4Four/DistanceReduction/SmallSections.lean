module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.Backward
public import Theory.GroupAction.SimpleSeventeenSmallSection

/-!
# The small normal-section action in the actual symplectic geometry

At each original-group vertex, a surjection from its literal stabilizer
onto the simple quotient, with the neighborhood kernel as kernel, suffices.
A normal radius subgroup of order at most 64 modulo the original Z-layer
is centralized by the two-residual modulo Z. The proof passes through the
actual stabilizer inclusion and its subgroup quotient. It retains the
whole neighborhood kernel and every central attachment.

The consumer removes the small-section callback from the displacement
branch of MS93 (5.7), printed p.919. The remaining displacement inequality
is precisely the earlier local action comparison, not a critical-path
conclusion.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  (geometry : Geometry R)

/-- A genuine simple local quotient kills all normal radius sections of
order at most 64. Its kernel is the actual first-neighborhood kernel. -/
theorem small_normal_radius_commutator
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a)) (hS : 17 ∣ Nat.card S)
    (H : Subgroup (FreeAmalgam R)) (hH : H ≤ V R a)
    (hn : stabilizer R a ≤ normalizer (H : Set _))
    (hi : (Z R a).relIndex H ≤ 64) : ⁅H,Ltilde R a⁆ ≤ Z R a := by
  let G := stabilizer R a
  let D := H.subgroupOf G
  let Z₀ := (Z R a).subgroupOf G
  let := finite_stabilizer R a
  let : D.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Z₀.Normal := geometry.Z_normal a
  have hQG : Q R a ≤ G := fun _ hx => hx.1
  have hHG : H ≤ G := (hH.trans (geometry.V_le_Q hb a ha)).trans hQG
  have hker : IsPGroup 2 q.ker := by
    rw [hk]
    exact hp.of_equiv (subgroupOfEquivOfLe hQG).symm
  have hD : D ≤ q.ker := by
    rw [hk]
    exact fun _ hx => (hH.trans (geometry.V_le_Q hb a ha)) hx
  have hi₀ : Z₀.relIndex D ≤ 64 := by
    rw [relIndex_subgroupOf hHG]
    exact hi
  have hh := map_mono (f := G.subtype)
    (commutator_pResidual_le_of_simple_seventeen_small_section q hq hker hS D Z₀ hD hi₀)
  rw [map_commutator, map_subgroupOf_eq_of_le hHG,
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at hh
  exact hh

/-- The literal source generators and local displacement produce a backward
critical path; the small-section representation premise is discharged here. -/
theorem backward_path_of_simple_quotient_displacement
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (p : CriticalPath R geometry a e)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a)) (hS : 17 ∣ Nat.card S)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hat : Adjacent R a t) (hdt : Adjacent R (act R x d) t)
    (hindex : (Z R t).relIndex (Z R (act R x d)) ≤ 64)
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e)
    (hmove : 1 < (B R a (geometry.Z_normal a)).relIndex (U R d))
    (hdisp : ⁅V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R e⁆ ≤ Z R a) :
    (∃ r : CriticalPath R geometry (act R x d) (p.walk.getVert (p.walk.length-2)),
      r.walk.getVert 1 = t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i) ∧
      ¬ V R a ≤ Q R (p.walk.getVert (p.walk.length-2)) :=
  backward_path_of_radius_displacement geometry hb p x hx hat hdt 64 hindex
    (small_normal_radius_commutator geometry hb p.start_color q hq hk hp hS)
    hgen hmove hdisp

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
