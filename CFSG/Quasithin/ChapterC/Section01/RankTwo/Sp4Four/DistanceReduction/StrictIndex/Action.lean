module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.Backward
public import Theory.GroupTheory.NormalSectionTwoResidual

/-!
# The terminal normal-section action in the strict-index argument

Once the source conjugate span is normal in the literal vertex stabilizer,
an actor outside its neighborhood kernel which fixes the span modulo Z
forces the local two-residual to fix it. The original preimage B then
contains the span. All subgroups, quotient maps and central layers belong
to the original MS93 graph; there is no binary model or split-section input.

Source: Meierfrankenfeld–Stellmacher (1993), final paragraph of (5.9),
printed p.922. The preceding proof that the span is invariant and the actor
escapes Q is supplied separately by the strict-index argument.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  (geometry : Geometry R)

/-- A normal radius section fixed by an actor escaping Q is fixed by the
literal local residual. -/
theorem normal_radius_commutator_of_kernel_escape
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a))
    (H T : Subgroup (FreeAmalgam R)) (hH : H ≤ V R a)
    (hn : stabilizer R a ≤ normalizer (H : Set _))
    (hT : T ≤ stabilizer R a) (hTQ : ¬ T ≤ Q R a)
    (hc : ⁅H,T⁆ ≤ Z R a) : ⁅H,Ltilde R a⁆ ≤ Z R a := by
  let G := stabilizer R a
  let D := H.subgroupOf G
  let Z₀ := (Z R a).subgroupOf G
  let T₀ := T.subgroupOf G
  let : D.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Z₀.Normal := geometry.Z_normal a
  have hQG : Q R a ≤ G := fun _ hx => hx.1
  have hHG : H ≤ G := (hH.trans (geometry.V_le_Q hb a ha)).trans hQG
  have hker : IsPGroup 2 q.ker := by
    rw [hk]
    exact hp.comap_subtype
  have hescape : ¬ T₀ ≤ q.ker := by
    intro h
    apply hTQ
    intro t ht
    have hh := h (show (⟨t,hT ht⟩ : G) ∈ T₀ from ht)
    rw [hk] at hh
    exact hh
  have hc₀ : ⁅D,T₀⁆ ≤ Z₀ := by
    apply commutator_le.mpr
    intro d hd t ht
    exact hc (commutator_mem_commutator hd ht)
  have hh := map_mono (f := G.subtype)
    (commutator_pResidual_le_of_simple_kernel_escape 2 q hq hker D Z₀ T₀ hescape hc₀)
  rw [map_commutator, map_subgroupOf_eq_of_le hHG,
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at hh
  exact hh

/-- The actual fixed preimage B contains the normal radius section. -/
theorem normal_radius_le_B_of_kernel_escape
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a))
    (H T : Subgroup (FreeAmalgam R)) (hH : H ≤ V R a)
    (hn : stabilizer R a ≤ normalizer (H : Set _))
    (hT : T ≤ stabilizer R a) (hTQ : ¬ T ≤ Q R a)
    (hc : ⁅H,T⁆ ≤ Z R a) : H ≤ B R a (geometry.Z_normal a) :=
  radius_le_B_of_commutator geometry hb ha H hH
    (normal_radius_commutator_of_kernel_escape geometry hb ha q hq hk hp H T hH hn hT hTQ hc)

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
