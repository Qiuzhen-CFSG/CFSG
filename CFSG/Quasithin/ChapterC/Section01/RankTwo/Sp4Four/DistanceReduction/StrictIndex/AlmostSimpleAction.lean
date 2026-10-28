module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Action
public import Theory.GroupTheory.NormalSectionResidualMonolith

/-!
# The terminal action with the original local quotient

The actual vertex quotient may have an outer part. Its simple residual
image with trivial centralizer suffices for the terminal action argument:
an actor escaping Q and fixing a normal local section modulo Z forces the
local residual to fix that section. Any part of that section in the radius
subgroup then lies in the literal fixed preimage B. No removal of outer
automorphisms is assumed.

Source: Meierfrankenfeld–Stellmacher (1993), final paragraph of (5.9),
printed p.922. The preceding span invariance and kernel escape remain
the separate source inputs to this action step.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  (geometry : Geometry R)

/-- The actual simple residual image fixes a normal local section.
The section need only lie in the stabilizer, not in the radius subgroup. -/
theorem normal_local_commutator_of_monolithic_kernel_escape
    {a : Vertex R}
    {J : Type*} [Group J]
    (q : stabilizer R a →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R a)).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R a)).map q : Set J) = ⊥)
    (H T : Subgroup (FreeAmalgam R)) (hH : H ≤ stabilizer R a)
    (hn : stabilizer R a ≤ normalizer (H : Set _))
    (hT : T ≤ stabilizer R a) (hTQ : ¬ T ≤ Q R a)
    (hc : ⁅H,T⁆ ≤ Z R a) : ⁅H,Ltilde R a⁆ ≤ Z R a := by
  let G := stabilizer R a
  let D := H.subgroupOf G
  let Z₀ := (Z R a).subgroupOf G
  let T₀ := T.subgroupOf G
  let := finite_stabilizer R a
  let := hS
  let : D.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Z₀.Normal := normal_subgroupOf_of_le_normalizer (Z_normalized R a)
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
    (commutator_pResidual_le_of_monolithic_kernel_escape 2 q hq hker hC
      D Z₀ T₀ hescape hc₀)
  rw [map_commutator, map_subgroupOf_eq_of_le hH,
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at hh
  exact hh

/-- The radius-section version of the local normal-section action. -/
theorem normal_radius_commutator_of_monolithic_kernel_escape
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {J : Type*} [Group J]
    (q : stabilizer R a →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R a)).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R a)).map q : Set J) = ⊥)
    (H T : Subgroup (FreeAmalgam R)) (hH : H ≤ V R a)
    (hn : stabilizer R a ≤ normalizer (H : Set _))
    (hT : T ≤ stabilizer R a) (hTQ : ¬ T ≤ Q R a)
    (hc : ⁅H,T⁆ ≤ Z R a) : ⁅H,Ltilde R a⁆ ≤ Z R a :=
  normal_local_commutator_of_monolithic_kernel_escape q hq hk hp hS hC
    H T ((hH.trans (geometry.V_le_Q hb a ha)).trans (fun _ hx => hx.1)) hn hT hTQ hc

/-- The original fixed preimage contains the normal section using only
the simple self-centralizing residual image in the actual quotient. -/
theorem normal_radius_le_B_of_monolithic_kernel_escape
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {J : Type*} [Group J]
    (q : stabilizer R a →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R a)).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R a)).map q : Set J) = ⊥)
    (H T : Subgroup (FreeAmalgam R)) (hH : H ≤ V R a)
    (hn : stabilizer R a ≤ normalizer (H : Set _))
    (hT : T ≤ stabilizer R a) (hTQ : ¬ T ≤ Q R a)
    (hc : ⁅H,T⁆ ≤ Z R a) : H ≤ B R a (geometry.Z_normal a) :=
  radius_le_B_of_commutator geometry hb ha H hH
    (normal_radius_commutator_of_monolithic_kernel_escape geometry hb ha
      q hq hk hp hS hC H T hH hn hT hTQ hc)

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
