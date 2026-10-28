module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Eight.Products
public import Theory.GroupTheory.InvolutionTransferResidual
public import Mathlib.GroupTheory.IsPerfect

/-!
# The transfer conclusion of the A₈ argument

The permutation calculation must put every Sylow involution into A by
L-conjugacy, give index two for T ∩ L⟨rz⟩, and put the five marked elements
outside L⟨rz⟩. The proved class intersection then gives nonfusion into
that subgroup. Thompson transfer puts z outside O²(G), which is all of G
for a finite nonabelian simple group.

Only the elementary permutation and index calculations are retained as
inputs here. In particular, nonfusion is a conclusion. Source:
Aschbacher–Smith, proof of 16.4.9(2), printed p.1192.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
open Subgroup
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G} {T : Sylow 2 G}

/-- The model calculations needed for transfer. The overgroup is the actual
L⟨rz⟩; none of these fields asserts an ambient fusion exclusion. -/
structure TransferGeometry (F : MarkedEmbedding L z r) (T : Sylow 2 G) : Prop where
  sylow_le : (T : Subgroup G) ≤ AlternatingOvergroup L z r
  cover : ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
    ∃ l ∈ L, MulAut.conj l t ∈ F.subgroup
  index : (L ⊔ zpowers (r * z)).relIndex (T : Subgroup G) = 2
  avoids : ∀ i, F.mark i ∉ L ⊔ zpowers (r * z)

variable [Finite G]
namespace MarkedEmbedding

/-- No conjugate of z in T belongs to the actual subgroup L⟨rz⟩. -/
theorem nonfusion (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) (Q : TransferGeometry F T)
    {t : G} (ht : t ∈ (T : Subgroup G)) (hc : IsConj z t) :
    t ∉ L ⊔ zpowers (r * z) := by
  have ht2 : orderOf t = 2 := by
    obtain ⟨x, hx⟩ := isConj_iff.mp hc
    have hx' : MulAut.conj x z = t := hx
    rw [← hx', (MulAut.conj x).orderOf_eq, h.involution]
  obtain ⟨l, hl, hlt⟩ := Q.cover t ht ht2
  have hcl : IsConj z (MulAut.conj l t) := hc.trans (isConj_iff.mpr ⟨l, rfl⟩)
  have hmark : MulAut.conj l t ∈ Set.range F.mark := by
    rw [← F.class_intersection_eq_marks h hsmall hempty hdis hr P]
    exact ⟨hcl, hlt⟩
  obtain ⟨i, hi⟩ := hmark
  intro hmem
  apply Q.avoids i
  rw [hi]
  exact (L ⊔ zpowers (r * z)).mul_mem
    ((L ⊔ zpowers (r * z)).mul_mem (mem_sup_left hl) hmem)
    ((L ⊔ zpowers (r * z)).inv_mem (mem_sup_left hl))

/-- The exact residual conclusion of Thompson transfer, keeping O²(G). -/
theorem not_mem_twoResidual (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) (Q : TransferGeometry F T) :
    z ∉ pResidual 2 G := by
  apply T.not_mem_twoResidual_of_nonfusion_index_two
    ((L ⊔ zpowers (r * z)).subgroupOf (T : Subgroup G)) Q.index
    ⟨z, h.mem_sylow⟩ ((orderOf_coe _).symm.trans h.involution)
  intro other hc
  exact F.nonfusion h hsmall hempty hdis hr P Q other.property hc

end MarkedEmbedding

private theorem twoResidual_eq_top_of_simple [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G) : pResidual 2 G = ⊤ := by
  let : Group.IsPerfect G := ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (_root_.commutator G) inferInstance).resolve_left
      (fun he => hnonab ((commutator_eq_bot_iff G).mp he))⟩
  apply (pResidual_eq_top_iff 2 G).mpr
  intro N hN hp
  let := hN
  have hsub : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- Conditional endgame: the marked permutation construction and its actual
placements discharge the A₈ contradiction. Their existence is not assumed
by the source theorem and must be supplied by its assembly. -/
theorem deltaZero_nonempty_of_geometry [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G)
    (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) (Q : TransferGeometry F T) :
    (deltaZero L).Nonempty := by
  by_contra hempty
  have hn := F.not_mem_twoResidual h hsmall hempty hdis hr P Q
  rw [twoResidual_eq_top_of_simple hnonab] at hn
  exact hn (mem_top z)

end CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
