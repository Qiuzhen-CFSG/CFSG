module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntrinsic

/-!
# The adjacent cores inside the central seed

The local two-residual moves Q_alpha into the seed. Adjoining the seed to
Q_alpha ∩ Q_beta therefore gives a subgroup normalized by that residual
and by the actual neighboring-core Sylow supplement. It is normal in the
local actor. An opposite lift identifies it with the corresponding join
at the other neighbor. Factoring elements in these equal joins then gives
Q_alpha ∩ Q_beta = (V_beta ∩ Q_alpha) D_alpha.

Consequently the seed is the join of the two adjacent-core intersections,
and the radius/core factor index equals the literal adjacent-core index.
These identities do not assert that the seed is all of Q_alpha. No
saturation, field equality, or classification output is assumed.

Source: DGS, *Groups and Graphs* (1985), the seed argument in (10.7),
printed pp.158--159, with D_alpha as in p.153 and (10.4).
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem core_normalizer (x : Vertex F) :
    stabilizer F x ≤ normalizer (Q F x : Set G) :=
  (stabilizer F x).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The whole adjacent-core intersection is already in the source seed. -/
theorem BTwoCenterActionData.seed_adjacent_intersection
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    Q F v ⊓ Q F m = (V F m 1 ⊓ Q F v) ⊔ D F m t := by
  let := finite_endpoints h
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let J := centralSeed F v m t
  let N := Q F v ⊓ Q F m
  let T := Q F v ⊓ Q F t
  let A := V F m 1 ⊓ Q F v
  let C := V F t 1 ⊓ Q F v
  let R := (pResidual 2 c.actor).map c.actor.subtype
  have hJQ : J ≤ Q F v := sup_le (sup_le inf_le_right inf_le_right) d.separated
  have hJnorm : stabilizer F v ≤ normalizer (J : Set G) :=
    c.seed_stabilizer_normalized h hS hb ht hne
  have hQm : Q F v ≤ stabilizer F m :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F c.middle).trans inf_le_right)
  have hQt : Q F v ≤ stabilizer F t :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F ht).trans inf_le_right)
  have hQmv : Q F m ≤ stabilizer F v := c.neighbor_core_le.trans c.actor_le
  have hE : Q F m ⊔ Q F v ≤ stabilizer F v ⊓ stabilizer F m :=
    sup_le (le_inf hQmv (Q_le_stabilizer F m))
      (le_inf (Q_le_stabilizer F v) hQm)
  have hNnorm : Q F m ⊔ Q F v ≤ normalizer (N : Set G) :=
    (le_inf (hE.trans inf_le_left |>.trans (core_normalizer v))
      (hE.trans inf_le_right |>.trans (core_normalizer m))).trans
        inf_normalizer_le_normalizer_inf
  have hmove : ⁅Q F v,R⁆ ≤ J := by
    have hh := d.core_residual_le_seed h hS hb (hd.symm ▸ c.actor_le)
    rwa [hd] at hh
  have hRactor : R ≤ c.actor := map_subtype_le _
  have hnR : R ≤ normalizer ((N ⊔ J : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact commutator_sup_le_of_relative_normal (Q F v) N J R (N ⊔ J)
      ((le_inf (le_sup_right.trans hNnorm)
        ((Q_le_stabilizer F v).trans hJnorm)).trans
          (normalizer_inf_normalizer_le_normalizer_sup N J))
      inf_le_left hJQ
      (((commutator_mono inf_le_left le_rfl).trans hmove).trans le_sup_right)
      ((le_normalizer_iff_commutator_le_left.mp
        (hRactor.trans (c.actor_le.trans hJnorm))).trans le_sup_right)
  have hn : c.actor ≤ normalizer ((N ⊔ J : Subgroup G) : Set G) := by
    rw [←c.residual_core_supplement h]
    apply sup_le hnR
    exact (le_inf hNnorm (hE.trans inf_le_left |>.trans hJnorm)).trans
      (normalizer_inf_normalizer_le_normalizer_sup N J)
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hconj : N.map (MulAut.conj (g : G)).toMonoidHom = T := by
    dsimp only [N,T]
    rw [map_inf _ _ _ (MulAut.conj (g : G)).injective,←Q_translate,←Q_translate,hg,hgv]
  have hconjJ : J.map (MulAut.conj (g : G)).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (hJnorm (c.actor_le g.property))
  have heq : T ⊔ J = N ⊔ J := by
    have hh := mem_normalizer_iff_map_conj_eq.mp (hn g.property)
    change (N ⊔ J).map (MulAut.conj (g : G)).toMonoidHom = N ⊔ J at hh
    rwa [Subgroup.map_sup,hconj,hconjJ] at hh
  have hVm : V F m 1 ≤ Q F m := graph_V_le_Q_of_short h hS m (by rw [hb]; decide)
  have hVt : V F t 1 ≤ Q F t := graph_V_le_Q_of_short h hS t (by rw [hb]; decide)
  have hAN : A ≤ N := le_inf inf_le_right (inf_le_left.trans hVm)
  have hCT : C ≤ T := le_inf inf_le_right (inf_le_left.trans hVt)
  have hDT : D F m t ≤ T := le_inf d.separated inf_le_right
  have hcover : N ≤ A ⊔ T := by
    apply le_trans (le_sup_left.trans heq.ge)
    apply sup_le le_sup_right
    exact sup_le (sup_le le_sup_left (hCT.trans le_sup_right)) (hDT.trans le_sup_right)
  have hAT : A ≤ normalizer (T : Set G) :=
    (le_inf (inf_le_right.trans (Q F v).le_normalizer)
      (inf_le_right.trans (hQt.trans (core_normalizer t)))).trans
        inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (A : Set G) * (T : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hAT]
      exact hcover hx
    obtain ⟨a,ha,y,hy,rfl⟩ := hxprod
    have hym : y ∈ Q F m := by
      simpa only [inv_mul_cancel_left] using
        (Q F m).mul_mem ((Q F m).inv_mem ((hAN ha).2)) hx.2
    exact (A ⊔ D F m t).mul_mem (mem_sup_left ha) (mem_sup_right ⟨hym,hy.2⟩)
  · exact sup_le hAN (le_inf d.separated inf_le_left)

/-- The seed is generated by the two actual adjacent-core intersections. -/
theorem BTwoCenterActionData.seed_eq_core_intersections
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    centralSeed F v m t = (Q F v ⊓ Q F m) ⊔ (Q F v ⊓ Q F t) := by
  have hI := c.seed_adjacent_intersection h hS hb ht hne
  have hIJ : Q F v ⊓ Q F m ≤ centralSeed F v m t := by
    rw [hI]
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hJnorm := c.seed_stabilizer_normalized h hS hb ht hne
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hconjJ : (centralSeed F v m t).map (MulAut.conj (g : G)).toMonoidHom =
      centralSeed F v m t :=
    mem_normalizer_iff_map_conj_eq.mp (hJnorm (c.actor_le g.property))
  have hTJ : Q F v ⊓ Q F t ≤ centralSeed F v m t := by
    have hh := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hIJ
    rwa [map_inf _ _ _ (MulAut.conj (g : G)).injective,←Q_translate,←Q_translate,
      hg,hgv,hconjJ] at hh
  apply le_antisymm _ (sup_le hIJ hTJ)
  exact sup_le (sup_le
    ((le_inf inf_le_right (inf_le_left.trans
      (graph_V_le_Q_of_short h hS m (by rw [hb]; decide)))).trans le_sup_left)
    ((le_inf inf_le_right (inf_le_left.trans
      (graph_V_le_Q_of_short h hS t (by rw [hb]; decide)))).trans le_sup_right))
    ((le_inf d.separated inf_le_left).trans le_sup_left)

/-- The radius/core index is exactly the adjacent-core index over D. -/
theorem BTwoCenterActionData.seed_factor_index_eq
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    (D F m t).relIndex (Q F v ⊓ Q F m) =
      (D F m t).relIndex (V F m 1 ⊓ Q F v) := by
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hn : Q F v ≤ normalizer (D F m t : Set G) :=
    c.core_le.trans (hd ▸ d.normalized h hS hb)
  let : ((D F m t).subgroupOf (Q F v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer d.separated).mpr hn
  have hh := relIndex_sup_right ((V F m 1 ⊓ Q F v).subgroupOf (Q F v))
    ((D F m t).subgroupOf (Q F v))
  rw [←subgroupOf_sup inf_le_right d.separated,
    relIndex_subgroupOf (sup_le inf_le_right d.separated),
    relIndex_subgroupOf inf_le_right] at hh
  rw [c.seed_adjacent_intersection h hS hb ht hne]
  exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
