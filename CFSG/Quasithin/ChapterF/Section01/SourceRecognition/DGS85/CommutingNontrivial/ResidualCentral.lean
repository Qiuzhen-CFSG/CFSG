module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientOmegaAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborSylow
public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex

/-!
# Residual fixed vectors in the Chapter 8 comparison

A normal subgroup containing a two-subgroup outside O₂ supplements a local
Sylow: otherwise the rank-one maximal overgroup property puts it in the
Sylow normalizer, whose normal core has no additional two-subgroups.
Its quotient is therefore a two-group, so it contains O².

Apply this to the local centralizer of the intersection of the neighboring
centers. The adjacent core lies in that centralizer and escapes the vertex
core by the original 6.5(a) obstruction. Thus the entire intersection, and
in particular the original H, is fixed by O²(L_alpha'). This supplies the
residual denominator containment used in DGS 8.3, pp.135--136, without
assuming descent or naturality of the whole residual module.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private theorem residual_le_normal_of_two_escape {D : Type*} [Group D] [Finite D]
    (M : IsRankOneModel (D ⧸ pCore 2 D))
    (N A : Subgroup D) [N.Normal] (hA : IsPGroup 2 A)
    (hAN : A ≤ N) (hAQ : ¬ A ≤ pCore 2 D) : pResidual 2 D ≤ N := by
  let S : Sylow 2 D := Classical.choice inferInstance
  have hs : N ⊔ (S : Subgroup D) = ⊤ := by
    by_contra hn
    have hnS : N ≤ normalizer (S : Set D) := le_sup_left.trans
      ((rankOneSylowFacts_of_quotient S (M.rankOneSylowFacts _)).unique_maximal
        (N ⊔ (S : Subgroup D)) le_sup_right (lt_top_iff_ne_top.mpr hn))
    have hAS : A ≤ S := by
      have hh := hA.inf_normalizer_sylow S
      rw [inf_eq_left.mpr (hAN.trans hnS)] at hh
      exact inf_eq_left.mp hh.symm
    have hcore : (normalizer (S : Set D)).pCoreIn 2 = (S : Subgroup D) := by
      apply le_antisymm
      · have hh := pCoreIn_le_sylow (normalizer (S : Set D))
          (S.subtype (S : Subgroup D).le_normalizer)
        intro x hx
        obtain ⟨y,hy,rfl⟩ := hh hx
        exact hy
      · exact le_pCoreIn_of_normalizes S.isPGroup' (S : Subgroup D).le_normalizer le_rfl
    have he := Theory.GroupTheory.AmalgamLocalCores.core_eq_edge_inf_kernel S
      (normalizer (S : Set D)) (S : Subgroup D).le_normalizer
    rw [hcore] at he
    exact hAQ (he.symm ▸ le_inf hAS (hAN.trans (normal_le_normalCore.mpr hnS)))
  exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N (S : Subgroup D) S.isPGroup' hs⟩

private theorem pGroup_inf_action_kernel_le_core {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (M : IsRankOneModel (D ⧸ pCore 2 D))
    (ρ : Representation (ZMod 2) D W) (hr : fixedSpace ρ (pResidual 2 D) = ⊥)
    (A : Subgroup D) (hp : IsPGroup 2 A) : A ⊓ ρ.ker ≤ pCore 2 D := by
  by_contra hn
  have hh := residual_le_normal_of_two_escape M ρ.ker (A ⊓ ρ.ker)
    (hp.to_le inf_le_left) inf_le_right hn
  have he : fixedSpace ρ (pResidual 2 D) = ⊤ := by
    apply top_unique
    intro w _ r
    change ρ r.val w = w
    rw [show ρ r.val = 1 from hh r.property]
    rfl
  exact top_ne_bot (he.symm.trans hr)

private theorem section_actor_kernel_of_commutator {D : Type*} [Group D]
    {L U C E : Subgroup D} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) L W) (c : BinaryConjugationSection L U C ρ)
    (hh : ⁅E,U⁆ ≤ C) : E.subgroupOf L ≤ ρ.ker := by
  intro e he
  apply LinearMap.ext
  intro v
  obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
  let z : U := ⟨(e : D)*u*(e : D)⁻¹,
    (mem_normalizer_iff.mp (c.normalized e.property) u).mp u.property⟩
  have hk : c.coordinates (z*u⁻¹) = 1 :=
    (c.coordinates_eq_one_iff _).mpr (hh (commutator_mem_commutator he u.property))
  rw [map_mul,map_inv,mul_inv_eq_one] at hk
  have hv := c.equivariant e u
  change (c.coordinates z).toAdd = ρ e (c.coordinates u).toAdd at hv
  rw [hk,hu] at hv
  exact hv.symm

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Any locally invariant subgroup centralized by an escaping adjacent core
is centralized by the whole local two-residual. Relative normality is proved
for its centralizer inside the displayed local group. -/
theorem source_residual_centralizes_invariant (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hescape : ¬ Q (family P) w ≤ Q (family P) v)
    (X : Subgroup G) (hn : d.localGroup v ≤ normalizer (X : Set G))
    (hc : Q (family P) w ≤ centralizer (X : Set G)) :
    X ≤ centralizer ((pResidual 2 (d.localGroup v)).map (d.localGroup v).subtype : Set G) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let C := (centralizer (X : Set G)).subgroupOf L
  let A := (Q F w).subgroupOf L
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  have hQL : Q F w ≤ L := (Noncommuting.graph_Q_le_edgeCore h hvw.symm).trans
    (by rw [inf_comm,hR.symm]; exact map_subtype_le _)
  have hNC : L ≤ normalizer (centralizer (X : Set G) : Set G) :=
    hn.trans (normalizer_le_normalizer_centralizer X)
  let : C.Normal := normal_subgroupOf_of_le_normalizer hNC
  have hAQ : ¬ A ≤ pCore 2 L := by
    intro he
    apply hescape
    rw [←localGroup_core_eq F d v]
    intro x hx
    exact ⟨⟨x,hQL hx⟩,he hx,rfl⟩
  have hres : pResidual 2 L ≤ C := residual_le_normal_of_two_escape M C A
    ((isPGroup_pCoreIn 2 (stabilizer F w)).comap_subtype) (comap_mono hc) hAQ
  apply le_centralizer_iff.mp
  rintro x ⟨r,hr,rfl⟩
  exact hres hr

/-- The whole neighboring-center intersection is in the actual residual
centralizer at the vertex. No Chapter 8.3 commutator conclusion is assumed. -/
theorem source_neighbor_intersection_residual_fixed (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hescape : ¬ Q (family P) w ≤ Q (family P) v) :
    neighborCenterIntersection (family P) v ≤
      centralizer ((pResidual 2 (d.localGroup v)).map (d.localGroup v).subtype : Set G) := by
  let := finite_endpoints h
  apply source_residual_centralizes_invariant h hB d hvw M hescape
  · exact (d.local_le v).trans (neighborCenterIntersection_normalized (family P) v)
  · exact (le_centralizer_iff.mp (Z_centralizes_Q (family P) w (source_Z_Q_U h w).1)).trans
      (centralizer_le (iInf_le (fun z : (graph (family P)).neighborSet v => Z (family P) z.val) ⟨w,hvw⟩))

/-- The original nontrivial displacement is killed by the literal
residual-section coordinate map. Its relative normality alone is not used
as a substitute for centralization. -/
theorem source_critical_displacement_residual_fixed (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a') :
    let F := family P
    ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≤ V F a' 1 ⊓
      centralizer ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype : Set G) := by
  let := finite_endpoints h
  have hHZ := (source_critical_commutator_structure h hB d hc hab hd hb hcomm models).2.1
  exact le_inf ((hHZ w).trans (Z_neighbor_le_V (family P) w.property))
    ((le_iInf hHZ).trans (source_neighbor_intersection_residual_fixed h hB d
      w.property (models a') hescape))

/-- On the full residual section, the opposite span has exactly its printed
core kernel and actor order a₁. This does not assert that the whole local
core acts trivially; it identifies the kernel on the actual opposite actor. -/
theorem source_critical_residual_actor_kernel (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (ρ : Representation (ZMod 2) (d.localGroup a') W)
    (c : BinaryConjugationSection (d.localGroup a') (V (family P) a' 1)
      (V (family P) a' 1 ⊓ centralizer
        ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype : Set G)) ρ)
    (hr : fixedSpace ρ (pResidual 2 (d.localGroup a')) = ⊥) :
    let F := family P
    let A := (V F beta 1).subgroupOf (d.localGroup a')
    A ⊓ ρ.ker = (V F beta 1 ⊓ Q F a').subgroupOf (d.localGroup a') ∧
      Nat.card (A.map ρ.asGroupHom) = (Q F a').relIndex (V F beta 1) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let A := (V F beta 1).subgroupOf L
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) beta
  have hVL : V F beta 1 ≤ L := pGroup_le_localGroup F d a' _
    (IsElementaryAbelian.isPGroup 2 _) (V_le_stabilizer_of_dist_add_le_b F h.generate beta a' 1 hd.le)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVL
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  have hcore : pCore 2 L = (Q F a').subgroupOf L := by
    rw [←localGroup_core_eq F d a']
    exact (comap_map_eq_self_of_injective L.subtype_injective _).symm
  have hupper := pGroup_inf_action_kernel_le_core (models a') ρ hr A (IsElementaryAbelian.isPGroup 2 A)
  rw [hcore] at hupper
  have hlower := section_actor_kernel_of_commutator ρ c
    (source_critical_displacement_residual_fixed h hB d hc hab hd hb hcomm models w hescape)
  have he : A ⊓ ρ.ker = (V F beta 1 ⊓ Q F a').subgroupOf L :=
    le_antisymm (fun x hx => ⟨hx.1,hupper hx⟩) (fun x hx => ⟨hx.1,hlower hx⟩)
  refine ⟨he,?_⟩
  have hk : ρ.asGroupHom.ker = ρ.ker := by
    ext x
    exact ⟨fun hx => congrArg Units.val hx,fun hx => Units.ext hx⟩
  rw [←relIndex_ker,hk,←inf_relIndex_right ρ.ker A,inf_comm ρ.ker A,he]
  rw [show (V F beta 1 ⊓ Q F a').subgroupOf L =
      A ⊓ (Q F a').subgroupOf L from rfl,inf_comm A,
    inf_relIndex_right,subgroupOf,relIndex_comap,map_subgroupOf_eq_of_le hVL]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
