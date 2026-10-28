module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.RadiusTwoPaths
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Splitting off the preceding central line

The preceding central line has the full root index at the terminal vertex.
It therefore supplements the terminal core inside Q_(alpha+2). Any subgroup
between that line and Q_(alpha+2) splits over its terminal-core intersection.
For the original fixed subgroup D, the line is central because it is the
omega-center of the preceding local group.

This is the direct-product step in DGS 9.10(4), printed p.148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem split_over_intersection (D Z R : Subgroup G)
    (hZD : Z ≤ D) (hDR : D ≤ Z ⊔ R) (hn : Z ≤ normalizer (R : Set G)) :
    D = Z ⊔ (D ⊓ R) := by
  apply le_antisymm ?_ (sup_le hZD inf_le_left)
  intro d hd
  have hh : d ∈ (Z : Set G) * (R : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right Z R hn]
    exact hDR hd
  obtain ⟨z,hz,r,hr,he⟩ := hh
  have hrD : r ∈ D := by
    have hh := D.mul_mem (D.inv_mem (hZD hz)) hd
    rwa [←he,inv_mul_cancel_left] at hh
  exact he ▸ mul_mem_sup hz ⟨hrD,hr⟩

/-- The actual fixed subgroup splits over the terminal core once the
preceding center line has its source full index and trivial intersection. -/
theorem graph_cartan_fixed_terminal_split
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {l x a' : Vertex (family P)} (hxa' : (graph (family P)).Adj x a')
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e' : (graphLocalGroup (family P) a' ⧸ pCore 2 (graphLocalGroup (family P) a')) ≃* SL(2,F))
    (hωl : Z (family P) l = omegaCenterIn (graphLocalGroup (family P) l))
    (hlcard : Nat.card (Z (family P) l) = Nat.card F)
    (hldis : Disjoint (Z (family P) l) (Q (family P) a'))
    (T : Subgroup G) (hTl : T ≤ graphLocalGroup (family P) l)
    (hDx : Q (family P) l ⊓ centralizer (T : Set G) ≤ Q (family P) x) :
    let D := Q (family P) l ⊓ centralizer (T : Set G)
    D = Z (family P) l ⊔ (D ⊓ Q (family P) a') ∧
      Disjoint (Z (family P) l) (D ⊓ Q (family P) a') ∧
      ⁅Z (family P) l,D ⊓ Q (family P) a'⁆ = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  let D := Q Γ l ⊓ centralizer (T : Set G)
  have hZQ : Z Γ l ≤ Q Γ l := (source_Z_Q_U h l).1.trans
    (fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1)
  have hZL : Z Γ l ≤ centralizer (graphLocalGroup Γ l : Set G) := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp (hωl ▸ hz)).2.1
  have hZD : Z Γ l ≤ D := le_inf hZQ (hZL.trans (centralizer_le hTl))
  have hi : (Q Γ a').relIndex (Z Γ l) = Nat.card F := by
    rw [←inf_relIndex_left,(disjoint_iff.mp hldis),relIndex_bot_left,hlcard]
  have hprod := linear_local_pgroup_saturation h a' e' (Z Γ l) (Q Γ x) (hZD.trans hDx)
    (neighbor_core_le_localGroup h hB hS hxa'.symm) (isPGroup_pCoreIn 2 _) hi
  have hzn : Z Γ l ≤ normalizer (Q Γ a' : Set G) :=
    ((hZD.trans hDx).trans ((source_Z_Q_U h x).2.trans
      ((ballKernel_one_le_edge Γ hxa').trans inf_le_right))).trans (stabilizer_normalizes_Q Γ a')
  refine ⟨split_over_intersection D (Z Γ l) (Q Γ a') hZD ?_ hzn,
    hldis.mono_right inf_le_right,?_⟩
  · exact hDx.trans (hprod.le.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right)))
  · exact commutator_eq_bot_iff_le_centralizer.mpr (hZL.trans
      (centralizer_le ((inf_le_left.trans inf_le_left).trans (core_le_graphLocalGroup h l))))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
