module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedTerminal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SecondKernel

/-!
# Radius-two control from a Cartan-kernel factor

Let D supplement the vertex two-core in the intrinsic local group, and
let A be a subgroup of that core normalized by D and the full edge Cartan.
If the Cartan's nontrivial part in the full local permutation kernel
centralizes D, then A fixes the entire radius-two ball. The adjacent-kernel
intersection theorem and the second Cartan-fixed neighbor first put A in
the neighboring core. Supplementation makes D transitive on all neighbors;
normalization transports the containment to every neighboring core.

Both incident linear fields are nonbinary. Relative normalization, the
actual two-core and full permutation kernel are kept distinct. The literal
four-path application is in ElementaryActorSecondKernel.
Source: DGS, Groups and Graphs (1985), (14.5)(c), p.213; the adjacent-kernel
and Cartan propagation arguments are the nonbinary linear case of (9.10),
pp.147--148.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A normalized subgroup of the vertex core centralizing the nontrivial
Cartan-kernel factor lies in every neighboring core, hence the second kernel. -/
theorem source_linear_actor_subgroup_le_second_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (ht : RootPathTransitive (graph (family P)) G v 2)
    {k l : Type*} [Field k] [Finite k] [CharP k 2] [Field l] [Finite l] [CharP l 2]
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,k))
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,l))
    (hk : 4 ≤ Nat.card k) (hl : 4 ≤ Nat.card l)
    (C D A : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAQ : A ≤ Q (family P) v) (hCA : C ≤ normalizer (A : Set G))
    (hDA : D ≤ normalizer (A : Set G))
    (hcover : D ⊔ Q (family P) v = graphLocalGroup (family P) v)
    (hcentral : C ⊓ U (family P) v ≤ centralizer (D : Set G))
    (hAD : A ≤ D) (hne : C ⊓ U (family P) v ≠ ⊥) :
    A ≤ ballKernel (family P) v 2 := by
  let Γ := family P
  have hAW : A ≤ Q Γ w := cartan_kernel_centralizer_le_neighbor_core h hB hS hvw ht ew
    C A (C ⊓ U Γ v) hCE hd hg hAQ hCA inf_le_left inf_le_right
    (ho.of_dvd_nat (card_dvd_of_le (show C ⊓ U Γ v ≤ C from inf_le_left))) hne
    (hcentral.trans (centralizer_le hAD))
    (nonbinary_adjacent_kernel_intersection h hB hS hvw ev ew hk hl)
  have hD : D ≤ graphLocalGroup Γ v := hcover ▸ le_sup_left
  have hDN : D ≤ normalizer (Q Γ v : Set G) :=
    (hD.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ v)
  have hall : A ≤ neighborCoreIntersection Γ v := by
    apply le_iInf
    intro z
    obtain ⟨g,hgD,hgz⟩ : ∃ g∈D, g • w=z.val := by
      obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive h hB hS v ⟨w,hvw⟩ z
      have hprod : g∈(D : Set G)*(Q Γ v : Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right D (Q Γ v) hDN,hcover]
        exact hg
      obtain ⟨d,hd,q,hq,rfl⟩ := hprod
      refine ⟨d,hd,?_⟩
      have hqw : q • w=w := (source_Z_Q_U h v).2 hq w
        ((mem_ball_one Γ v w).mpr (Or.inl hvw))
      simpa only [mul_smul,hqw] using hgz
    intro x hx
    have hconj : g⁻¹*x*g ∈ A := by
      have hh := (mem_normalizer_iff.mp (hDA (D.inv_mem hgD)) x).mp hx
      simpa only [inv_inv] using hh
    rw [←hgz,Q_translate]
    refine ⟨g⁻¹*x*g,hAW hconj,?_⟩
    change g*(g⁻¹*x*g)*g⁻¹=x
    group
  exact hall.trans (source_neighborCoreIntersection_le_second_kernel h hvw.symm)
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
