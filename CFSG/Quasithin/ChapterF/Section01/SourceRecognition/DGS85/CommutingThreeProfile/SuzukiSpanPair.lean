module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices
public import Theory.SpecificGroups.Suzuki.OmegaPairGeneration

/-!
# Two actual neighboring spans generate the Suzuki action

The proved first intersection index identifies the image of V_x in the
marked quotient at y with the full Sylow omega. Its two-conjugate generation
lifts through the original quotient map. Thus V_x, V_(g x), and Q_y
generate the actual starred endpoint, with g in that endpoint.

The critical pair and common Sylow remain the earlier source inputs;
neither two-span generation nor a quotient order is assumed. The following
SuzukiSecondKernelUpper consumer uses this equality to combine two fixed
indices. This is the nonbinary case; selection and the binary branch
remain separate obligations of the Chapter 12 family.

Source: DGS85, Groups and Graphs, (12.3)(a), (12.6), printed pp.179,183.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Construct the two generating spans with their literal graph translate. -/
theorem source_suzuki_span_pair_generation
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x m : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    ∃ g ∈ star L S i,
      (V F x 1 ⊔ V F (g • x) 1) ⊔ Q F (base F i) = star L S i := by
  let F := reducedFamily L S
  let A := star L S i
  let Vx := V F x 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hV : Vx ≤ A := (V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hxm).trans
      ((le_sup_left.trans hR.ge).trans (map_subtype_le _))
  let q := ((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := ((originalQuotient h i).symm.trans eSuz).surjective.comp
    (QuotientGroup.mk'_surjective _)
  obtain ⟨_,_,P,hP⟩ := source_suzuki_first_index h i hb hc hxa hxm hym hn eSuz eLin R hR
  obtain ⟨t,ht⟩ := suzukiSylow_exists_omega_pair hn (MulEquiv.refl _) P
  obtain ⟨g,hg⟩ := hq t
  have he : q.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp q := by
    ext v
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv,hg]
  have hmap : ((Vx.subgroupOf A) ⊔
      (Vx.subgroupOf A).map (MulAut.conj g).toMonoidHom).map q = ⊤ := by
    rw [Subgroup.map_sup,map_map,he]
    rw [←map_map (Vx.subgroupOf A) (MulAut.conj t).toMonoidHom q,hP]
    exact ht
  have hker : q.ker = pCore 2 A := by
    ext v
    change eSuz ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) v)) = 1 ↔ v ∈ pCore 2 A
    rw [map_eq_one_iff _ eSuz.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff v
  have hgen := congrArg (Subgroup.comap q) hmap
  rw [comap_map_eq,comap_top,hker] at hgen
  have hsub : A.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G₀ L S)).toMonoidHom.comp A.subtype := by
    ext v
    rfl
  have hh := congrArg (Subgroup.map A.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,map_map,hsub,←map_map,
    map_subgroupOf_eq_of_le hV,←MonoidHom.range_eq_map,range_subtype] at hh
  change (Vx ⊔ Vx.map (MulAut.conj (g : G₀ L S)).toMonoidHom) ⊔ A.pCoreIn 2 = A at hh
  rw [star_core h i,←V_translate F] at hh
  exact ⟨g,g.property,hh⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
