module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourRecognitionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalVerticesSource

/-!
# The actual original field-four Cartan

Transport the constructed beta Cartan through the reduced-completion
inclusion. It is an element of order three in the full original Borel,
and its cyclic subgroup complements the full Borel two-core inside the
original beta enlargement's Borel. The linear enlargement theorem identifies
that Borel with the original starred-parabolic intersection, retaining all
original scalar, projective and endpoint maps.

The alpha field restriction is discharged by the earlier exceptional
argument. The Cartan lies in the image of the actual alpha permutation
kernel and normalizes every original neighboring core intersection.
The earlier (7.4) commutator and natural-center hypotheses remain explicit.
This supplies the original invariance inputs for DGS (5.16); constructing
the two four-group complements and the J₂ parabolic equivalence remains.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.16), pp.116--117, (10.9), p.163, and the original reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourCartanAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- The original field-four Cartan complements the full Borel two-core
inside the actual beta enlargement's Borel. It preserves every literal
neighboring core intersection and lies in the alpha permutation kernel. -/
theorem original_bTwo_field_four_cartan
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    ∃ a : commonBorel L S, orderOf a = 3 ∧
      (a : G) ∈ enlargedEndpoint L S 1 ∧
      (a : G) ∈ (U F₀ α).map (G₀ L S).subtype ∧
      Disjoint ((commonBorel L S).pCoreIn 2) (zpowers (a : G)) ∧
      (commonBorel L S).pCoreIn 2 ⊔ zpowers (a : G) =
        enlargedEndpoint L S 1 ⊓ commonBorel L S ∧
      ∀ μ, (graph F₀).Adj α μ →
        (Q F₀ μ).map (G₀ L S).subtype = (V F₀ μ 1).map (G₀ L S).subtype ∧
        (a : G) ∈ normalizer
          (((Q F₀ μ).map (G₀ L S).subtype ⊓ (parabolic L S 0).pCoreIn 2 : Subgroup G) : Set G) := by
  let ι := (G₀ L S).subtype
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  have hk := (original_bTwo_exceptional_fields_and_orders h hb c hactor hcentral
    ht hne hcomm hnot e hD E).1
  obtain ⟨a,ha,hoa,hU,hd,hgen,hfactors⟩ := c.field_four_cartan (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb ht hne hD' eβ hk hK
  change a ∈ graphLocalGroup F₀ β at ha
  change a ∈ U F₀ α at hU
  change Disjoint ((stabilizer F₀ α ⊓ stabilizer F₀ β).pCoreIn 2) (zpowers a) at hd
  change (stabilizer F₀ α ⊓ stabilizer F₀ β).pCoreIn 2 ⊔ zpowers a =
    graphLocalGroup F₀ β ⊓ stabilizer F₀ α at hgen
  change ∀ μ, (graph F₀).Adj α μ → Q F₀ μ = V F₀ μ 1 ∧
    a ∈ normalizer ((Q F₀ μ ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)) at hfactors
  have hSmap : ((stabilizer F₀ α ⊓ stabilizer F₀ β).pCoreIn 2).map ι =
      (commonBorel L S).pCoreIn 2 := by
    have hh := c.core_product_eq_edge_core (reduced_triple h)
    change Q F₀ β ⊔ Q F₀ α = (stabilizer F₀ β ⊓ stabilizer F₀ α).pCoreIn 2 at hh
    have he : (stabilizer F₀ α ⊓ stabilizer F₀ β).pCoreIn 2 = Q F₀ β ⊔ Q F₀ α := by
      simpa only [inf_comm] using hh.symm
    rw [he,Subgroup.map_sup,reduced_base_Q_map h true,reduced_base_Q_map h false]
    exact (sup_comm _ _).trans (original_bTwo_borel_core_eq_product h c).symm
  have hBmap : (stabilizer F₀ α ⊓ stabilizer F₀ β).map ι = B₀ L S := by
    have he : stabilizer F₀ α ⊓ stabilizer F₀ β = (B₀ L S).subgroupOf (G₀ L S) := by
      simp only [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
      exact (reduced_triple h).intersection
    rw [he,map_subgroupOf_eq_of_le (show B₀ L S ≤ G₀ L S from le_sup_right.trans le_sup_left)]
  have hLocal : (graphLocalGroup F₀ β).map ι = enlargedEndpoint L S 1 :=
    reduced_graphLocalGroup_image h true
  have hEB : (graphLocalGroup F₀ β ⊓ stabilizer F₀ α).map ι =
      enlargedEndpoint L S 1 ⊓ commonBorel L S := by
    have he : graphLocalGroup F₀ β ⊓ stabilizer F₀ α =
        graphLocalGroup F₀ β ⊓ (stabilizer F₀ α ⊓ stabilizer F₀ β) := by
      apply le_antisymm
      · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (sylowGenerated_le _)))
      · exact le_inf inf_le_left (inf_le_right.trans inf_le_left)
    rw [he,map_inf _ _ _ (G₀ L S).subtype_injective,hLocal,hBmap,
      reduced_enlargedEndpoint_eq_starred_of_linear h 1 e]
    exact (inf_comm _ _).trans ((B₀_inf_star h 1).trans (inf_comm _ _))
  have hjoin : (commonBorel L S).pCoreIn 2 ⊔ zpowers (ι a) =
      enlargedEndpoint L S 1 ⊓ commonBorel L S := by
    have hh := congrArg (map ι) hgen
    rwa [Subgroup.map_sup,hSmap,MonoidHom.map_zpowers,hEB] at hh
  have haB : ι a ∈ commonBorel L S :=
    (hjoin ▸ (show ι a ∈ (commonBorel L S).pCoreIn 2 ⊔ zpowers (ι a) from
      mem_sup_right (mem_zpowers _))).2
  let aB : commonBorel L S := ⟨ι a,haB⟩
  refine ⟨aB,?_,?_,?_,?_,hjoin,?_⟩
  · exact (Subgroup.orderOf_coe aB).symm.trans
      ((Subgroup.orderOf_coe a).trans hoa)
  · change ι a ∈ enlargedEndpoint L S 1
    rw [←hLocal]
    exact mem_map_of_mem ι ha
  · exact mem_map_of_mem ι hU
  · have hh := disjoint_map (G₀ L S).subtype_injective hd
    rw [hSmap,MonoidHom.map_zpowers] at hh
    exact hh
  · intro μ hμ
    obtain ⟨hcore,hn⟩ := hfactors μ hμ
    refine ⟨congrArg (map ι) hcore,?_⟩
    have hh := (Q F₀ μ ⊓ Q F₀ α).le_normalizer_map ι (mem_map_of_mem ι hn)
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h false] at hh
    exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
