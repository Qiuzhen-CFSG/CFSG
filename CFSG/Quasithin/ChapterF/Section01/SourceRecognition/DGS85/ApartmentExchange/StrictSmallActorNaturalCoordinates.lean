module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorReflection

/-!
# Complete original coordinates on the nonzero strict alpha actor

Use the genuine natural center marking of the whole actor kernel, then
remark both path radicals simultaneously. Inner coordinate transport
preserves that same natural kernel. The full original Cartan fills the
diagonal torus, and the source-selected reversing involution lies inside
the actual actor. All fields of SmallActorPathCoordinates are constructed
from the original strict inputs and the displayed local case conditions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
universe uG
variable {G : Type uG} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S

/-- The original nonzero alpha actor has all natural, root, full-Cartan,
and reflection coordinates on the literal two-root subgroup. -/
theorem strict_source_small_actor_alpha_coordinates
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hCU : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6))≠⊥)
    (htype : ((bOne_tree_cover h).vertex (p.getVert 6)).type=false)
    (hcore : pCore 2 (halfPathActor (X := (A).Universal) p 6)≠⊥) :
    Nonempty (SmallActorPathCoordinates.{uG} p 6 (cartan (chosenCartans h))) := by
  obtain ⟨_,k,fk,fink,chk,_,e,hsurj,hker,⟨nat⟩⟩ :=
    strict_source_small_actor_alpha_natural h hc hne hb hβu hns hlinear
      p hp hl hT hCU htype hcore
  let _ := fk
  let _ := fink
  let _ := chk
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  obtain ⟨K,fK,finK,chK,hK,e'⟩ :=
    original_bTwo_strict_nonbinary_markings h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  let E (w) := Classical.choice (e' w)
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index=Nat.card (K i)+1 := by
    have hadj : (graph F).Adj (base F i) (base F (!i)) :=
      ⟨by change i≠!i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    have he := source_linear_edge_index_of_quotient (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj (E (base F i))
    change (stabilizer F (base F (!i))).relIndex (stabilizer F (base F i)) = _ at he
    rw [show stabilizer F (base F i)=F i from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F (!i))=F (!i) from Subgroup.CosetGeometry.stabilizer_base _ _] at he
    exact he
  have hfield : Nat.card (K v.type)=Nat.card k :=
    Matrix.SL2.field_card_eq_of_equiv ((E v).symm.trans e)
  have hval : Nat.card ((sourceGraph A).neighborSet (p.getVert 6))=Nat.card k+1 := by
    rw [Nat.card_congr (Equiv.ofBijective ((bOne_tree_cover h).hom.mapNeighborSet (p.getVert 6))
      ((bOne_tree_cover h).neighbor_bijective (p.getVert 6)))]
    exact (card_neighbors_of_indices F (fun i => Nat.card (K i)+1) hi v).trans
      (congrArg (fun n => n+1) hfield)
  let c := chosenCartans h
  let d := strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear
  obtain ⟨_,_,z,hR,hV⟩ := source_six_root_coordinates h c d p hp hl hT e hval
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e)
  obtain ⟨x,hx,_,_,_,hrev,_⟩ :=
    strict_source_small_actor_reflection h hc hne hb hβu hns hlinear p hp hl hT
  refine ⟨{ «F» := k, quotient := f
            onto := (MulAut.conj z).surjective.comp hsurj
            kernel_eq := ?_
            natural := nat.marking z
            upper_image := ?_
            lower_elements := ?_
            lower_image := ?_
            diagonal_image := strict_source_small_actor_full_diagonal
              h hc hne hb hβu hns hlinear p hp hl hT e z hR hV
            reflection := ⟨x,hx⟩, reverses := hrev }⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective,hker]
    exact (comap_map_eq_self_of_injective
      (halfPathActor (X := (A).Universal) p 6).subtype_injective _).symm
  · intro y hy
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent k (f y)).mp
      (hR ▸ mem_map_of_mem f hy)
    exact ⟨a,ha.symm⟩
  · intro y hy
    obtain ⟨a,ha⟩ := (hV (f y)).mp (mem_map_of_mem f hy)
    exact ⟨a,ha.symm⟩
  · intro a
    obtain ⟨y,hy,he⟩ := (hV (NaturalCubic.lower a)).mpr ⟨a,rfl⟩
    exact ⟨y,hy,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
