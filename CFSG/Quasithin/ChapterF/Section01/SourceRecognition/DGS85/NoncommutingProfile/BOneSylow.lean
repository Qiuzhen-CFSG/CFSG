module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The literal common Sylow product in the b=1 branch

The inverse image of the marked neighbor Sylow is exactly the product
of the two actual vertex cores. Its two-group kernel makes it Sylow in
the local actor; the actor contains a full vertex Sylow, so the same
product is Sylow in the full vertex stabilizer. Relative indices compute
its order without assuming the ambient completion finite.

The whole Borel normalizes this product. If it also normalizes the local
actor, Borel maximality forces the actor normalizer of the product into
the Borel. Thus every element of the marked SL₂ Sylow normalizer lifts
inside the original full Borel. This supplies the Cartan action used in
the center-order calculation, rather than postulating a fixed-line action.

Source: DGS, *Groups and Graphs* (1985), 6.0--6.2, 7.1(c), and the
proof of 10.5(c), printed pp.118--119,126,156. The actor normalization
is an earlier Chapter 6 premise; no path parameter is asserted here.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W)

/-- The Sylow inverse image is the literal neighbor-core product. -/
theorem neighbor_core_product_preimage
    (hcore : Q (family P) w = Z (family P) w) :
    (c.imageSylow : Subgroup SL(2,k)).comap c.quotient =
      (Q (family P) w ⊔ Q (family P) v).subgroupOf c.actor := by
  have hm : ((Q (family P) w).subgroupOf c.actor).map c.quotient = c.imageSylow := by
    rw [hcore,c.neighbor_image]
  rw [←hm,comap_map_eq,c.kernel,subgroupOf_sup c.neighbor_core_le c.core_le]

include c in
/-- The same core product is Sylow in the full vertex stabilizer. -/
theorem core_product_sylow (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) w = Z (family P) w) :
    Stellmacher.IsSylowSubgroupIn (Q (family P) w ⊔ Q (family P) v)
      (stabilizer (family P) v) := by
  let := finite_endpoints h
  have hk : IsPGroup 2 c.quotient.ker := by
    rw [c.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer (family P) v)).comap_subtype
  let T := c.imageSylow.comapOfKerIsPGroup c.quotient hk
    (by rw [MonoidHom.range_eq_top.mpr c.onto]; exact le_top)
  have hS : Stellmacher.IsSylowSubgroupIn
      (Q (family P) w ⊔ Q (family P) v) c.actor := by
    refine ⟨T,?_⟩
    change ((c.imageSylow : Subgroup SL(2,k)).comap c.quotient).map c.actor.subtype = _
    rw [neighbor_core_product_preimage c hcore,
      map_subgroupOf_eq_of_le (sup_le c.neighbor_core_le c.core_le)]
  have hle : (c.sylow : Subgroup (stabilizer (family P) v)) ≤
      c.actor.subgroupOf (stabilizer (family P) v) := by
    intro x hx
    exact c.sylow_le_actor (mem_map_of_mem _ hx)
  have hi : ¬ 2 ∣ c.actor.relIndex (stabilizer (family P) v) :=
    fun hd => c.sylow.not_dvd_index (hd.trans (index_dvd_of_le hle))
  exact Noncommuting.sylow_in_overgroup_of_odd_relIndex _ _ _ c.actor_le hS hi

private theorem core_normalized (F : Bool → Subgroup G) (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) := by
  simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
    using (pCore 2 (stabilizer F v)).le_normalizer_map (stabilizer F v).subtype

local instance bOneSylowFieldAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

include c in
/-- Natural fixed index computes the actual common Sylow order. -/
theorem core_product_card (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card (Q (family P) w ⊔ Q (family P) v : Subgroup G) =
      Nat.card (Q (family P) w) * Nat.card k := by
  let := finite_endpoints h
  let : Finite (Q (family P) w) := Finite.of_injective
    (inclusion (Q_le_stabilizer (family P) w))
    (inclusion_injective _)
  have hn : Q (family P) w ≤ normalizer (Q (family P) v : Set G) :=
    (source_Z_Q_U h w).2.trans
      ((ballKernel_one_le_edge (family P) c.adjacent.symm).trans
        (inf_le_right.trans (core_normalized (family P) v)))
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (Q (family P) w)
    (Q (family P) w ⊔ Q (family P) v) bot_le le_sup_left
  simp only [relIndex_bot_left] at hc
  have hi : (Q (family P) w).relIndex (Q (family P) w ⊔ Q (family P) v) = Nat.card k := by
    rw [sup_comm (Q (family P) w),relIndex_sup_of_normalizes _ _ hn,hcore,
      opposite_core_index_of_natural c E]
  rw [hi] at hc
  exact hc.symm

/-- The whole source Borel realizes the quotient Sylow normalizer. -/
theorem base_borel_lifts_sylow_normalizer (h : LocallyRankOneTriple P B) (i : Bool)
    (c : BOneActionData (family P) (base (family P) i) (base (family P) (!i)) k W)
    (hcore : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i)))
    (hnActor : B ≤ normalizer (c.actor : Set G)) :
    ∀ g ∈ normalizer (c.imageSylow : Set SL(2,k)),
      ∃ a : c.actor, (a : G) ∈ B ∧ c.quotient a = g := by
  let F := family P
  let v := base F i
  let w := base F (!i)
  let T := Q F w ⊔ Q F v
  let M := c.actor ⊓ normalizer (T : Set G)
  have hT : T ≤ c.actor := sup_le c.neighbor_core_le c.core_le
  have hpre : (c.imageSylow : Subgroup SL(2,k)).comap c.quotient = T.subgroupOf c.actor :=
    neighbor_core_product_preimage c hcore
  have heB : stabilizer F v ⊓ stabilizer F w = B := by
    cases i <;> simpa only [F,v,w,stabilizer,Subgroup.CosetGeometry.stabilizer_base,family,
      Bool.not_false,Bool.not_true,inf_comm (P 1) (P 0)] using h.intersection
  have hnT : B ≤ normalizer (T : Set G) := by
    have hv := heB ▸ (inf_le_left : stabilizer F v ⊓ stabilizer F w ≤ stabilizer F v)
    have hw := heB ▸ (inf_le_right : stabilizer F v ⊓ stabilizer F w ≤ stabilizer F w)
    exact (le_inf (hw.trans (core_normalized F w)) (hv.trans (core_normalized F v))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnM : B ≤ normalizer (M : Set G) :=
    (le_inf hnActor (hnT.trans (normalizer (T : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hmN (a : c.actor) : (a : G) ∈ M ↔ c.quotient a ∈ normalizer (c.imageSylow : Set SL(2,k)) := by
    have he := congrArg (fun K : Subgroup c.actor => a ∈ K)
      (comap_normalizer_eq_of_surjective (c.imageSylow : Subgroup SL(2,k)) c.onto)
    rw [hpre] at he
    rw [←subgroupOf_normalizer_eq hT] at he
    exact (and_iff_right a.property).trans (Iff.of_eq he.symm)
  have hMB : M ≤ B := by
    have hp : M ⊔ B ≤ stabilizer F v :=
      sup_le (inf_le_left.trans c.actor_le) (heB ▸ inf_le_left)
    have hd : M ⊔ B = B ∨ M ⊔ B = stabilizer F v := by
      cases i
      · simpa only [F,v,stabilizer,Subgroup.CosetGeometry.stabilizer_base,family] using
          source_borel_maximal (Classical.choice (h.local_data 0)) _ le_sup_right
            (by simpa only [F,v,stabilizer,Subgroup.CosetGeometry.stabilizer_base,family] using hp)
      · simpa only [F,v,stabilizer,Subgroup.CosetGeometry.stabilizer_base,family] using
          source_borel_maximal (Classical.choice (h.local_data 1)) _ le_sup_right
            (by simpa only [F,v,stabilizer,Subgroup.CosetGeometry.stabilizer_base,family] using hp)
    rcases hd with he | he
    · exact le_sup_left.trans he.le
    · have hAM : c.actor ≤ M := by
        intro a ha
        have hx : a ∈ (M : Set G) * (B : Set G) := by
          rw [←coe_mul_of_right_le_normalizer_left M B hnM,he]
          exact c.actor_le ha
        obtain ⟨m,hm,b,hb,rfl⟩ := hx
        have hbA : b ∈ c.actor := by
          simpa only [inv_mul_cancel_left] using c.actor.mul_mem (c.actor.inv_mem hm.1) ha
        exact M.mul_mem hm ⟨hbA,hnT hb⟩
      exfalso
      apply Matrix.SpecialLinearGroup.sylow_normalizer_ne_top c.imageSylow
      apply top_unique
      intro g _
      obtain ⟨a,rfl⟩ := c.onto g
      exact (hmN a).mp (hAM a.property)
  intro g hg
  obtain ⟨a,rfl⟩ := c.onto g
  exact ⟨a,hMB ((hmN a).mpr hg),rfl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
