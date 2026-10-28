module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorRootCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCartan
public import Theory.SpecificGroups.SL2.OppositeRootCartan
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanCentralizer

/-!
# The full diagonal torus in the actual strict-root coordinates

The original Cartan's intersection with the midpoint actor has order q-1
and lies in the actual half-path actor. It normalizes both marked roots and
meets the quotient kernel trivially, so its image is the entire diagonal
torus in their same coordinates. The source package constructs the field,
quotient and root markings internally before applying this calculation.
No natural kernel action or apartment exchange is assumed.

Source: DGS, Groups and Graphs (1985), (14.3)(b), p.212, and (14.11), p.217.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
  (c : CompatibleCartans L (reducedSylow L S))
  (t : Bool → (reducedAmalgam L S).Universal)
  (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal))
  {a b : SourceVertex (reducedAmalgam L S)}
  (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (hl : p.length = 12)
  (hT : ∀ z ∈ p.support, z ∈ cartanApartment (reducedAmalgam L S) (reflectionGroup c t))
  (hCD : cartan c ⊓
    (graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) ≤
      halfPathActor (X := (reducedAmalgam L S).Universal) p 6)

include hCD hT htnorm in
private theorem six_actor_full_diagonal
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,k))
    (z : SL(2,k))
    (hR : ((pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf
      (halfPathActor (X := (A).Universal) p 6)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e))=
          Matrix.SpecialLinearGroup.upperUnipotent k)
    (hV : ∀ y : SL(2,k), y∈((pathRoot (X := (A).Universal) (p.take 6)).subgroupOf
      (halfPathActor (X := (A).Universal) p 6)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e)) ↔
      ∃ a : k, NaturalCubic.lower a=y) :
    ∀ a : k, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
      ((cartan c).subgroupOf (halfPathActor (X := (A).Universal) p 6)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e)) := by
  let D := halfPathActor (X := (A).Universal) p 6
  let R := (pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf D
  let V := (pathRoot (X := (A).Universal) (p.take 6)).subgroupOf D
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 6)
  let w := cov.vertex (p.getVert 7)
  let J := graphLocalGroup F v
  let C₀ := (cartan c).map φ
  let C := (cartan c ⊓ J.comap φ).subgroupOf D
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 6 hl)
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e)
  have hpker : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]
    exact halfPathLinearMap_kernel_isTwo h p 6 hl e
  have hCm : C.map (φ.comp D.subtype)=C₀ ⊓ J := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_map_of_mem φ hy.1,hy.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hyJ⟩
      exact ⟨⟨y,hCD ⟨hy,hyJ⟩⟩,⟨hy,hyJ⟩,rfl⟩
  have hoC : Odd (Nat.card C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCD).toEquiv]
    exact (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
      (card_dvd_of_le (show cartan c ⊓ J.comap φ ≤ cartan c from inf_le_left))
  have hCk : Disjoint C f.ker := by
    obtain ⟨r,hr⟩ := hpker.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact hoC.coprime_two_right.pow_right r)
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  have hCE : C₀ ≤ stabilizer F v ⊓ stabilizer F w := by
    rintro _ ⟨x,hx,rfl⟩
    constructor
    · change φ x • cov.vertex (p.getVert 6)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 6))]
    · change φ x • cov.vertex (p.getVert 7)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 7))]
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=T false ⊓ T true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hC0 : C₀ ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E ≤ normalizer (W : Set G₀) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C₀) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd0 : Disjoint C₀ (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg0 : C₀ ⊔ E.pCoreIn 2=E := by
    apply le_antisymm (sup_le hC0 (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    exact he.symm.le.trans (sup_le (hWcore.trans le_sup_right) le_sup_left)
  have hEbase : E=stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [show stabilizer F (base F false)=F false from Subgroup.CosetGeometry.stabilizer_base F false,
      show stabilizer F (base F true)=F true from Subgroup.CosetGeometry.stabilizer_base F true]
  have hbase : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨hd,hg⟩ := CommutingTrivial.path_cartan_complement_at_edge (reduced_triple h)
    hbase hvw C₀ (hEbase ▸ hC0) hCE ho (hEbase ▸ hd0) (hEbase ▸ hg0)
  obtain ⟨⟨etor⟩,_⟩ := CommutingTrivial.edge_complement_local_torus (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw e C₀ hCE hd hg
  have hCn (q : (sourceGraph A).Walk a (p.getVert 6))
      (hqT : ∀ x∈q.support, x∈cartanApartment A (reflectionGroup c t)) :
      C ≤ normalizer ((pathRoot (X := (A).Universal) q).subgroupOf D : Set D) := by
    intro x hx
    have hfix : x.val∈pathFixer (X := (A).Universal) q := by
      intro j _
      exact reflectionApartment_fixed c t htnorm x.val hx.1 _ (hqT _ (q.getVert_mem_support j))
    have hn := pathFixer_le_normalizer_pathRoot q hfix
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp hn y.val
  have hCR : C ≤ normalizer (R : Set D) := by
    intro x hx
    have hfix : x.val∈pathFixer (X := (A).Universal) (p.drop 6) := by
      intro j _
      rw [drop_getVert]
      exact reflectionApartment_fixed c t htnorm x.val hx.1 _ (hT _ (p.getVert_mem_support _))
    have hn := pathFixer_le_normalizer_pathRoot (p.drop 6) hfix
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp hn y.val)
  have hCV : C ≤ normalizer (V : Set D) := by
    apply hCn (p.take 6)
    intro x hx
    rw [support_take] at hx
    exact hT x (List.mem_of_mem_take hx)
  have hφi : Function.Injective (φ.comp D.subtype) := by
    intro x y he
    apply halfPathLocalMap_injective h p 6 hl
    exact Subtype.ext he
  have hcC : Nat.card C=Nat.card k-1 := by
    rw [←card_map_of_injective (f := φ.comp D.subtype) hφi,hCm]
    exact (Nat.card_congr etor.toEquiv).trans (Nat.card_units (α := k))
  have hfi : Function.Injective (f.comp C.subtype) := by
    intro x y he
    apply Subtype.ext
    apply inv_mul_eq_one.mp
    apply disjoint_def.mp hCk (C.mul_mem (C.inv_mem x.property) y.property)
    change f (x.val⁻¹*y.val)=1
    change f x.val=f y.val at he
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hf := Matrix.SpecialLinearGroup.full_diagonal_image_of_opposite_roots
    f R V C hR hV hCR hCV hfi hcC
  intro a ha
  exact map_mono (show C ≤ (cartan c).subgroupOf D from fun _ hx => hx.1) (hf a ha)

variable {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : DGS85.b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))


/-- The full diagonal torus has lifts in the actual prescribed Cartan,
using the same opposite-root marking produced from the original source. -/
theorem strict_source_small_actor_full_diagonal
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length = 12)
    (hT : ∀ z ∈ p.support,
      z ∈ strictSourceApartment h hc hne hb hβu hns hlinear)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,k))
    (z : SL(2,k))
    (hR : ((pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf
      (halfPathActor (X := (A).Universal) p 6)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e))=
          Matrix.SpecialLinearGroup.upperUnipotent k)
    (hV : ∀ y : SL(2,k), y∈((pathRoot (X := (A).Universal) (p.take 6)).subgroupOf
      (halfPathActor (X := (A).Universal) p 6)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e)) ↔
      ∃ a : k, NaturalCubic.lower a=y) :
    ∀ a : k, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
      ((cartan (chosenCartans h)).subgroupOf (halfPathActor (X := (A).Universal) p 6)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl e)) := by
  let r := strictSourceReflections h hc hne hb hβu hns hlinear
  exact six_actor_full_diagonal h (chosenCartans h) r.t r.normalizes p hl hT
    (strict_source_small_actor_cartan_le h hc hne hb hβu hns hlinear p hp hl hT).2 e z hR hV

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
