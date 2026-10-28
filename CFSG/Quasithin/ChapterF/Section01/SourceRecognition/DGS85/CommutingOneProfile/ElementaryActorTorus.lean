module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorCartan
public import Theory.SpecificGroups.SL2.OppositeRootCartan

/-!
# The full Cartan in the prescribed elementary root coordinates

Intersect the apartment Cartan with the intrinsic midpoint local group.
The previously proved containment places this intersection inside the
two-root actor. The original covering is injective there, and the edge
complement theorem gives its order |F|-1. Oddness makes its image under
the literal midpoint quotient injective. Since it normalizes both marked
roots, that image is the entire diagonal torus in their same coordinates.

This supplies the diagonal-lift input for ElementaryActorExchange. It
requires no nontriviality of the Cartan's full local-kernel intersection;
that separate premise is still needed for the faithful actor used there.
Source: DGS, Groups and Graphs (1985), (14.3)(b), p.212, and
(14.11)--(14.12), p.217; the elementary source profile is (11.7), pp.174--175.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem


variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include c t htfix htmove htsq htnorm

variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=8)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t))
include hp hl hT

/-- The full diagonal torus is present in the same opposite-root coordinates
on the original actor. No Cartan-kernel nontriviality is assumed. -/
theorem original_elementary_actor_full_diagonal
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4)))) ≃* SL(2,k))
    (z : SL(2,k))
    (hR : ((pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf
      (halfPathActor (X := (A).Universal) p 4)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 4 hl e))=
          Matrix.SpecialLinearGroup.upperUnipotent k)
    (hV : ∀ y : SL(2,k), y∈((pathRoot (X := (A).Universal) (p.take 4)).subgroupOf
      (halfPathActor (X := (A).Universal) p 4)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 4 hl e)) ↔
      ∃ a : k, NaturalCubic.lower a=y) :
    ∀ a : k, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
      ((cartan c).subgroupOf (halfPathActor (X := (A).Universal) p 4)).map
        ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 4 hl e)) := by
  let D := halfPathActor (X := (A).Universal) p 4
  let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
  let V := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let w := cov.vertex (p.getVert 5)
  let J := graphLocalGroup F v
  let C₀ := (cartan c).map φ
  let C := (cartan c ⊓ J.comap φ).subgroupOf D
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 4 hl)
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 4 hl e)
  have hpker : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective]
    exact halfPathLinearMap_kernel_isTwo h p 4 hl e
  have hCD : cartan c ⊓ J.comap φ ≤ D :=
    (original_elementary_local_cartan_le_actor h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT).2
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
    · change φ x • cov.vertex (p.getVert 4)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 4))]
    · change φ x • cov.vertex (p.getVert 5)=_
      rw [←cov.vertex_smul,reflectionApartment_fixed c t htnorm x hx _
        (hT _ (p.getVert_mem_support 5))]
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
  have hCn (q : (sourceGraph A).Walk a (p.getVert 4))
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
    have hfix : x.val∈pathFixer (X := (A).Universal) (p.drop 4) := by
      intro j _
      rw [drop_getVert]
      exact reflectionApartment_fixed c t htnorm x.val hx.1 _ (hT _ (p.getVert_mem_support _))
    have hn := pathFixer_le_normalizer_pathRoot (p.drop 4) hfix
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp hn y.val)
  have hCV : C ≤ normalizer (V : Set D) := by
    apply hCn (p.take 4)
    intro x hx
    rw [support_take] at hx
    exact hT x (List.mem_of_mem_take hx)
  have hφi : Function.Injective (φ.comp D.subtype) := by
    intro x y he
    apply halfPathLocalMap_injective h p 4 hl
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

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
