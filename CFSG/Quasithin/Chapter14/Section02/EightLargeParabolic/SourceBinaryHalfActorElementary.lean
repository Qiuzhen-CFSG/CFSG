module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorBounds
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceLocalKernels
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinarySecondCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedTerminal
public import Theory.GroupTheory.WeakBNPair.RegularTree.BallKernelCover

/-!
# Elementary kernels of the actual binary half-path actors

The whole original Cartan centralizes the binary actor. Its nontrivial
factor in the full binary permutation kernel propagates the actor's own
two-core into the neighboring core, using the proved mixed adjacent-kernel
intersection. Actor transitivity puts that same kernel in every neighboring
core, hence in the original elementary radius-two core. The actual cyclic
kernel is therefore of order at most two, leaving dihedral orders six or
twelve. Every previous quotient, root, Cartan and reflection witness is kept.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorElementary
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceBinaryHalfActorBounds
open CommutingOneProfile CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

/-- The unchanged mixed source data with binary actor orders six, twelve
and the entire canonical two-core elementary of order at most two. -/
@[expose] def HasElementaryBinaryHalfPathActors (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∃ d : SixPathSmallActorGeometry c,
    (∀ i, Nonempty (BinarySixPathReflectionClass h i (d.reflection i))) ∧
    ∃ (K : Bool → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Finite (K i))
      (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i)=if i then 8 else 2) ∧
      ∃ e : ∀ v : Vertex F,
        (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
      ∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=12),
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection)) →
        Function.Surjective (halfPathLinearMap h p 6 hl
          (e ((bOne_tree_cover h).vertex (p.getVert 6)))) ∧
        (halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6)))).ker =
          pCore 2 (halfPathActor (X := (A).Universal) p 6) ∧
        (halfPathActor (X := (A).Universal) p 6).map (bOne_tree_map h) ⊔
          Q F ((bOne_tree_cover h).vertex (p.getVert 6)) =
            graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ∧
        (∃ E : (halfPathActor (X := (A).Universal) p 6 ⧸
            pCore 2 (halfPathActor (X := (A).Universal) p 6)) ≃*
              SL(2,K ((bOne_tree_cover h).vertex (p.getVert 6)).type),
          ∀ x : halfPathActor (X := (A).Universal) p 6,
            E (QuotientGroup.mk' _ x) =
              e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 6 hl x))) ∧
        (let D := halfPathActor (X := (A).Universal) p 6
         let R := (pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf D
         let V := (pathRoot (X := (A).Universal) (p.take 6)).subgroupOf D
         let f := halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6)))
         R ⊓ f.ker=⊥ ∧ V ⊓ f.ker=⊥ ∧
           ∃ z : SL(2,K ((bOne_tree_cover h).vertex (p.getVert 6)).type),
             R.map ((MulAut.conj z).toMonoidHom.comp f)=
               Matrix.SpecialLinearGroup.upperUnipotent _ ∧
             (∀ y, y∈V.map ((MulAut.conj z).toMonoidHom.comp f) ↔
               ∃ a, Matrix.SpecialLinearGroup.transvection
                 (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y) ∧
             (∀ a, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
               ((cartan c).subgroupOf D).map ((MulAut.conj z).toMonoidHom.comp f)) ∧
             ((p.getVert 6).type=false →
               ∃ (r : ℕ) (x y : D), x∈R ∧ y∈V ∧
                 ((MulAut.conj z).toMonoidHom.comp f) x=NaturalCubic.upper 1 ∧
                 ((MulAut.conj z).toMonoidHom.comp f) y=NaturalCubic.lower 1 ∧
                 x*x=1 ∧ y*y=1 ∧ R=zpowers x ∧ V=zpowers y ∧
                 orderOf (x*y)=3*2^r ∧ pCore 2 D=zpowers ((x*y)^3) ∧
                 Nat.card (pCore 2 D)=2^r ∧ Nat.card D=6*2^r ∧
                 Nonempty (D ≃* DihedralGroup (3*2^r)) ∧
                 (D.pCoreIn 2).map (bOne_tree_map h) ≤
                   (ballKernel F ((bOne_tree_cover h).vertex (p.getVert 6)) 2).pCoreIn 2 ∧
                 IsElementaryAbelian 2 (pCore 2 D) ∧ r≤1 ∧
                 Nat.card (pCore 2 D)≤2 ∧
                 (Nonempty (D ≃* DihedralGroup 3) ∨ Nonempty (D ≃* DihedralGroup 6)))) ∧
        (cartan c ⊓ (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6))).comap
          (bOne_tree_map h) ≤ halfPathActor (X := (A).Universal) p 6) ∧
        ((p.getVert 6).type=true → cartan c ≤ halfPathActor (X := (A).Universal) p 6) ∧
        cartan c ⊓ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) =
          cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) ∧
        ((p.getVert 6).type=false →
          cartan c ≤ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal)) ∧
        ((p.getVert 6).type=true →
          Group.IsPerfect (halfPathActor (X := (A).Universal) p 6) ∧
          pResidual 2 (halfPathActor (X := (A).Universal) p 6)=⊤)

private theorem binary_kernel_le_second_core (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex A,
      Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (hpar : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7)
    (hkk : ∀ {v w : Vertex F}, (graph F).Adj v w → U F v ⊓ U F w=Q F v ⊓ Q F w)
    (d : SixPathSmallActorGeometry c)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ v : Vertex F, (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type))
    {a b} (p : (sourceGraph A).Walk a b) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection))
    (hker : (halfPathLinearMap h p 6 hl (e _)).ker=pCore 2 (halfPathActor (X := (A).Universal) p 6))
    (hcover : (halfPathActor (X := (A).Universal) p 6).map (bOne_tree_map h) ⊔
      Q F ((bOne_tree_cover h).vertex (p.getVert 6))=graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))
    (hcentral : cartan c ≤ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal))
    (htype : (p.getVert 6).type=false) :
    ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h) ≤
      (ballKernel F ((bOne_tree_cover h).vertex (p.getVert 6)) 2).pCoreIn 2 := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let D := halfPathActor (X := (A).Universal) p 6
  let M := D.map φ
  let V := (D.pCoreIn 2).map φ
  let v := cov.vertex (p.getVert 6)
  let w := cov.vertex (p.getVert 7)
  have hfix (k) (hk : k∈cartan c) (j : ℕ) : k • p.getVert j=p.getVert j :=
    reflectionApartment_fixed c d.reflection d.normalizes k hk _ (hT _ (p.getVert_mem_support j))
  have hvw : (graph F).Adj v w := cov.hom.map_adj (p.adj_getVert_succ (by omega))
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hVQ : V≤Q F v := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    have hxk := hker.symm ▸ hx
    rw [halfPathLinearMap_kernel] at hxk
    exact (CommutingTrivial.graphLocalGroup_core (reduced_triple h) v).le
      ⟨halfPathLocalMap h p 6 hl x,hxk,rfl⟩
  have hCM : C≤centralizer (M : Set (G₀ L S)) := by
    rintro _ ⟨k,hk,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact (show Commute x k from mem_centralizer_iff.mp (hcentral hk) x hx).map φ
  have hVM : V≤M := map_mono (pCoreIn_le 2 D)
  have hCV : C≤normalizer (V : Set (G₀ L S)) :=
    (hCM.trans (centralizer_le hVM)).trans (Subgroup.centralizer_le_normalizer _)
  have hMV : M≤normalizer (V : Set (G₀ L S)) :=
    (map_mono (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))).trans
        ((D.pCoreIn 2).le_normalizer_map φ)
  have hCE : C≤stabilizer F v ⊓ stabilizer F w := by
    rintro _ ⟨k,hk,rfl⟩
    constructor
    · change φ k • cov.vertex (p.getVert 6)=_
      rw [←cov.vertex_smul,hfix k hk 6]
    · change φ k • cov.vertex (p.getVert 7)=_
      rw [←cov.vertex_smul,hfix k hk 7]
  have hCker : C≤U F v := by
    have hu : cartan c≤ballKernel UP (p.getVert 6) 1 :=
      seven_cubic_vertex_kernel UP (cartan c) hC (p.getVert 6) (fun k hk => hfix k hk 6)
        (by simpa only [htype,Bool.false_eq_true,if_false] using hval (p.getVert 6))
    exact (map_mono hu).trans (cov.ballKernel_map_le (p.getVert 6) 1)
  have hCne : C≠⊥ := by
    intro he
    have hc : cartan c=⊥ := by
      apply bot_unique
      intro x hx
      have hxφ : φ x=1 := he.le (mem_map_of_mem φ hx)
      have hx1 := (cov.stabilizerEquiv (p.getVert 6)).injective
        (a₁ := ⟨x,hfix x hx 6⟩) (a₂ := 1) (Subtype.ext (by
          change φ x=φ 1
          rw [map_one]
          exact hxφ))
      exact congrArg Subtype.val hx1
    rw [hc,Subgroup.card_bot] at hC
    omega
  let E := F false ⊓ F true
  let W := (twoGroup L S).map φ
  have hmapE : (originalMiddle A).map φ=E := by
    rw [show originalMiddle A=UP false ⊓ UP true from
      (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))).symm]
    exact cov.map_inf
  have hC0 : C≤E := hmapE ▸ map_mono (cartan_le c)
  have hW0 : W≤E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hWn : E≤normalizer (W : Set (G₀ L S)) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hWcore : W≤E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hW0 hWn
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  let _ : Finite E := Finite.of_injective (inclusion (show E≤F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hd0 : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨r,hr⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hr]; exact ho.coprime_two_right.pow_right r)
  have hg0 : C ⊔ E.pCoreIn 2=E := by
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
    hbase hvw C (hEbase ▸ hC0) hCE ho (hEbase ▸ hd0) (hEbase ▸ hg0)
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S))=7 :=
    (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hpar.2
  have hVW : V≤Q F w := CommutingTrivial.cartan_kernel_centralizer_le_neighbor_core
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw
    (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) v (by omega))
    (e w) C V C hCE hd hg hVQ hCV le_rfl hCker ho hCne
    (hCM.trans (centralizer_le hVM)) (hkk hvw)
  have hMN : M≤normalizer (Q F v : Set (G₀ L S)) :=
    ((show M≤graphLocalGroup F v from hcover ▸ le_sup_left).trans (sylowGenerated_le _)).trans
      (stabilizer_normalizes_Q F v)
  have hall : V≤neighborCoreIntersection F v := by
    apply le_iInf
    intro z
    obtain ⟨g,hgM,hgz⟩ : ∃ g∈M, g • w=z.val := by
      obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive (reduced_triple h)
        (reduced_borel_core_sylow h) (reduced_vertex_sylow h) v ⟨w,hvw⟩ z
      have hprod : g∈(M : Set (G₀ L S))*(Q F v : Set (G₀ L S)) := by
        rw [←coe_mul_of_left_le_normalizer_right M (Q F v) hMN,hcover]
        exact hg
      obtain ⟨m,hm,q,hq,rfl⟩ := hprod
      refine ⟨m,hm,?_⟩
      have hqw : q • w=w := (source_Z_Q_U (reduced_triple h) v).2 hq w
        ((mem_ball_one F v w).mpr (Or.inl hvw))
      simpa only [mul_smul,hqw] using hgz
    intro x hx
    have hconj : g⁻¹*x*g∈V := by
      have hh := (mem_normalizer_iff.mp (hMV (M.inv_mem hgM)) x).mp hx
      simpa only [inv_inv] using hh
    rw [←hgz,Q_translate]
    refine ⟨g⁻¹*x*g,hVW hconj,?_⟩
    change g*(g⁻¹*x*g)*g⁻¹=x
    group
  exact hall.trans_eq (reduced_neighborCoreIntersection_eq_second_core h hvw.symm)

private theorem elementary_actors_of_second_core (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex A,
      Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (hpar : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7)
    (hkk : ∀ {v w : Vertex F}, (graph F).Adj v w → U F v ⊓ U F w=Q F v ⊓ Q F w)
    (hsecond : ∀ v : Vertex F, v.type=false → IsElementaryAbelian 2 ((ballKernel F v 2).pCoreIn 2))
    (hq : HasBoundedBinaryHalfPathActors h c) : HasElementaryBinaryHalfPathActors h c := by
  obtain ⟨d,hclass,K,fK,finK,chK,hK,e,hpaths⟩ := hq
  let _ := fK
  let _ := finK
  let _ := chK
  refine ⟨d,hclass,K,fK,finK,chK,hK,e,?_⟩
  intro a b p hp hl hT
  obtain ⟨hsurj,hker,hsupp,hE,hcoords,hCD,hcontain,hcent,hbinary,hperfect⟩ := hpaths p hp hl hT
  obtain ⟨hRk,hVk,z,hR,hV,hdiag,hmodel⟩ := hcoords
  refine ⟨hsurj,hker,hsupp,hE,⟨hRk,hVk,z,hR,hV,hdiag,?_⟩,
    hCD,hcontain,hcent,hbinary,hperfect⟩
  intro ht
  obtain ⟨r,x,y,hx,hy,hfx,hfy,hx2,hy2,hRx,hVy,horder,hcore,hcard,hDcard,he,_,_,_⟩ := hmodel ht
  have hball := binary_kernel_le_second_core h c hC hval hpar hkk d K e p hl hT hker hsupp
    (hbinary ht) ht
  let D := halfPathActor (X := (A).Universal) p 6
  let N := (ballKernel F ((bOne_tree_cover h).vertex (p.getVert 6)) 2).pCoreIn 2
  let _ : IsElementaryAbelian 2 N := hsecond _ ht
  let j : pCore 2 D →* N :=
    ((bOne_tree_map h).comp (D.subtype.comp (pCore 2 D).subtype)).codRestrict N
      (fun x => hball (mem_map_of_mem _ (mem_map_of_mem D.subtype x.property)))
  have hj : Function.Injective j := by
    intro x y heq
    apply Subtype.ext
    apply halfPathLocalMap_injective h p 6 hl
    apply Subtype.ext
    have hh : bOne_tree_map h x.val.val=bOne_tree_map h y.val.val :=
      congrArg (fun z : N => z.val) heq
    exact hh
  have hel : IsElementaryAbelian 2 (pCore 2 D) := IsElementaryAbelian.of_injective j hj
  let _ := hel
  have hpow : ((x*y)^3)^2=1 := elemPow_eq_one_of_isElementaryAbelian
    ((x*y)^3) (hcore.symm ▸ mem_zpowers _)
  have hd : 2^r∣2 := by
    have hd := orderOf_dvd_of_pow_eq_one hpow
    rw [←Nat.card_zpowers,←hcore,hcard] at hd
    exact hd
  have hle : 2^r≤2 := Nat.le_of_dvd (by decide) hd
  have hr : r≤1 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hle
  refine ⟨r,x,y,hx,hy,hfx,hfy,hx2,hy2,hRx,hVy,horder,hcore,hcard,hDcard,he,hball,hel,hr,?_,?_⟩
  · rwa [hcard]
  · interval_cases r
    · exact Or.inl he
    · exact Or.inr he

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]


set_option maxHeartbeats 800000 in
/-- The actual binary actor kernel embeds in the full elementary second-ball
core. The same source geometry therefore has only dihedral actors of orders
six and twelve at its binary midpoints. -/
theorem source_binary_halfactor_elementary
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    HasElementaryBinaryHalfPathActors
      (show HypothesisF11 Lₛ (T : Subgroup G) from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  exact elementary_actors_of_second_core _ c
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
    (source_path_profile hG T hempty hM hu hmany hcard e H hH eR).1
    (fun {_ _} hw => SourceLocalKernels.source_adjacent_kernel_intersection hG T hempty hM hu hmany hcard e H hH eR hw)
    (SourceBinarySecondCore.source_binary_second_core hG T hempty hM hu hmany hcard e H hH eR)
    (source_binary_halfactor_bounds hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorElementary
