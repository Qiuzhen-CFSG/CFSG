module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceOppositeRootJoin
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryReflectionOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement

/-!
# Faithfulness of the selected original eight-field half-path actor

The local covering embeds the actual half-path actor in the original
endpoint. Its two actual roots are simultaneously placed with the original
whole Cartan in a full-core complement, making the literal local quotient
map faithful. The selected reflection and its centered path are retained.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightHalfActor
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceBinaryReflectionOrders
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
private theorem faithful_root_card {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (R : Subgroup X) (hk : R ⊓ f.ker=⊥) :
    Nat.card R=Nat.card (R.map f) := by
  apply Nat.card_congr
  exact (MulEquiv.ofBijective (f.subgroupMap R) ⟨by
    intro x y he
    apply Subtype.ext
    have he' : f x=f y := congrArg Subtype.val he
    have hx : (x:X)/(y:X)∈R ⊓ f.ker :=
      ⟨R.div_mem x.property y.property,by change f (_/_) = 1; rw [map_div,he',div_self']⟩
    rw [hk,mem_bot] at hx
    exact div_eq_one.mp hx,
    f.subgroupMap_surjective R⟩).toEquiv

private theorem opposite_coordinate_data {X k : Type*} [Group X] [Field k]
    (f : X →* SL(2,k)) (R V : Subgroup X)
    (hRk : R ⊓ f.ker=⊥) (hVk : V ⊓ f.ker=⊥)
    (z : SL(2,k))
    (hR : R.map ((MulAut.conj z).toMonoidHom.comp f)=Matrix.SpecialLinearGroup.upperUnipotent k)
    (hV : ∀ y, y∈V.map ((MulAut.conj z).toMonoidHom.comp f) ↔
      ∃ a, Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y) :
    Nat.card R=Nat.card k ∧ Nat.card V=Nat.card k ∧ R.map f≠V.map f := by
  let g := (MulAut.conj z).toMonoidHom.comp f
  have hg : g.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective
  have hVc : Nat.card (V.map g)=Nat.card k := by
    let j : k → V.map g := fun a => ⟨NaturalCubic.lower a,(hV _).mpr ⟨a,rfl⟩⟩
    have hj : Function.Bijective j := by
      constructor
      · intro x y he
        have he' := congrArg (fun z : V.map g => z.val.val 1 0) he
        simpa [j,NaturalCubic.lower,Matrix.SpecialLinearGroup.transvection_coe] using he'
      · intro x
        obtain ⟨a,ha⟩ := (hV x.val).mp x.property
        exact ⟨a,Subtype.ext ha⟩
    exact (Nat.card_congr (Equiv.ofBijective j hj)).symm
  refine ⟨(faithful_root_card g R (hg.symm ▸ hRk)).trans
    (by rw [hR,Matrix.SpecialLinearGroup.card_upperUnipotent]),
    (faithful_root_card g V (hg.symm ▸ hVk)).trans hVc,?_⟩
  intro he
  have he' : R.map g=V.map g := by
    change R.map ((MulAut.conj z).toMonoidHom.comp f)=_
    rw [←Subgroup.map_map,he,Subgroup.map_map]
  have hu : NaturalCubic.upper (1:k)∈R.map g := by
    rw [hR]
    exact (Matrix.SpecialLinearGroup.mem_upperUnipotent k _).mpr ⟨1,rfl⟩
  obtain ⟨a,ha⟩ := (hV _).mp (he' ▸ hu)
  have hh := congrArg (fun y : SL(2,k) => y.val 0 1) ha
  simp [NaturalCubic.upper,Matrix.SpecialLinearGroup.transvection_coe] at hh

private theorem reversed_starred {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G} :
    family (starredParabolic ![L 1,L 0] S) true=starredParabolic L S 0 := rfl

private theorem graph_actor_equiv_of_starred {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S H : Subgroup G} (h : HypothesisF11 L S)
    (eK : (family L true ⧸ pCore 2 (family L true)) ≃* PSL(2,GaloisField 2 3))
    (hs : family (starredParabolic L S) true=H) :
    ∃ j : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true) ≃* H,
      ∀ x, (j x:G)=(x:G₀ L S) := by
  refine ⟨(reduced_linearActorEquiv h true eK).trans (MulEquiv.subgroupCongr hs),?_⟩
  intro x
  exact reduced_linearActorEquiv_coe h true eK x

private theorem quotient_bijective_complement {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup Y) [N.Normal] (j : X →* Y)
    (hb : Function.Bijective ((QuotientGroup.mk' N).comp j)) : N.IsComplement' j.range := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    rintro y hy ⟨x,rfl⟩
    have hx : x=1 := hb.1 ((QuotientGroup.eq_one_iff (j x)).mpr hy |>.trans
      (map_one ((QuotientGroup.mk' N).comp j)).symm)
    rw [hx,map_one]
  · apply Set.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨x,hx⟩ := hb.2 (QuotientGroup.mk' N y)
    refine ⟨y/j x,?_,j x,⟨x,rfl⟩,div_mul_cancel _ _⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (y/j x)=1
    rw [map_div,show QuotientGroup.mk' N (j x)=QuotientGroup.mk' N y from hx,div_self']

section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

/-- The unchanged binary reflection package and a path centered at the original
 eight endpoint, reversed by the same eight reflection. Its literal half-actor
 map is faithful and gives the displayed marking on every representative. -/
@[expose] def HasEightHalfActor (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∃ d : SixPathSmallActorGeometry c,
    (∀ i, Nonempty (BinarySixPathReflectionClass h i (d.reflection i))) ∧
    (∃ (a b : SourceVertex A) (p : (sourceGraph A).Walk a b),
      p.IsPath ∧ p.length=12 ∧ p.getVert 6=base UP false ∧ p.getVert 7=base UP true ∧
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection)) ∧
      (∀ k≤12, d.reflection false • p.getVert k=p.getVert (12-k)) ∧
      let R := pathRoot (X := (A).Universal) (p.drop 6)
      (pathRoot (X := (A).Universal) (p.take 6))=R.map (MulAut.conj (d.reflection false)).toMonoidHom ∧
      ∃ (k : ℕ) (x : (A).Universal), x∈R ∧ R=zpowers x ∧ x*x=1 ∧
        orderOf (x*d.reflection false)=3*2^k ∧ k≤2 ∧
        Nonempty ((R ⊔ zpowers (d.reflection false) : Subgroup (A).Universal) ≃*
          DihedralGroup (3*2^k))) ∧
    ∃ (K : Bool → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Finite (K i))
      (_ : ∀ i, CharP (K i) 2),
      (∀ i, Nat.card (K i)=if i then 8 else 2) ∧
      ∃ e : ∀ v : Vertex F,
        (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type),
      (∀ {a b} (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=12),
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
          pResidual 2 (halfPathActor (X := (A).Universal) p 6)=⊤)) ∧
      ∃ (a b : SourceVertex A) (p : (sourceGraph A).Walk a b)
        (_hp : p.IsPath) (hl : p.length=12),
        p.getVert 6=base UP true ∧ p.getVert 7=base UP false ∧
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection)) ∧
        (∀ k≤12, d.reflection true • p.getVert k=p.getVert (12-k)) ∧
        pathRoot (X := (A).Universal) (p.take 6)=
          (pathRoot (X := (A).Universal) (p.drop 6)).map
            (MulAut.conj (d.reflection true)).toMonoidHom ∧
        pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥ ∧
        Function.Injective (halfPathLinearMap h p 6 hl
          (e ((bOne_tree_cover h).vertex (p.getVert 6)))) ∧
        (pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))).IsComplement'
          (halfPathLocalMap h p 6 hl).range ∧
        ∃ E : halfPathActor (X := (A).Universal) p 6 ≃*
            SL(2,K ((bOne_tree_cover h).vertex (p.getVert 6)).type),
          ∀ x, E x=e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 6 hl x))

private theorem assemble_eight_halfactor (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hq : HasBinaryReflectionOrders h c)
    (hcores : ∀ (d : SixPathSmallActorGeometry c) {a b : SourceVertex A}
      (p : (sourceGraph A).Walk a b), p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection)) →
      p.getVert 6=base UP true → pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥) :
    HasEightHalfActor h c := by
  obtain ⟨d,hclass,hbinary,K,fK,finK,chK,hK,em,hpaths⟩ :=
    hq
  let _ := fK
  let _ := finK
  let _ := chK
  refine ⟨d,hclass,hbinary,K,fK,finK,chK,hK,em,hpaths,?_⟩
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hab : (sourceGraph A).Adj (base UP true) (base UP false) :=
    ⟨by change true≠false; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨a,b,p,hp,hl,hmid,hnext,hrev,hline,_,hright⟩ :=
    reflection_centered_path htree ⟨source_action A⟩ hab
      (d.fixes true) (d.fixes false) (d.moves true) (d.moves false)
      (d.squares true) (d.squares false) 6 (by decide)
  have hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    rw [reflectionApartment_eq_oriented_line c d.reflection d.fixes d.squares d.normalizes true]
    exact hline
  have hcore := hcores d p hp hl hT hmid
  obtain ⟨hsurj,hker,_⟩ := hpaths p hp hl hT
  have hinj : Function.Injective (halfPathLinearMap h p 6 hl
      (em ((bOne_tree_cover h).vertex (p.getVert 6)))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (hker.trans hcore)
  have hcomp : (pCore 2 (graphLocalGroup (reducedFamily L S)
      ((bOne_tree_cover h).vertex (p.getVert 6)))).IsComplement'
        (halfPathLocalMap h p 6 hl).range := by
    apply quotient_bijective_complement
    constructor
    · intro x y he
      apply hinj
      exact congrArg (em _) he
    · intro y
      obtain ⟨x,hx⟩ := hsurj (em _ y)
      exact ⟨x,(em _).injective hx⟩
  refine ⟨a,b,p,hp,hl,hmid,hnext,hT,hrev,hright.symm,hcore,hinj,hcomp,
    MulEquiv.ofBijective _ ⟨hinj,hsurj⟩,?_⟩
  intro x
  rfl

end Geometry

variable {G : Type*} [Group G] [Finite G]
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
local notation "Sₛ" => (T : Subgroup G)

private theorem embedded_opposite_kernel
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    {D : Type*} [Group D] (j : D →* H) (hj : Function.Injective j)
    (R S : Subgroup D) (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hr : Nat.card R=8) (hs : Nat.card S=8) (hgen : R⊔S=⊤)
    (hkR : Disjoint R ((QuotientGroup.mk' (pCore 2 H)).comp j).ker)
    (hkS : Disjoint S ((QuotientGroup.mk' (pCore 2 H)).comp j).ker)
    (hCR : c.D 0⊔c.D 1≤normalizer (R.map (H.subtype.comp j):Set G))
    (hCS : c.D 0⊔c.D 1≤normalizer (S.map (H.subtype.comp j):Set G))
    (hne : R.map ((QuotientGroup.mk' (pCore 2 H)).comp j)≠
      S.map ((QuotientGroup.mk' (pCore 2 H)).comp j)) :
    ((QuotientGroup.mk' (pCore 2 H)).comp j).ker=⊥ := by
  let f := H.subtype.comp j
  have hf : Function.Injective f := H.subtype_injective.comp hj
  have hle (X : Subgroup D) : X.map f≤H := by
    rintro x ⟨y,hy,rfl⟩
    exact (j y).property
  have hres (X : Subgroup D) : (X.map f).subgroupOf H=X.map j := by
    change (X.map f).comap H.subtype=X.map j
    rw [show X.map f=(X.map j).map H.subtype from (Subgroup.map_map _ _ _).symm]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hkill (x:D) : f x∈H.pCoreIn 2 ↔ ((QuotientGroup.mk' (pCore 2 H)).comp j) x=1 := by
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff (j x)).mpr
      exact (comap_map_eq_self_of_injective H.subtype_injective (pCore 2 H)).le hx
    · intro hx
      exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (j x)).mp hx)
  have hdis (X : Subgroup D) (hk : Disjoint X ((QuotientGroup.mk' (pCore 2 H)).comp j).ker) :
      Disjoint (X.map f) (H.pCoreIn 2) := by
    apply disjoint_def.mpr
    rintro x ⟨y,hy,rfl⟩ hx
    rw [hk.le_bot ⟨hy,(hkill y).mp hx⟩,map_one]
  have hneq : ((R.map f).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))≠
      ((S.map f).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) := by
    rw [hres,hres,Subgroup.map_map,Subgroup.map_map]
    exact hne
  obtain ⟨hcomp,_,_⟩ := SourceOppositeRootJoin.source_opposite_root_join
    hG T hempty hM hu hmany hcard e H hH eR c (R.map f) (S.map f) (hle R) (hle S)
    (hR.map f) (hS.map f) ((card_map_of_injective hf).trans hr)
    ((card_map_of_injective hf).trans hs) (hdis R hkR) (hdis S hkS) hCR hCS hneq
  apply bot_unique
  intro x hx
  have hjcore : j x∈pCore 2 H := (QuotientGroup.eq_one_iff (j x)).mp hx
  have hxjoin : f x∈R.map f⊔S.map f := by
    rw [←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map]
    exact ⟨x,rfl⟩
  have hj1 : j x=1 := hcomp.disjoint.le_bot ⟨hjcore,hxjoin⟩
  exact hj (hj1.trans (map_one j).symm)

set_option maxHeartbeats 800000 in
private theorem base_eight_actor_equiv :
    ∃ j : graphLocalGroup (reducedFamily Lₛ Sₛ) (base (reducedFamily Lₛ Sₛ) true) ≃* H,
      ∀ x, (j x:G)=(x:G₀ Lₛ Sₛ) := by
  let h : HypothesisF11 Lₛ Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let eK : (family Lₛ true ⧸ pCore 2 (family Lₛ true)) ≃* PSL(2,GaloisField 2 3) :=
    residualQuotientEquiv H eR
  have hs : family (starredParabolic Lₛ Sₛ) true=H :=
    reversed_starred.trans (source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).1
  exact graph_actor_equiv_of_starred h eK hs

private theorem original_cartan_image (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    (cartan c).map ((G₀ Lₛ Sₛ).subtype.comp
      (bOne_tree_map (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap))=
        c.D 0⊔c.D 1 := by
  rw [cartan,Subgroup.map_map]
  have hm : (((G₀ Lₛ Sₛ).subtype.comp
      (bOne_tree_map (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap)).comp
        (middleMap Lₛ Sₛ))=(commonBorel Lₛ (reducedSylow Lₛ Sₛ)).subtype := by
    ext x
    exact bOne_tree_map_middle _ x
  rw [hm,map_subgroupOf_eq_of_le c.joint_le]

private theorem centered_eight_core_eq_bot
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex (reducedAmalgam Lₛ Sₛ)}
    (p : (sourceGraph (reducedAmalgam Lₛ Sₛ)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam Lₛ Sₛ) (reflectionGroup c d.reflection))
    (hmid : p.getVert 6=base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) true) :
    pCore 2 (halfPathActor (X := (reducedAmalgam Lₛ Sₛ).Universal) p 6)=⊥ := by
  let h : HypothesisF11 Lₛ Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let A := reducedAmalgam Lₛ Sₛ
  let F := reducedFamily Lₛ Sₛ
  let D := halfPathActor (X := A.Universal) p 6
  let R := (pathRoot (X := A.Universal) (p.drop 6)).subgroupOf D
  let V := (pathRoot (X := A.Universal) (p.take 6)).subgroupOf D
  have hv : (bOne_tree_cover h).vertex (p.getVert 6)=base F true := by
    rw [hmid,(bOne_tree_cover h).vertex_base]
  obtain ⟨jbase,hjbase⟩ := base_eight_actor_equiv hG T hempty hM hu hmany hcard e H hH eR
  let j₀ : graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ≃* H :=
    (MulEquiv.subgroupCongr (congrArg (graphLocalGroup F) hv)).trans
      jbase
  let j : D →* H := j₀.toMonoidHom.comp (halfPathLocalMap h p 6 hl)
  have hj : Function.Injective j := j₀.injective.comp (halfPathLocalMap_injective h p 6 hl)
  let ε := (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let e₀ := (QuotientGroup.congr _ _ j₀ (pCore_map_iso 2 j₀)).trans ε
  let f := halfPathLinearMap h p 6 hl e₀
  let q := (QuotientGroup.mk' (pCore 2 H)).comp j
  have hf : f=ε.toMonoidHom.comp q := by
    apply MonoidHom.ext
    intro x
    exact congrArg ε (QuotientGroup.congr_mk' _ _ j₀ (pCore_map_iso 2 j₀) _)
  have hk : f.ker=q.ker := by rw [hf,MonoidHom.ker_comp_of_injective _ _ ε.injective]
  have hval : Nat.card ((sourceGraph A).neighborSet (p.getVert 6))=Nat.card (GaloisField 2 3)+1 := by
    rw [SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR,
      hmid,GaloisField.card 2 3 (by decide)]
    rfl
  obtain ⟨hRk,hVk,z,hR,hV⟩ := source_six_root_coordinates h c d p hp hl hT e₀ hval
  obtain ⟨hr,hs,hne⟩ := opposite_coordinate_data f R V hRk hVk z hR hV
  have h8 : Nat.card (GaloisField 2 3)=8 := by rw [GaloisField.card 2 3 (by decide)]; rfl
  have hgen : R⊔V=⊤ := by
    rw [←subgroupOf_sup (show pathRoot (X := A.Universal) (p.drop 6)≤D from le_sup_left)
      (show pathRoot (X := A.Universal) (p.take 6)≤D from le_sup_right),subgroupOf_self]
  let φ := (G₀ Lₛ Sₛ).subtype.comp (bOne_tree_map h)
  have hjφ : H.subtype.comp j=φ.comp D.subtype := by
    ext x
    exact hjbase _
  have hnorm (X : Subgroup A.Universal) (hXD : X≤D)
      (hCX : cartan c≤normalizer (X : Set A.Universal)) :
      c.D 0⊔c.D 1≤normalizer ((X.subgroupOf D).map (H.subtype.comp j):Set G) := by
    rw [hjφ,←Subgroup.map_map,map_subgroupOf_eq_of_le hXD]
    rw [←original_cartan_image hG T hempty hM hu hmany hcard e H hH eR c]
    exact (map_mono hCX).trans (X.le_normalizer_map φ)
  have hfix (k : A.Universal) (hk : k∈cartan c) (n : ℕ) : k • p.getVert n=p.getVert n :=
    reflectionApartment_fixed c d.reflection d.normalizes k hk _ (hT _ (p.getVert_mem_support n))
  have hCR : c.D 0⊔c.D 1≤normalizer (R.map (H.subtype.comp j):Set G) := by
    apply hnorm _ le_sup_left
    intro k hk
    apply pathFixer_le_normalizer_pathRoot (p.drop 6)
    intro n _
    rw [drop_getVert]
    exact hfix k hk _
  have hCV : c.D 0⊔c.D 1≤normalizer (V.map (H.subtype.comp j):Set G) := by
    apply hnorm _ le_sup_right
    intro k hk
    apply pathFixer_le_normalizer_pathRoot (p.take 6)
    intro n _
    rw [take_getVert]
    exact hfix k hk _
  have hneq : R.map q≠V.map q := by
    intro he
    apply hne
    rw [hf,←Subgroup.map_map,he,Subgroup.map_map]
  have hqbot := embedded_opposite_kernel hG T hempty hM hu hmany hcard e H hH eR c j hj R V
    (pathRoot_isTwo _).comap_subtype (pathRoot_isTwo _).comap_subtype
    (hr.trans h8) (hs.trans h8) hgen
    (disjoint_iff.mpr (hk ▸ hRk)) (disjoint_iff.mpr (hk ▸ hVk)) hCR hCV hneq
  exact (source_six_halfPathLinearMap_kernel h c d p hp hl hT e₀ hval).symm.trans (hk.trans hqbot)

set_option maxHeartbeats 800000 in
/-- The original source identifies the actual eight-side halfactor, retaining
its selected reflection, both reflection classes, the whole Cartan, binary
alternatives and every earlier canonical half-path quotient marking. -/
theorem source_eight_halfactor
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    HasEightHalfActor
      (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  exact assemble_eight_halfactor _ c
    (source_binary_reflection_orders hG T hempty hM hu hmany hcard e H hH eR c)
    (centered_eight_core_eq_bot hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightHalfActor
