module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorElementary
public import Theory.GroupTheory.WeakBNPair.RegularTree.ReflectionMidpointPath
public import Theory.GroupTheory.InvolutionPairDihedral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathReflectionChange

/-!
# The actual binary root/reflection dihedral alternatives

The same chosen reflections determine a twelve-path centered at the original
binary endpoint. The binary halfactor's two roots are exchanged by its chosen
reflection. Its rotation of order three or six is the square of the original
root/reflection product. Thus the full root/reflection group has literal
dihedral order six, twelve or twenty-four. All previous source markings are
kept for the same geometry; no root, order or reflection-class premise is added.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryReflectionOrders
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceBinaryHalfActorElementary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

/-- The unchanged mixed source data with binary actor orders six, twelve
and the entire canonical two-core elementary of order at most two. -/
@[expose] def HasBinaryReflectionOrders (h : HypothesisF11 L S)
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

private theorem two_generator_unique {X : Type*} [Group X] (y z : X)
    (hy : orderOf y=2) (hz : z∈zpowers y) (hne : z≠1) : z=y := by
  classical
  have hf : IsOfFinOrder y := orderOf_pos_iff.mp (by omega)
  rw [hf.mem_zpowers_iff_mem_range_orderOf,hy] at hz
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  have hn2 : n<2 := Finset.mem_range.mp hn
  interval_cases n
  · exact (hne (pow_zero y)).elim
  · simp

private theorem bounded_square_rotation {X : Type*} [Group X] (z : X)
    (ho : orderOf (z^2)=3 ∨ orderOf (z^2)=6) :
    ∃ k : ℕ, k≤2 ∧ orderOf z=3*2^k := by
  have hd : orderOf (z^2)∣6 := ho.elim (fun h => by norm_num [h]) (fun h => by norm_num [h])
  have hp : z^12=1 := by
    have hh := orderOf_dvd_iff_pow_eq_one.mp hd
    simpa only [←pow_mul] using hh
  have hz : orderOf z∣12 := orderOf_dvd_of_pow_eq_one hp
  have hs : 3∣orderOf (z^2) := ho.elim (fun h => by norm_num [h]) (fun h => by norm_num [h])
  have h3 : 3∣orderOf z := hs.trans (orderOf_pow_dvd 2)
  have hle : orderOf z≤12 := Nat.le_of_dvd (by decide) hz
  have he : orderOf z=3 ∨ orderOf z=6 ∨ orderOf z=12 := by
    interval_cases h : orderOf z <;> norm_num at *
  rcases he with he | he | he
  · exact ⟨0,by decide,he⟩
  · exact ⟨1,by decide,he⟩
  · exact ⟨2,by decide,he⟩

private theorem reflection_orders_of_halfactors (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S))
    (hq : HasElementaryBinaryHalfPathActors h c) : HasBinaryReflectionOrders h c := by
  obtain ⟨d,hclass,K,fK,finK,chK,hK,e,hpaths⟩ := hq
  let _ := fK
  let _ := finK
  let _ := chK
  refine ⟨d,hclass,?_,K,fK,finK,chK,hK,e,hpaths⟩
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hab : (sourceGraph A).Adj (base UP false) (base UP true) :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨a,b,p,hp,hl,hmid,hnext,hrev,hline,hleft,hright⟩ :=
    reflection_centered_path htree ⟨source_action A⟩ hab
      (d.fixes false) (d.fixes true) (d.moves false) (d.moves true)
      (d.squares false) (d.squares true) 6 (by decide)
  have hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    rw [reflectionApartment_eq_oriented_line c d.reflection d.fixes d.squares d.normalizes false]
    exact hline
  have htype : (p.getVert 6).type=false := by rw [hmid]; rfl
  obtain ⟨_,_,_,_,hcoords,_⟩ := hpaths p hp hl hT
  obtain ⟨_,_,z,_,_,_,hmodels⟩ := hcoords
  obtain ⟨r,x,y,hx,hy,_,_,hx2,hy2,hRx,hVy,horder,_,_,_,_,_,_,hr,_,_⟩ := hmodels htype
  let D := halfPathActor (X := (A).Universal) p 6
  let R := pathRoot (X := (A).Universal) (p.drop 6)
  let V := pathRoot (X := (A).Universal) (p.take 6)
  let t := d.reflection false
  have hR : R=zpowers (x : (A).Universal) := by
    have hh := congrArg (Subgroup.map D.subtype) hRx
    rw [map_subgroupOf_eq_of_le (show R≤D from le_sup_left),MonoidHom.map_zpowers] at hh
    exact hh
  have hV : V=zpowers (y : (A).Universal) := by
    have hh := congrArg (Subgroup.map D.subtype) hVy
    rw [map_subgroupOf_eq_of_le (show V≤D from le_sup_right),MonoidHom.map_zpowers] at hh
    exact hh
  have hx2' : (x : (A).Universal)*(x : (A).Universal)=1 := congrArg Subtype.val hx2
  have hy2' : (y : (A).Universal)*(y : (A).Universal)=1 := congrArg Subtype.val hy2
  have hxy : orderOf ((x : (A).Universal)*(y : (A).Universal))=3 ∨
      orderOf ((x : (A).Universal)*(y : (A).Universal))=6 := by
    have hh : orderOf ((x : (A).Universal)*(y : (A).Universal))=3*2^r :=
      (Subgroup.orderOf_mk (x*y).val (x*y).property).symm.trans horder
    interval_cases r
    · exact Or.inl hh
    · exact Or.inr hh
  have hxne : (x : (A).Universal)≠1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one (show (y : (A).Universal)^2=1 by simpa only [pow_two] using hy2')
    rcases hxy with hh | hh <;> rw [he,one_mul] at hh <;> rw [hh] at hd <;> norm_num at hd
  have hyne : (y : (A).Universal)≠1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one (show (x : (A).Universal)^2=1 by simpa only [pow_two] using hx2')
    rcases hxy with hh | hh <;> rw [he,mul_one] at hh <;> rw [hh] at hd <;> norm_num at hd
  have hyo : orderOf (y : (A).Universal)=2 :=
    orderOf_eq_prime (by simpa only [pow_two] using hy2') hyne
  have hconj : t*(x : (A).Universal)*t⁻¹=(y : (A).Universal) := by
    apply two_generator_unique _ _ hyo
    · have hr' : R.map (MulAut.conj t).toMonoidHom=V := hright
      rw [←hV,←hr']
      exact mem_map_of_mem (MulAut.conj t).toMonoidHom hx
    · intro he
      apply hxne
      exact (MulAut.conj t).injective (he.trans (map_one (MulAut.conj t)).symm)
  have hsquare : ((x : (A).Universal)*t)^2=(x : (A).Universal)*(y : (A).Universal) := by
    have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (d.squares false)
    rw [←hconj]
    simp only [pow_two,hti,mul_assoc]
  obtain ⟨k,hk,hkorder⟩ := bounded_square_rotation ((x : (A).Universal)*t) (by rw [hsquare]; exact hxy)
  have hequiv := involution_pair_dihedral (x : (A).Universal) t
    (by simpa only [pow_two] using hx2')
    (by simpa only [pow_two] using d.squares false)
    (show 2<3*2^k by
      have : 0<2^k := by positivity
      omega) hkorder
  refine ⟨a,b,p,hp,hl,hmid,hnext,hT,hrev,hright.symm,k,x,hx,hR,hx2',hkorder,hk,?_⟩
  change Nonempty ((R ⊔ zpowers t : Subgroup (A).Universal) ≃* DihedralGroup (3*2^k))
  rw [hR]
  exact hequiv

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
/-- The original mixed source supplies the literal binary root/reflection
dihedral alternatives with the same Cartan, geometry and quotient markings. -/
theorem source_binary_reflection_orders
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    HasBinaryReflectionOrders
      (show HypothesisF11 Lₛ (T : Subgroup G) from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  exact reflection_orders_of_halfactors _ c
    (source_binary_halfactor_elementary hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryReflectionOrders
