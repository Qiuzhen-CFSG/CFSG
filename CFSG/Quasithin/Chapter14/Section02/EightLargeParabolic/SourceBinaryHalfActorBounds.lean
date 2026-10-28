module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActor
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryCoreExponent

/-!
# Exhaustion of the actual binary half-path actors

The exact canonical kernel embeds into the full original binary endpoint
core, whose fourth powers vanish. Its proved cyclic generator therefore has
order at most four. Thus the same selected source geometry has only the
literal dihedral actors of orders six, twelve and twenty-four at binary
midpoints. The full permutation kernel is not substituted for this own-core
kernel. All root generators, quotient maps, Cartan data and eight-actor
perfectness are retained, without a bound or reflection-correction premise.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorBounds
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceHalfPathQuotients SourceHalfPathCoordinates SourceHalfPathTorus SourceHalfPathActors SourceBinaryHalfActor SourceBinaryCoreExponent
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

/-- The unchanged mixed source data with binary actor orders six, twelve
or twenty-four and the entire canonical two-core of order at most four. -/
@[expose] def HasBoundedBinaryHalfPathActors (h : HypothesisF11 L S)
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
                 Nonempty (D ≃* DihedralGroup (3*2^r)) ∧ r≤2 ∧
                 Nat.card (pCore 2 D)≤4 ∧
                 (Nonempty (D ≃* DihedralGroup 3) ∨
                   Nonempty (D ≃* DihedralGroup 6) ∨ Nonempty (D ≃* DihedralGroup 12)))) ∧
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

private theorem halfactor_core_fourth (h : HypothesisF11 L S)
    (hfour : ∀ v : Vertex F, v.type=false → ∀ x∈Q F v, x^4=1)
    {a b} (p : (sourceGraph A).Walk a b) (hl : p.length=12)
    {k : Type*} [Field k]
    (e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,k))
    (hker : (halfPathLinearMap h p 6 hl e).ker=pCore 2 (halfPathActor (X := (A).Universal) p 6))
    (ht : (p.getVert 6).type=false)
    (x : halfPathActor (X := (A).Universal) p 6)
    (hx : x∈pCore 2 (halfPathActor (X := (A).Universal) p 6)) : x^4=1 := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  let J := graphLocalGroup F v
  have hxlocal : halfPathLocalMap h p 6 hl x∈pCore 2 J := by
    rw [←hker,halfPathLinearMap_kernel] at hx
    exact hx
  have hxQ : (halfPathLocalMap h p 6 hl x : G₀ L S)∈Q F v := by
    rw [←show J.pCoreIn 2=Q F v from sylowGenerated_core _]
    exact mem_map_of_mem J.subtype hxlocal
  apply halfPathLocalMap_injective h p 6 hl
  rw [map_pow,map_one]
  apply Subtype.ext
  exact hfour v ht _ hxQ

private theorem bounded_actors_of_full_core (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S))
    (hfour : ∀ v : Vertex F, v.type=false → ∀ x∈Q F v, x^4=1)
    (hq : HasBinaryDihedralHalfPathActors h c) : HasBoundedBinaryHalfPathActors h c := by
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
  obtain ⟨r,x,y,hx,hy,hfx,hfy,hx2,hy2,hRx,hVy,horder,hcore,hcard,hDcard,he⟩ := hmodel ht
  have hpow := halfactor_core_fourth h hfour p hl (e _) hker ht ((x*y)^3)
    (hcore.symm ▸ mem_zpowers _)
  have hd : 2^r∣4 := by
    have hd := orderOf_dvd_of_pow_eq_one hpow
    rw [←Nat.card_zpowers,←hcore,hcard] at hd
    exact hd
  have hle : 2^r≤4 := Nat.le_of_dvd (by decide) hd
  have hr : r≤2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hle
  refine ⟨r,x,y,hx,hy,hfx,hfy,hx2,hy2,hRx,hVy,horder,hcore,hcard,hDcard,he,hr,?_,?_⟩
  · rwa [hcard]
  · interval_cases r
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)

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
/-- The original source bounds the full binary halfactor core by four and
exhausts its actual dihedral actors of orders six, twelve and twenty-four.
All previous source data refer to the same chosen geometry and quotient maps. -/
theorem source_binary_halfactor_bounds
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    HasBoundedBinaryHalfPathActors
      (show HypothesisF11 Lₛ (T : Subgroup G) from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  exact bounded_actors_of_full_core _ c
    (source_binary_core_fourth hG T hempty hM hu hmany hcard e H hH eR).2
    (source_binary_halfactor hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceBinaryHalfActorBounds
