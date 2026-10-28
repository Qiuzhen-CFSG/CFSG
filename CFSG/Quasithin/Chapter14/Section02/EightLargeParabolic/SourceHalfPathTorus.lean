module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathCoordinates
public import Theory.GroupTheory.CoprimeSupplementNormalizer
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorTorus

/-!
# Full Cartan lifts on the original mixed-field half-path actors

The original half-path actor supplements the midpoint two-core. The odd
Cartan normalizes its two generating radicals, so its intersection with the
intrinsic local group lies in the actual actor. The same opposite-root
coordinates then contain every diagonal element as an original Cartan image.
At eight-element midpoints this forces the entire order-seven Cartan into
the actor. At binary midpoints it centralizes the actor as already proved.
No nonbinary hypothesis is imposed on the binary endpoint.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathTorus
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceHalfPathQuotients SourceHalfPathCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

/-- The same actual geometry and canonical quotient, with full diagonal
lifts in the prescribed Cartan and whole-Cartan containment at eight midpoints. -/
@[expose] def HasTorusMarkedHalfPathQuotients (h : HypothesisF11 L S)
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
             ∀ a, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
               ((cartan c).subgroupOf D).map ((MulAut.conj z).toMonoidHom.comp f)) ∧
        (cartan c ⊓ (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6))).comap
          (bOne_tree_map h) ≤ halfPathActor (X := (A).Universal) p 6) ∧
        ((p.getVert 6).type=true → cartan c ≤ halfPathActor (X := (A).Universal) p 6) ∧
        cartan c ⊓ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal) =
          cartan c ⊓ (U F ((bOne_tree_cover h).vertex (p.getVert 6))).comap (bOne_tree_map h) ∧
        ((p.getVert 6).type=false →
          cartan c ≤ centralizer (halfPathActor (X := (A).Universal) p 6 : Set (A).Universal))

private theorem local_cartan_le_halfactor (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection))
    (hcover : (halfPathActor (X := (A).Universal) p 6).map (bOne_tree_map h) ⊔
      Q F ((bOne_tree_cover h).vertex (p.getVert 6)) =
        graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6))) :
    let D := halfPathActor (X := (A).Universal) p 6
    let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6))
    cartan c ⊓ J.comap (bOne_tree_map h) ≤ D := by
  intro D J
  have hfix (k) (hk : k ∈ cartan c) (j : ℕ) : k • p.getVert j = p.getVert j :=
    reflectionApartment_fixed c d.reflection d.normalizes k hk _ (hT _ (p.getVert_mem_support j))
  have hn : cartan c ≤ normalizer (D : Set (reducedAmalgam L S).Universal) := by
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := (reducedAmalgam L S).Universal) (p.drop 6) ⊔
      pathRoot (X := (reducedAmalgam L S).Universal) (p.take 6)).map _ = _
    rw [Subgroup.map_sup]
    have hr := pathRoot_map_conj (p.drop 6) (p.drop 6) k rfl
      (fun j _ => by rw [drop_getVert]; exact hfix k hk _)
    have ht := pathRoot_map_conj (p.take 6) (p.take 6) k rfl
      (fun j _ => by rw [take_getVert]; exact hfix k hk _)
    exact congrArg₂ (fun R U : Subgroup (reducedAmalgam L S).Universal => R ⊔ U) hr ht
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  let : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hnm : (cartan c).map (bOne_tree_map h) ≤
      normalizer (D.map (bOne_tree_map h) : Set (G₀ L S)) :=
    (map_mono hn).trans (D.le_normalizer_map (bOne_tree_map h))
  have hcov : D.map (bOne_tree_map h) ⊔ J.pCoreIn 2 = J := by
    have hJ : J.pCoreIn 2 = Q (reducedFamily L S)
        ((bOne_tree_cover h).vertex (p.getVert 6)) := sylowGenerated_core _
    rw [hJ]
    exact hcover
  have hle := coprime_normalizer_inf_le_pCore_supplement
    (halfPathActor_map_le_local h p 6 hl) hcov hnm
    ((cartan_odd c).of_dvd_right ((cartan c).card_map_dvd (bOne_tree_map h)))
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hle ⟨mem_map_of_mem (bOne_tree_map h) hx.1, hx.2⟩
  have hxv : x • p.getVert 6 = p.getVert 6 := hfix x hx.1 6
  have hyv : y • p.getVert 6 = p.getVert 6 := halfPathActor_le_midpoint_stabilizer hl hy
  have he := (bOne_tree_cover h).stabilizerEquiv (p.getVert 6) |>.injective
    (a₁ := ⟨y, hyv⟩) (a₂ := ⟨x, hxv⟩) (Subtype.ext hxy)
  have hyx : y = x := congrArg Subtype.val he
  exact hyx ▸ hy


private theorem full_cartan_le_of_diagonal
    {X k : Type*} [Group X] [Field k] [Finite k]
    (C D : Subgroup X) (hC : Nat.card C=7) (hk : Nat.card k=8)
    (f : D →* SL(2,k))
    (hdiag : ∀ a : k, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈(C.subgroupOf D).map f) :
    C ≤ D := by
  have primeC : Fact (Nat.card C).Prime := ⟨by rw [hC]; decide⟩
  let _ := primeC
  rcases ((C ⊓ D).subgroupOf C).eq_bot_or_eq_top_of_prime_card with hb | ht
  · let _ : Nontrivial kˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [Nat.card_units,hk]; decide)
    obtain ⟨s,hs⟩ := exists_ne (1:kˣ)
    obtain ⟨x,hx,hfx⟩ := hdiag (s:k) s.ne_zero
    have hm : (⟨x.val,hx⟩ : C)∈(C ⊓ D).subgroupOf C := ⟨hx,x.property⟩
    rw [hb,mem_bot] at hm
    have hx1 : x=1 := Subtype.ext (congrArg (fun z : C => (z : X)) hm)
    rw [hx1,map_one] at hfx
    have heq := congrArg (fun y : SL(2,k) => y.val 0 0) hfx
    apply False.elim
    apply hs
    apply Units.ext
    simpa [Matrix.SpecialLinearGroup.diag2_coe'] using heq.symm
  · intro x hx
    have hm : (⟨x,hx⟩ : C)∈(C ⊓ D).subgroupOf C := ht.symm ▸ mem_top _
    exact hm.2

private theorem torus_of_root_coordinates (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hq : HasCoordinatizedHalfPathQuotients h c) : HasTorusMarkedHalfPathQuotients h c := by
  obtain ⟨d,hclass,K,hfield,hfinite,hchar,hK,e,hpaths⟩ := hq
  let _ := hfield
  let _ := hfinite
  let _ := hchar
  refine ⟨d,hclass,K,hfield,hfinite,hchar,hK,e,?_⟩
  intro a b p hp hl hT
  obtain ⟨hsurj,hker,hsupp,hE,hcoords,hcent,hbinary⟩ := hpaths p hp hl hT
  obtain ⟨hRk,hVk,z,hR,hV⟩ := hcoords
  have hCD := local_cartan_le_halfactor h c d p hl hT hsupp
  have hdiag := Assembly.BTwoSource.six_actor_full_diagonal h c d.reflection d.normalizes
    p hl hT hCD (e _) z hR hV
  refine ⟨hsurj,hker,hsupp,hE,⟨hRk,hVk,z,hR,hV,hdiag⟩,hCD,?_,hcent,hbinary⟩
  intro ht
  apply full_cartan_le_of_diagonal (cartan c) _ hC
    (show Nat.card (K ((bOne_tree_cover h).vertex (p.getVert 6)).type)=8 from ?_)
    ((MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 6 hl (e _))) hdiag
  rw [hK]
  change (if (p.getVert 6).type then 8 else 2)=8
  rw [ht]
  rfl

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
/-- The original source constructs full diagonal lifts in its own Cartan,
and the whole order-seven Cartan lies in every eight-midpoint half-path actor.
The fields, root coordinates, quotient kernels and reflection classes are shared. -/
theorem source_half_path_torus
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    HasTorusMarkedHalfPathQuotients
      (show HypothesisF11 Lₛ (T : Subgroup G) from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  exact torus_of_root_coordinates _ c
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
    (source_half_path_coordinates hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceHalfPathTorus
