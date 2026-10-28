module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeEndpoint
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathRootTransport

/-!
# Original quotient images of aligned six-path roots

Seven-path transitivity transports equally oriented six-path roots by the
original Borel two-group. Its image in the original full-core quotient is
abelian. Thus the two roots have the same literal quotient image through
the pointwise original endpoint marking.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTreeRootQuotient
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile

private theorem image_eq_of_transport {X Y : Type*} [Group X] [Group Y]
    (P U R S : Subgroup X) (q : P →* Y)
    [IsMulCommutative ((U.subgroupOf P).map q)]
    (hUP : U≤P) (hRU : R≤U) (hSU : S≤U)
    (u:X) (hu:u∈U) (he:R.map (MulAut.conj u).toMonoidHom=S) :
    (R.subgroupOf P).map q=(S.subgroupOf P).map q := by
  let uP : P := ⟨u,hUP hu⟩
  have heP : (R.subgroupOf P).map (MulAut.conj uP).toMonoidHom=S.subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_map]
    change (R.subgroupOf P).map ((MulAut.conj u).toMonoidHom.comp P.subtype)=_
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le (hRU.trans hUP),he,
      map_subgroupOf_eq_of_le (hSU.trans hUP)]
  exact (SourceRootQuotient.map_conjugate_eq_of_commutative_image q
    (U.subgroupOf P) (R.subgroupOf P) (subgroupOf_mono P hRU) uP hu).symm.trans
      (congrArg (fun V:Subgroup P => V.map q) heP)

private theorem thick_of_neighbor_cards
    {X : Type*} [Group X] (F : Bool → Subgroup X)
    (hval : ∀ v:Vertex F, Nat.card ((graph F).neighborSet v)=if v.type then 9 else 3)
    (v a b:Vertex F) : ∃ z,(graph F).Adj v z ∧ z≠a ∧ z≠b := by
  have hn : 2 < ((graph F).neighborSet v).ncard := by
    change 2 < Nat.card ((graph F).neighborSet v)
    rw [hval v]
    cases v.type <;> decide
  let : Finite ((graph F).neighborSet v) := Nat.finite_of_card_ne_zero (by
    rw [hval v]; cases v.type <;> decide)
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hn
  by_cases hxa : x=a
  · by_cases hyb : y=b
    · exact ⟨z,hz,fun he => hxz (hxa.trans he.symm),fun he => hyz (hyb.trans he.symm)⟩
    · exact ⟨y,hy,fun he => hxy (hxa.trans he.symm),hyb⟩
  · by_cases hxb : x=b
    · by_cases hya : y=a
      · exact ⟨z,hz,fun he => hyz (hya.trans he.symm),fun he => hxz (hxb.trans he.symm)⟩
      · exact ⟨y,hy,hya,fun he => hxy (hxb.trans he.symm)⟩
    · exact ⟨x,hx,hxa,hxb⟩

section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => Universal.cosetFamily A
local notation "P" => stabilizer F (base F true)

/-- The same full endpoint marking identifies the quotient images of all
Cartan-fixed, equally oriented six-path radicals. -/
@[expose] def HasTreeRootQuotients (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (H : Subgroup G) : Prop :=
    ∃ j:P≃*H, (∀ x,(j x:G)=((G₀ L S).subtype.comp (bOne_tree_map h)) x) ∧
      ∀ {a b : SourceVertex A} (p:(sourceGraph A).Walk a (base F true))
        (r:(sourceGraph A).Walk b (base F true)),
        p.IsPath → r.IsPath → p.length=6 → r.length=6 →
        p.penultimate=base F false → r.penultimate=base F false →
        cartan c≤pathFixer (X := (A).Universal) p →
        ((pathRoot (X := (A).Universal) p).subgroupOf P).map
            ((QuotientGroup.mk' (pCore 2 H)).comp j.toMonoidHom)=
          ((pathRoot (X := (A).Universal) r).subgroupOf P).map
            ((QuotientGroup.mk' (pCore 2 H)).comp j.toMonoidHom)

private theorem root_quotients_of_endpoint (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (H : Subgroup G)
    (eH : (H ⧸ pCore 2 H) ≃* Theory.PSL2.BinaryGroup 3)
    (hend : SourceEightTreeEndpoint.HasEightTreeEndpoint h H)
    (htrans : BasedPathTransitive (X := (A).Universal) (sourceGraph A) 7)
    (hval : ∀ v:SourceVertex A,Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3) :
    HasTreeRootQuotients h c H := by
  obtain ⟨j,hj⟩ := hend.1
  let q := (QuotientGroup.mk' (pCore 2 H)).comp j.toMonoidHom
  let U := twoGroup L S
  let ε := eH.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let f := ε.toMonoidHom.comp ((U.subgroupOf P).map q).subtype
  let : IsMulCommutative ((U.subgroupOf P).map q) :=
    SourceRootQuotient.binary_linear_two_image_commutative f
      (ε.injective.comp ((U.subgroupOf P).map q).subtype_injective)
      ((twoGroup_isTwo h).comap_subtype.map q)
  have hUP : U≤P := by
    intro u hu
    have hm := twoGroup_le (L := L) (S := S) hu
    rw [originalMiddle,←Universal.overlap_eq A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))] at hm
    change u∈MulAction.stabilizer (A).Universal (base F true)
    rw [Subgroup.CosetGeometry.stabilizer_base]
    exact hm.2
  refine ⟨j,hj,?_⟩
  intro a b p r hp hr hpl hrl hprev hrprev hCp
  obtain ⟨u,hu,he⟩ := exists_twoGroup_pathRoot_transport h c 6 htrans
    (thick_of_neighbor_cards F hval) p r hp hr hpl hrl hprev hrprev hCp
  exact image_eq_of_transport P U _ _ q hUP
    (aligned_pathRoot_le_twoGroup h p hprev)
    (aligned_pathRoot_le_twoGroup h r hrprev) u hu he
end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
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
set_option maxHeartbeats 800000 in
/-- Equally oriented six-path roots have the same original full-core
quotient image, including the roots after central reflection correction. -/
theorem source_tree_root_quotients
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    HasTreeRootQuotients
      (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c H := by
  exact root_quotients_of_endpoint (L := Lₛ) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap c H
    (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
    (SourceEightTreeEndpoint.source_eight_tree_endpoint hG T hempty hM hu hmany hcard e H hH eR)
    (source_path_profile hG T hempty hM hu hmany hcard e H hH eR).2.1
    (SourceCartanPaths.source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR)
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTreeRootQuotient
