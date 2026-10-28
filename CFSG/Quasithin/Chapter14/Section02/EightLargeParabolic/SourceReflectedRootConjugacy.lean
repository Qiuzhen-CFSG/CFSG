module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootLiftConjugacy
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTreeRootQuotient
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectionRootProfile
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeNormalizer

/-!
# Original seven-fixed conjugators for the actual reflection roots

The actual quotient image equality and exact root profile supply every
hypothesis of the original root-lift conjugacy theorem. The resulting
conjugator is lifted through the same full endpoint equivalence, retaining
the whole original Cartan and full endpoint core on the universal tree.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Subgroup.CosetGeometry Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectedRootConjugacy
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan

private theorem lift_conjugacy {X Y : Type*} [Group X] [Group Y]
    (P C R S:Subgroup X) (j:P≃*Y) (hCP:C≤P) (hRP:R≤P) (hSP:S≤P)
    (v:Y) (hv:v∈pCore 2 Y ⊓ centralizer ((C.subgroupOf P).map j.toMonoidHom:Set Y))
    (he:(S.subgroupOf P).map j.toMonoidHom=
      ((R.subgroupOf P).map j.toMonoidHom).map (MulAut.conj v).toMonoidHom) :
    ∃ u∈P.pCoreIn 2 ⊓ centralizer (C:Set X),S=R.map (MulAut.conj u).toMonoidHom := by
  let u := j.symm v
  have hu : u∈pCore 2 P := by
    apply (mem_map_equiv (f := j)).mp
    rw [pCore_map_iso]
    exact hv.1
  have huc : (u:X)∈centralizer (C:Set X) := by
    intro c hc
    have hec := hv.2 (j ⟨c,hCP hc⟩) (mem_map_of_mem j.toMonoidHom hc)
    have hc' : (⟨c,hCP hc⟩:P)*u=u*⟨c,hCP hc⟩ := by
      apply j.injective
      simpa only [map_mul,u,j.apply_symm_apply] using hec
    exact congrArg Subtype.val hc'
  have heP : S.subgroupOf P=(R.subgroupOf P).map (MulAut.conj u).toMonoidHom := by
    apply map_injective (f := j.toMonoidHom) j.injective
    rw [he,Subgroup.map_map,Subgroup.map_map]
    congr 1
    ext x
    change v*j x*v⁻¹=j (u*x*u⁻¹)
    rw [map_mul,map_mul,map_inv]
    simp only [u,j.apply_symm_apply]
  refine ⟨u,⟨mem_map_of_mem (P).subtype hu,huc⟩,?_⟩
  have hh := congrArg (Subgroup.map (P).subtype) heP
  rw [map_subgroupOf_eq_of_le hSP,Subgroup.map_map] at hh
  change S=(R.subgroupOf P).map ((MulAut.conj (u:X)).toMonoidHom.comp (P).subtype) at hh
  rwa [←Subgroup.map_map,map_subgroupOf_eq_of_le hRP] at hh

section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => Universal.cosetFamily A
local notation "P" => RankTwo.stabilizer F (base F true)

/-- Reflection roots in the original eight endpoint differ by a conjugator
in its full core centralizing the same whole Cartan. -/
@[expose] def HasReflectedRootConjugacy (c:CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∀ d d':SixPathSmallActorGeometry c,
    let p := reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true
    let r := reflectionPath c d'.reflection d'.fixes d'.moves d'.normalizes 6 (by decide) true
    ∀ K:Subgroup (A).Universal,K≤P →
      (pCore 2 P).IsComplement' (K.subgroupOf P) → cartan c≤K →
      pathRoot (X := (A).Universal) p.walk≤K →
      ∃ u∈(P).pCoreIn 2 ⊓ centralizer (cartan c:Set (A).Universal),
        pathRoot (X := (A).Universal) r.walk=
          (pathRoot (X := (A).Universal) p.walk).map (MulAut.conj u).toMonoidHom

private theorem assemble (h:HypothesisF11 L S) (c:CompatibleCartans L (reducedSylow L S))
    (H:Subgroup G) (hC7:Nat.card (cartan c)=7)
    (hprofile:SourceReflectionRootProfile.HasEightReflectionRoots c)
    (himages:SourceTreeRootQuotient.HasTreeRootQuotients h c H)
    (hconj:∀ (K:Subgroup H),(pCore 2 H).IsComplement' K →
      ∀ C R V:Subgroup H,C≤K → Nat.card C=7 → R≤K →
      IsPGroup 2 V → Nat.card V=8 → Disjoint V (pCore 2 H) →
      C≤normalizer (V:Set H) →
      V.map (QuotientGroup.mk' (pCore 2 H))=R.map (QuotientGroup.mk' (pCore 2 H)) →
      ∃ v∈pCore 2 H⊓centralizer (C:Set H),V=R.map (MulAut.conj v).toMonoidHom) :
    HasReflectedRootConjugacy c := by
  obtain ⟨j,_,himages⟩ := himages
  intro d d'
  dsimp only
  intro K hKP hK hCK hRK
  let p := reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true
  let r := reflectionPath c d'.reflection d'.fixes d'.moves d'.normalizes 6 (by decide) true
  let R := pathRoot (X := (A).Universal) p.walk
  let V := pathRoot (X := (A).Universal) r.walk
  have hCP : cartan c≤P := hCK.trans hKP
  have hRP : R≤P := hRK.trans hKP
  obtain ⟨hVP,hV8,hVdis,hCV⟩ := hprofile d'
  change V≤P at hVP
  change Nat.card V=8 at hV8
  change Disjoint V ((P).pCoreIn 2) at hVdis
  change cartan c≤normalizer (V:Set (A).Universal) at hCV
  let C₀ := (cartan c).subgroupOf P
  let R₀ := R.subgroupOf P
  let V₀ := V.subgroupOf P
  let K₀ := K.subgroupOf P
  have hK' : (pCore 2 H).IsComplement' (K₀.map j.toMonoidHom) := by
    have hh := SourceEightTreeNormalizer.complement_map j (pCore 2 P) K₀ hK
    rwa [pCore_map_iso] at hh
  have hC' : Nat.card (C₀.map j.toMonoidHom)=7 := by
    rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv,hC7]
  have hV' : Nat.card (V₀.map j.toMonoidHom)=8 := by
    rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv,hV8]
  have hd' : Disjoint (V₀.map j.toMonoidHom) (pCore 2 H) := by
    apply disjoint_def.mpr
    rintro _ ⟨x,hx,rfl⟩ hq
    have hqx:x∈pCore 2 P := by
      have hm : j x∈(pCore 2 P).map j.toMonoidHom := by rwa [pCore_map_iso]
      simpa only [mem_map_equiv,j.symm_apply_apply] using hm
    have hx1:x=1 := Subtype.ext (hVdis.le_bot ⟨hx,mem_map_of_mem (P).subtype hqx⟩)
    rw [hx1,map_one]
  have hn' : C₀.map j.toMonoidHom≤normalizer (V₀.map j.toMonoidHom:Set H) := by
    apply (map_mono (show C₀≤normalizer (V₀:Set P) from ?_)).trans (V₀.le_normalizer_map j.toMonoidHom)
    intro x hx
    exact V.le_normalizer_comap (P).subtype (hCV hx)
  have hi : (V₀.map j.toMonoidHom).map (QuotientGroup.mk' (pCore 2 H))=
      (R₀.map j.toMonoidHom).map (QuotientGroup.mk' (pCore 2 H)) := by
    rw [Subgroup.map_map,Subgroup.map_map]
    exact himages r.walk p.walk r.isPath p.isPath r.length_eq p.length_eq r.previous p.previous r.fixed
  obtain ⟨v,hv,he⟩ := hconj (K₀.map j.toMonoidHom) hK'
    (C₀.map j.toMonoidHom) (R₀.map j.toMonoidHom) (V₀.map j.toMonoidHom)
    (map_mono (subgroupOf_mono P hCK)) hC' (map_mono (subgroupOf_mono P hRK))
    ((pathRoot_isTwo r.walk).comap_subtype.map j.toMonoidHom) hV' hd' hn' hi
  exact lift_conjugacy P (cartan c) R V j hCP hRP hVP v hv he
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
/-- Original path-root conjugacy with every cardinality, normalization and
quotient-image hypothesis derived from the actual source geometry. -/
theorem source_reflected_root_conjugacy
    (c:CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) : HasReflectedRootConjugacy c := by
  exact assemble (L := Lₛ) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap c H
    (SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceReflectionRootProfile.source_eight_reflection_roots hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceTreeRootQuotient.source_tree_root_quotients hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceRootLiftConjugacy.source_same_image_root_conjugacy hG T hempty hM hu hmany hcard e H hH eR)
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectedRootConjugacy
