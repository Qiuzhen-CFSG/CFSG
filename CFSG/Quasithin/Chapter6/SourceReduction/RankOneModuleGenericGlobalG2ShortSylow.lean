module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Nonfusion
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Nonfusion
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.SaturatedCentralizerCard
public import Theory.GroupTheory.SaturatedCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionFusion
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionFusion
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionFusionModel

/-!
# Extremality of the designated G₂ short-root involution

The full concrete short-root centralizer lies in the long local factor.
Its rank-one projection bounds the image of every two-subgroup by q, while
its kernel has only the A, B and C coordinates and hence order at most q³.
The four free A, B, C and E coordinates attain q⁴ in the common Sylow.

The existing local involution reduction tracks ambient and model conjugacy
simultaneously through the same compatible maps. Ambient nonfusion forces
each conjugate of the designated short root in S to belong to the concrete
short class. The q⁴ bound then holds at every such conjugate. Under S=T,
a maximal Sylow-centralizer choice proves that the designated root itself
is extremal: C_S(v) is Sylow in the full C_G(v), with order exactly q⁴.

The internal imports deliberately reuse the coordinate calculation and
local reduction of the earlier parts of this same proof family, preserving
their public boundaries. The predicate formulation avoids the kernel cost
of instantiating the reduction on a product of concrete groups. The Chapter
12 companion applies the result and discharges S=T at odd original degrees.
Even-degree transfer and the F.4.42 full-centralizer containment remain;
neither completion recognition nor GlobalExit follows from extremality alone.

Source: Aschbacher–Smith F.4.27 and F.4.40, printed pp.288–289 and 294,
and 5.3.3, p.659 (`refs/quasithin.pdf`). Root calculations reuse the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.ShortRootProducts.CentralizerCore
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortSylow
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem centralizer_le_local :
    centralizer ({rootC (1:F)} : Set (Model F)) ≤ local₂ := by
  intro g hg
  obtain ⟨p,c,M,rfl⟩ := centralizer_rootC_factor 1 one_ne_zero hg
  exact local₂.mul_mem
    (local₂.mul_mem (residualBlock_le_local (mem_sup_left ⟨p,rfl⟩))
      (unipotent_le_local₂ (shortRootGroup_le_unipotent ⟨Multiplicative.ofAdd c,rfl⟩)))
    (block_mem_local₂ M)

/-- The full model short-root centralizer has no two-subgroup larger than q⁴. -/
theorem two_subgroup_card_le (D : Subgroup (Model F)) (hD : IsPGroup 2 D)
    (hDC : D ≤ centralizer ({rootC (1:F)} : Set (Model F))) :
    Nat.card D ≤ Nat.card F^4 := by
  let f : D →* Matrix.SpecialLinearGroup (Fin 2) F :=
    longSLHom.comp (inclusion (hDC.trans centralizer_le_local))
  have hker (x : f.ker) : ∃ t : Fin 6 → F,
      t 3=0 ∧ t 4=0 ∧ t 5=0 ∧ unipotentProduct t=x.val.val := by
    have hx : (inclusion (hDC.trans centralizer_le_local) x.val) ∈ longSLHom.ker := x.property
    rw [longSLHom_ker] at hx
    obtain ⟨t,ht,he⟩ := hx
    have hc : Commute (unipotentProduct t) (rootC (1:F)) :=
      he.symm ▸ mem_centralizer_singleton_iff.mp (hDC x.val.property)
    obtain ⟨h3,h5⟩ := G2Nonfusion.centralizer_coordinates t hc
    exact ⟨t,h3,ht,h5,he⟩
  let a (x : f.ker) : Fin 3 → F :=
    ![unipotentParameters x.val.val 0,unipotentParameters x.val.val 1,
      unipotentParameters x.val.val 2]
  have ha : Function.Injective a := by
    intro x y he
    obtain ⟨t,h3,h4,h5,ht⟩ := hker x
    obtain ⟨u,k3,k4,k5,hu⟩ := hker y
    have htU : t=u := by
      have he' : ![t 0,t 1,t 2] = ![u 0,u 1,u 2] := by
        simpa only [a,←ht,←hu,unipotentParameters_product] using he
      ext i
      fin_cases i
      · exact congrFun he' 0
      · exact congrFun he' 1
      · exact congrFun he' 2
      · exact h3.trans k3.symm
      · exact h4.trans k4.symm
      · exact h5.trans k5.symm
    exact Subtype.ext (Subtype.ext (ht.symm.trans ((congrArg unipotentProduct htU).trans hu)))
  have hkcard : Nat.card f.ker ≤ Nat.card F^3 := by
    simpa only [Nat.card_fun,Nat.card_fin] using Nat.card_le_card_of_injective a ha
  obtain ⟨P,hP⟩ := (hD.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hr : Nat.card f.range ≤ Nat.card F := by
    calc
      _ ≤ Nat.card P := card_le_of_le hP
      _ = Nat.card F := (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv).symm
  calc
    Nat.card D = Nat.card f.ker * Nat.card f.range := by
      rw [←index_ker,f.ker.card_mul_index]
    _ ≤ Nat.card F^3 * Nat.card F := Nat.mul_le_mul hkcard hr
    _ = Nat.card F^4 := by ring

/-- The four free positive-root coordinates form the entire Sylow centralizer. -/
theorem short_sylow_centralizer_card :
    Nat.card (unipotent ⊓ centralizer ({rootC (1:F)} : Set (Model F)) : Subgroup (Model F)) =
      Nat.card F^4 := by
  let D := unipotent ⊓ centralizer ({rootC (1:F)} : Set (Model F))
  apply le_antisymm (two_subgroup_card_le D (unipotent_isTwoGroup.to_le inf_le_left) inf_le_right)
  let f : (Fin 4 → F) → D := fun t => ⟨unipotentProduct ![t 0,t 1,t 2,0,t 3,0],
    unipotentProduct_mem _,mem_centralizer_singleton_iff.mpr (by
      have hc : rootC (1:F)=unipotentProduct ![0,0,1,0,0,0] := by simp [unipotentProduct]
      rw [hc,unipotentProduct_mul,unipotentProduct_mul]
      congr 1
      ext i
      fin_cases i <;> simp [unipotentProductParameters,add_comm])⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh := unipotentProduct_injective (congrArg Subtype.val he)
    ext i
    fin_cases i
    · exact congrFun hh 0
    · exact congrFun hh 1
    · exact congrFun hh 2
    · exact congrFun hh 4
  simpa only [Nat.card_fun,Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The pinned short involution is extremal in the concrete common Sylow. -/
theorem short_saturated (D : Subgroup (Model F)) (hD : IsPGroup 2 D)
    (hED : unipotent ⊓ centralizer ({rootC (1:F)} : Set (Model F)) ≤ D)
    (hDC : D ≤ centralizer ({rootC (1:F)} : Set (Model F))) :
    D = unipotent ⊓ centralizer ({rootC (1:F)} : Set (Model F)) := by
  exact (eq_of_le_of_card_ge hED (by
    rw [short_sylow_centralizer_card]
    exact two_subgroup_card_le D hD hDC)).symm


private theorem centralizer_image {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) (U : Subgroup X) (x : X) :
    (U ⊓ centralizer ({x} : Set X)).map f =
      U.map f ⊓ centralizer ({f x} : Set Y) := by
  ext y
  constructor
  · rintro ⟨a,⟨ha,hc⟩,rfl⟩
    refine ⟨mem_map_of_mem f ha,mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hc)
  · rintro ⟨⟨a,ha,rfl⟩,hc⟩
    refine ⟨a,⟨ha,mem_centralizer_singleton_iff.mpr (hf ?_)⟩,rfl⟩
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] [Finite F] [CharP F 2] in
private theorem centralizer_card_transport
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (S : Subgroup G) (hS : (unipotent.subgroupOf parabolic₁).map f=S)
    (x : parabolic₁ (F := F)) :
    Nat.card (S ⊓ centralizer ({f x} : Set G) : Subgroup G) =
      Nat.card (unipotent ⊓ centralizer ({x.val} : Set (Model F)) : Subgroup (Model F)) := by
  have hm := centralizer_image f hf (unipotent.subgroupOf parabolic₁) x
  rw [hS] at hm
  have hn := centralizer_image (parabolic₁ (F := F)).subtype Subtype.val_injective
    (unipotent.subgroupOf parabolic₁) x
  rw [map_subgroupOf_eq_of_le (le_sup_left.trans borel_le_parabolic₁)] at hn
  change (unipotent.subgroupOf parabolic₁ ⊓ centralizer ({x} : Set (parabolic₁ (F := F)))).map
    (parabolic₁ (F := F)).subtype = unipotent ⊓ centralizer ({x.val} : Set (Model F)) at hn
  rw [←hm,←hn,card_map_of_injective hf,card_map_of_injective Subtype.val_injective]

omit [Finite G] in
/-- The existing local reduction tracks the ambient short class and model
short class together, without expanding a product of concrete group instances. -/
private theorem short_class_transport
    (f : parabolic₁ (F := F) →* G) (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x∈parabolic₁) (hy : x∈parabolic₂), f ⟨x,hx⟩=l ⟨x,hy⟩)
    (hn : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)))
    (x : parabolic₁ (F := F)) (hx : x.val∈unipotent)
    (hx2 : x^2=1) (hx1 : x≠1)
    (hfx : IsConj (f (G2CompletionFusion.short 1)) (f x)) :
    IsConj (rootC (1:F)) x.val := by
  let : Group (Model F) := inferInstance
  let : Group (parabolic₁ (F := F)) := Subgroup.toGroup _
  let : Group (parabolic₂ (F := F)) := Subgroup.toGroup _
  let P : Model F → Prop := fun y => ∀ hy : y∈parabolic₁,
    IsConj (f (G2CompletionFusion.short 1)) (f ⟨y,hy⟩) → IsConj (rootC (1:F)) y
  have hA (a : F) (ha0 : a≠0) : P (rootA a) := by
    intro hy hh
    exact (hn ((G2CompletionFusion.long_conj_one f a ha0).trans hh.symm)).elim
  have hC (a : F) (ha0 : a≠0) : P (rootC a) := by
    intro _ _
    exact G2CompletionFusion.short_conj_one (parabolic₁ (F := F)).subtype a ha0
  have hstep : ∀ g : Model F, g∈parabolic₁ ∨ g∈parabolic₂ →
      ∀ y∈unipotent, MulAut.conj g y∈unipotent → (P (MulAut.conj g y) ↔ P y) := by
    intro g hg y hy hgy
    have hc : IsConj (f ⟨y,G2CompletionFusion.u1 hy⟩)
        (f ⟨MulAut.conj g y,G2CompletionFusion.u1 hgy⟩) := by
      rcases hg with hg|hg
      · exact G2CompletionFusion.map_local_conj f g hg y _
          (G2CompletionFusion.u1 hy) (G2CompletionFusion.u1 hgy) rfl
      · rw [ha y (G2CompletionFusion.u1 hy) (G2CompletionFusion.u2 hy),
          ha _ (G2CompletionFusion.u1 hgy) (G2CompletionFusion.u2 hgy)]
        apply isConj_iff.mpr
        refine ⟨l ⟨g,hg⟩,?_⟩
        rw [←map_inv,←map_mul,←map_mul]
        rfl
    have hm : IsConj y (MulAut.conj g y) := isConj_iff.mpr ⟨g,rfl⟩
    constructor
    · intro hh _ hf'
      exact (hh (G2CompletionFusion.u1 hgy) (hf'.trans hc)).trans hm.symm
    · intro hh _ hf'
      exact (hh (G2CompletionFusion.u1 hy) (hf'.trans hc.symm)).trans hm
  rw [unipotent_eq_range] at hx
  obtain ⟨t,ht⟩ := hx
  have hs : unipotentProduct t ^ 2=1 := by
    rw [ht]
    exact congrArg Subtype.val hx2
  have hne : unipotentProduct t≠1 := by
    rw [ht]
    exact fun hh => hx1 (Subtype.ext hh)
  have hh := G2CompletionFusion.unipotent_reduction P hA hC hstep t hs hne
  rw [ht] at hh
  exact hh x.property hfx

/-- F.4.40 for a faithful compatible G₂ pair whose common Sylow is ambient.
No homomorphism from the full model is needed. -/
private theorem compatible_short_sylow
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x∈parabolic₁) (hy : x∈parabolic₂), f ⟨x,hx⟩=l ⟨x,hy⟩)
    (T : Sylow 2 G) (hS : (unipotent.subgroupOf parabolic₁).map f=(T : Subgroup G))
    (hn : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1))) :
    let v := f (G2CompletionFusion.short (1:F))
    Nat.card ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Subgroup G)=Nat.card F^4 ∧
      ∃ P : Sylow 2 (centralizer ({v} : Set G)),
        (P : Subgroup (centralizer ({v} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v} : Set G)) := by
  let v := f (G2CompletionFusion.short (1:F))
  let E := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  have hcard : Nat.card E=Nat.card F^4 :=
    (centralizer_card_transport f hf _ hS (G2CompletionFusion.short 1)).trans short_sylow_centralizer_card
  have hvT : v∈(T : Subgroup G) := by
    rw [←hS]
    exact mem_map_of_mem f (show rootC (1:F)∈unipotent from subset_closure (by simp))
  have hv2 : orderOf v=2 := by
    rw [show v=f (G2CompletionFusion.short (1:F)) from rfl,orderOf_injective f hf,
      ←orderOf_injective (parabolic₁ (F := F)).subtype Subtype.val_injective]
    apply orderOf_eq_prime
    · change rootC (1:F)^2=1
      rw [pow_two,rootC_add,CharTwo.add_self_eq_zero,rootC_zero]
    · change rootC (1:F)≠1
      exact fun hh => one_ne_zero (rootC_injective (hh.trans rootC_zero.symm))
  have hbound (x : T) (hvx : IsConj v x.val) :
      Nat.card ((T : Subgroup G) ⊓ centralizer ({x.val} : Set G) : Subgroup G) ≤ Nat.card F^4 := by
    have hx : x.val∈(unipotent.subgroupOf parabolic₁).map f := hS.symm ▸ x.property
    obtain ⟨y,hy,he⟩ := hx
    have hy2 : orderOf y=2 := by
      rw [←orderOf_injective f hf y,he]
      obtain ⟨g,hg⟩ := isConj_iff.mp hvx
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq v).trans hv2
    have hc := short_class_transport f l ha hn y hy
      (by simpa only [hy2] using pow_orderOf_eq_one y)
      (fun h => by simp [h] at hy2) (he.symm ▸ hvx)
    rw [←he,centralizer_card_transport f hf _ hS y]
    have hh := card_le_of_isConj_of_saturated_centralizer
      (rootC (1:F)) y.val hc
      (unipotent ⊓ centralizer ({rootC (1:F)} : Set (Model F)))
      (unipotent_isTwoGroup.to_le inf_le_left) inf_le_right short_saturated
      (unipotent ⊓ centralizer ({y.val} : Set (Model F)))
      (unipotent_isTwoGroup.to_le inf_le_left) inf_le_right
    rwa [short_sylow_centralizer_card] at hh
  obtain ⟨x,hvx,hmax⟩ := T.exists_conjugate_with_saturated_centralizer ⟨v,hvT⟩
  have hmax' : ∀ D : Subgroup G, IsPGroup 2 D →
      (T : Subgroup G) ⊓ centralizer ({x.val} : Set G) ≤ D →
      D ≤ centralizer ({x.val} : Set G) →
      D=(T : Subgroup G) ⊓ centralizer ({x.val} : Set G) := by
    have he := map_subtype_centralizer_singleton (T : Subgroup G) x
    change (centralizer ({x} : Set T)).map (T : Subgroup G).subtype =
      (T : Subgroup G) ⊓ centralizer ({x.val} : Set G) at he
    rw [he] at hmax
    exact hmax
  let C := centralizer ({v} : Set G)
  obtain ⟨P,hP⟩ := (T.isPGroup'.comap_subtype (K:=C)).exists_le_sylow
  have hPcard : Nat.card ((P : Subgroup C).map C.subtype) ≤ Nat.card E := by
    rw [hcard]
    exact (card_le_of_isConj_of_saturated_centralizer x.val v hvx.symm
      ((T : Subgroup G) ⊓ centralizer ({x.val} : Set G))
      (T.isPGroup'.to_le inf_le_left) inf_le_right hmax' _
      (P.isPGroup'.map _) (map_subtype_le _)).trans (hbound x hvx)
  refine ⟨hcard,P,?_⟩
  apply (eq_of_le_of_card_ge hP ?_).symm
  rw [←card_map_of_injective C.subtype_injective]
  have hEC : Nat.card ((T : Subgroup G).subgroupOf C) = Nat.card E := by
    rw [←card_map_of_injective C.subtype_injective,subgroupOf_map_subtype]
  exact hPcard.trans_eq hEC.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortSylow

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]

private theorem source_g2_inverse_sylow_image
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ((unipotent (K := F)).subgroupOf parabolic₁).map
      ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).subtype.comp
        e.right.symm.toMonoidHom) = sourceS L H := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  obtain ⟨D,hD⟩ := (d.hypothesisF11 h hTH).sylow_parabolic 1
  let U := ((unipotent (K := F)).subgroupOf parabolic₁).map e.right.symm.toMonoidHom
  have hDU : (D : Subgroup P) ≤ U := by
    intro x hx
    have hxS : x.val∈sourceS L H := hD.le (mem_map_of_mem P.subtype hx)
    exact ⟨e.right x,source_g2_sylow_image e x hxS,e.right.symm_apply_apply x⟩
  have heq := D.is_maximal'
    ((unipotent_isTwoGroup.comap_subtype).map e.right.symm.toMonoidHom) hDU
  rw [←map_map]
  change U.map P.subtype=sourceS L H
  change U=(D : Subgroup P) at heq
  rw [heq]
  exact hD

/-- The designated short-root centralizer is extremal in the original S=T.
Its order is q⁴, and the returned Sylow subgroup is the literal intersection
with the full ambient centralizer, under the same compatible local maps. -/
theorem Preparation.g2_short_centralizer_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (hST : sourceS L H = (T : Subgroup G)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let v : G := (e.right.symm (G2CompletionFusion.short (1:F))).val
      Nat.card (sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G) = Nat.card F^4 ∧
        ∃ P : Sylow 2 (centralizer ({v} : Set G)),
          (P : Subgroup (centralizer ({v} : Set G))) =
            (sourceS L H).subgroupOf (centralizer ({v} : Set G)) := by
  obtain ⟨e,z,v,hz,hv,_,_,_,hn,classes⟩ := d.g2_completion_involution_classes h hH hp F he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let P₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic₂ (F := F) →* G := P₀.subtype.comp e.left.symm.toMonoidHom
  have ha (x : Model F) (hx : x∈parabolic₁) (hy : x∈parabolic₂) :
      f ⟨x,hx⟩=l ⟨x,hy⟩ := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨x,hx,hy⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  have hf := P.subtype_injective.comp e.right.symm.injective
  have hs : (unipotent.subgroupOf parabolic₁).map f=(T : Subgroup G) :=
    (source_g2_inverse_sylow_image d h hH.1.1.2 e).trans hST
  have hnon : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)) := by
    change ¬ IsConj (e.right.symm (G2CompletionFusion.long 1)).val
      (e.right.symm (G2CompletionFusion.short 1)).val
    rwa [←hz,←hv]
  have hh := G2ShortSylow.compatible_short_sylow f hf l ha T hs hnon
  dsimp only at hh
  have hvf : f (G2CompletionFusion.short (1:F))=v.val := hv.symm
  rw [hvf] at hh
  refine ⟨e,?_⟩
  dsimp only
  rw [←hv]
  simpa only [hST] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
