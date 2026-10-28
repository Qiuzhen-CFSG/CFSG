module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.NativeRestriction
public import Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.Restriction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.CoreTransfer

/-!
# Native Sylow and quotient action transport from original extension markings

The original S embeds as flag-preserving automorphisms through both full
endpoint maps. A source local Sylow lying in the native overlap equals its
normal Sylow by relative Sylow maximality. Transporting normalizers then
identifies the whole local Borel, including its odd part, and carries the
source right-Borel normalization to the same S image.

Separately, the original join-core lies in S and its commutators with the
selected perfect R lie in O₂(R). The faithful inner marking carries these
to the native residual two-core, proving trivial quotient action without
assuming that the actor itself is inner. The adjacent unitary-five module
instantiates the native geometry and the literal Chapter 12 application.

Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(refs/quasithin.pdf). No equality S=T or R=O²(H) is used.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace OriginalExtension
variable {G X : Type*} [Group G] [Group X]
  {L R S : Subgroup G} {K₀ K₁ P₀ P₁ : Subgroup X}
  (e : Marking L R S K₀ K₁ P₀ P₁)

/-- The marking on every element of the actual source S. -/
def Marking.sylowHom : S →* MulAut X :=
  e.right.comp (inclusion (le_sup_right.trans le_sup_left))

theorem Marking.sylowHom_left (s : S) :
    e.sylowHom s = e.left (inclusion (le_sup_right.trans le_sup_left) s) := by
  have h0 : S ≤ ChapterF.Source.parabolic ![L,R] S 0 := le_sup_right.trans le_sup_left
  have h1 : S ≤ ChapterF.Source.parabolic ![L,R] S 1 := le_sup_right.trans le_sup_left
  exact (e.agrees ⟨s.val,h0 s.property,h1 s.property⟩).symm

theorem Marking.sylowHom_injective : Function.Injective e.sylowHom :=
  e.right_injective.comp (inclusion_injective _)

theorem preserves_base
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (A : Subgroup (MulAut X)) (P : Subgroup X)
    (hbase : A ⊓ MulAut.innerSubgroup X = P.map MulAut.conj)
    (a : MulAut X) (ha : a ∈ A) : P.map a.toMonoidHom = P := by
  apply Subgroup.map_injective hi
  have he : MulAut.conj.comp a.toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp MulAut.conj := by
    ext x y
    simp
  rw [map_map,he,←map_map,←hbase,map_inf _ _ _ (MulAut.conj a).injective]
  have hA := mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer ha)
  have hI := mem_normalizer_iff_map_conj_eq.mp
    (show a ∈ normalizer (MulAut.innerSubgroup X : Set _) from
      (normalizer_eq_top (MulAut.innerSubgroup X)) ▸ mem_top a)
  exact congrArg₂ (· ⊓ ·) hA hI

def Marking.sylowFlagHom (hi : Function.Injective (MulAut.conj : X →* MulAut X)) :
    S →* Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.flagAutomorphisms P₀ P₁ :=
  e.sylowHom.codRestrict _ (fun s => ⟨
    preserves_base hi e.left.range P₀ e.left_base _
      (e.sylowHom_left s ▸ ⟨_,rfl⟩),
    preserves_base hi e.right.range P₁ e.right_base _ ⟨_,rfl⟩⟩)

@[simp] theorem Marking.sylowFlagHom_val
    (hi : Function.Injective (MulAut.conj : X →* MulAut X)) (s : S) :
    (e.sylowFlagHom hi s).val = e.sylowHom s := rfl

end OriginalExtension

namespace Preparation
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)

include d h hTH in
/-- A marked native normal Sylow identifies the actual local intersection,
using the source's relative Sylow witness, rather than its ambient Sylow. -/
theorem original_localSylow_image [Finite X] (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* MulAut X)
    (hf : Function.Injective f)
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (K D U : Subgroup X)
    (hU : IsPGroup 2 U) (_hUD : U ≤ D) (hUn : (U.subgroupOf D).Normal)
    (hUi : ¬ 2 ∣ (U.subgroupOf D).index) (hUK : U ≤ K)
    (hK : ((![L,R] i).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f = K.map MulAut.conj)
    (hD : (((sourceS L H ⊓ ![L,R] i : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f) ≤ D.map MulAut.conj) :
    (((sourceS L H ⊓ ![L,R] i : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f) = U.map MulAut.conj := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  let V := ((sourceS L H ⊓ ![L,R] i : Subgroup G).subgroupOf P).map f
  have hKP : ![L,R] i ≤ P := le_sup_left.trans le_sup_left
  have hVP : sourceS L H ⊓ ![L,R] i ≤ P := inf_le_right.trans hKP
  have hs : Chapter1.IsSylowIn 2 V (K.map MulAut.conj) := by
    rw [←hK]
    apply (Chapter1.IsSylowIn.map_iff f hf).mpr
    apply (Chapter1.IsSylowIn.map_iff P.subtype P.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hKP,map_subgroupOf_eq_of_le hVP]
    exact (d.hypothesisF11 h hTH).sylow i
  have hV : IsPGroup 2 V := (Chapter1.isSylowIn_iff.mp hs).1
  let V' := V.comap (MulAut.conj : X →* MulAut X)
  have hV' : IsPGroup 2 V' := hV.comap_of_injective _ hi
  have hV'D : V' ≤ D := by
    intro x hx
    exact (mem_map_iff_mem hi).mp (hD hx)
  let := hUn
  have hVU : V' ≤ U := by
    intro x hx
    exact IsPGroup.le_normal_of_index_primeTo (U.subgroupOf D)
      (V'.subgroupOf D) hV'.comap_subtype hUi
      (show (⟨x,hV'D hx⟩ : D) ∈ V'.subgroupOf D from hx)
  have hle : V ≤ U.map MulAut.conj := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := hD ha
    exact mem_map_of_mem _ (hVU ha)
  exact ((Chapter1.isSylowIn_iff.mp hs).2.2 _ (hU.map _) hle (map_mono hUK)).symm
end Preparation

namespace OriginalExtension
open scoped commutatorElement
variable {G X : Type*} [Group G] [Group X]

private theorem join_core_commutator (K U : Subgroup G)
    (hn : U ≤ normalizer (K : Set G)) {g : G}
    (hg : g ∈ (K ⊔ U).pCoreIn 2) (x : K) : ⁅g,x.val⁆ ∈ K.pCoreIn 2 := by
  let J := K ⊔ U
  let K' := K.subgroupOf J
  let : K'.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hg' : (⟨g,map_subtype_le _ hg⟩ : J) ∈ pCore 2 J :=
    (mem_map_iff_mem J.subtype_injective).mp hg
  have hKJ : K ≤ J := le_sup_left
  have hc := normal_pCore_commutator_mem 2 K' hg' (⟨⟨x.val,hKJ x.property⟩,x.property⟩ : K')
  have hc' := mem_map_of_mem J.subtype hc
  change ⁅g,x.val⁆ ∈ (K'.pCoreIn 2).map J.subtype at hc'
  rw [map_pCoreIn_of_injective 2 K' J.subtype J.subtype_injective,
    map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)] at hc'
  exact hc'

/-- Core elements of a marked local join act trivially on the native
local modulo its intrinsic two-core. The actor itself is not assumed inner. -/
theorem native_core_action (K U : Subgroup G)
    (hn : U ≤ normalizer (K : Set G))
    (f : G →* MulAut X) (hf : Function.Injective f)
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (N : Subgroup X) (hK : K.map f = N.map MulAut.conj)
    {g : G} (hg : g ∈ (K ⊔ U).pCoreIn 2) (x : N) :
    f g x.val / x.val ∈ N.pCoreIn 2 := by
  have hx : MulAut.conj x.val ∈ K.map f := hK ▸ mem_map_of_mem MulAut.conj x.property
  obtain ⟨y,hy,he⟩ := hx
  have hc := mem_map_of_mem f (join_core_commutator K U hn hg ⟨y,hy⟩)
  rw [map_pCoreIn_of_injective 2 K f hf,hK,
    ←map_pCoreIn_of_injective 2 N MulAut.conj hi] at hc
  have hcomm : f ⁅g,y⁆ = ⁅f g,MulAut.conj x.val⁆ := by
    simp only [commutatorElement_def,map_mul,map_inv,he]
  have hinner : MulAut.conj (f g x.val / x.val) = ⁅f g,MulAut.conj x.val⁆ := by
    apply MulEquiv.ext
    intro z
    change (f g x.val / x.val)*z*(f g x.val / x.val)⁻¹ =
      f g (x.val*(f g).symm (x.val⁻¹*z*x.val)*x.val⁻¹)
    simp only [div_eq_mul_inv,map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  rw [hcomm,←hinner] at hc
  exact (mem_map_iff_mem hi).mp hc
end OriginalExtension

namespace Preparation
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  {K₀ K₁ P₀ P₁ : Subgroup X}
  (e : OriginalExtension.Marking L R (sourceS L H) K₀ K₁ P₀ P₁)

include d h hTH in
/-- The source join core lies in the actual source S, by relative Sylow
restriction inside its parabolic. -/
theorem original_right_core_le_sourceS : (R ⊔ sourceS L H).pCoreIn 2 ≤ sourceS L H := by
  have hs : Chapter1.IsSylowIn 2 (sourceS L H)
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :=
    (d.hypothesisF11 h hTH).sylow_parabolic 1
  obtain ⟨Q,hQ⟩ := hs.restrict (show sourceS L H ≤ R ⊔ sourceS L H from le_sup_right)
    (show R ⊔ sourceS L H ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 from le_sup_left)
  apply le_trans (b := (Q : Subgroup (R ⊔ sourceS L H : Subgroup G)).map (R ⊔ sourceS L H).subtype) _ hQ.le
  exact Subgroup.map_mono (f := (R ⊔ sourceS L H).subtype)
    (pCore_isPGroup (p := 2) (G := (R ⊔ sourceS L H : Subgroup G))
      |>.le_sylow_of_normal Q)

include d h hTH hp in
/-- Every source join-core element acts trivially on the marked right
native residual quotient. The original endpoint, source S and selected R
are retained throughout. -/
theorem original_right_core_native_action
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (g : sourceS L H) (hg : g.val ∈ (R ⊔ sourceS L H).pCoreIn 2)
    (x : K₁) : e.sylowHom g x.val / x.val ∈ K₁.pCoreIn 2 := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  let K := R.subgroupOf P
  let U := (sourceS L H).subgroupOf P
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hn : U ≤ normalizer (K : Set P) := by
    rw [←subgroupOf_normalizer_eq hRP]
    exact comap_mono d.S_normalizes_right
  have hK : K.map e.right = K₁.map MulAut.conj := by
    have he := d.original_local_eq_residual h hTH hp 1
    change K = _ at he
    rw [he,e.right_residual]
  have hcore : ((K ⊔ U).pCoreIn 2).map P.subtype = (R ⊔ sourceS L H).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hRP,map_subgroupOf_eq_of_le hSP]
  have hg' : (⟨g.val,hSP g.property⟩ : P) ∈ (K ⊔ U).pCoreIn 2 := by
    apply (mem_map_iff_mem P.subtype_injective).mp
    rwa [hcore]
  exact OriginalExtension.native_core_action K U hn e.right e.right_injective hi K₁ hK hg' x
end Preparation

namespace OriginalExtension
variable {G X : Type*} [Group G] [Group X]

private theorem map_inf_normalizer (K U : Subgroup G) (f : G →* X)
    (hf : Function.Injective f) :
    (K ⊓ normalizer (U : Set G)).map f = K.map f ⊓ normalizer (U.map f : Set X) := by
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left)
      ((map_mono inf_le_right).trans (U.le_normalizer_map f))
  · rintro x ⟨⟨y,hy,rfl⟩,hn⟩
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    have hh : y ∈ (normalizer (U.map f : Set X)).comap f := hn
    rwa [comap_normalizer_eq_of_le_range (map_le_range f U),
      comap_map_eq_self_of_injective hf] at hh
end OriginalExtension

namespace Preparation
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  {K₀ K₁ P₀ P₁ : Subgroup X}
  (e : OriginalExtension.Marking L R (sourceS L H) K₀ K₁ P₀ P₁)
include d h hTH hp

/-- The original right Borel maps onto the entire native local Borel,
including its odd part, under the same endpoint marking. -/
theorem original_right_borel_image
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (U : Subgroup X)
    (hs : (((sourceS L H ⊓ R : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right) = U.map MulAut.conj) :
    ((ChapterF.Source.borel R (sourceS L H)).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right =
      (K₁ ⊓ normalizer (U : Set X)).map MulAut.conj := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hUP : sourceS L H ⊓ R ≤ P := inf_le_right.trans (le_sup_left.trans le_sup_left)
  have hb : (ChapterF.Source.borel R (sourceS L H)).subgroupOf P =
      R.subgroupOf P ⊓ normalizer ((sourceS L H ⊓ R : Subgroup G).subgroupOf P : Set P) := by
    rw [←subgroupOf_normalizer_eq hUP]
    rfl
  have he := d.original_local_eq_residual h hTH hp 1
  change R.subgroupOf P = _ at he
  rw [hb,OriginalExtension.map_inf_normalizer _ _ _ e.right_injective,
    he,e.right_residual,hs,OriginalExtension.map_inf_normalizer _ _ _ hi]

/-- Transport the normalized-Borel source hypothesis through the literal
right endpoint. No normality of S in the full odd overlap is asserted. -/
theorem original_right_borel_normalizes_image
    (hi : Function.Injective (MulAut.conj : X →* MulAut X))
    (U : Subgroup X)
    (hs : (((sourceS L H ⊓ R : Subgroup G).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right) = U.map MulAut.conj) :
    (K₁ ⊓ normalizer (U : Set X)).map MulAut.conj ≤ normalizer (e.sylowHom.range : Set _) := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hn : (ChapterF.Source.borel R (sourceS L H)).subgroupOf P ≤
      normalizer ((sourceS L H).subgroupOf P : Set P) := by
    rw [←subgroupOf_normalizer_eq hSP]
    exact comap_mono d.right_borel_normalizes_sourceS
  have he : e.sylowHom.range = ((sourceS L H).subgroupOf P).map e.right := by
    rw [OriginalExtension.Marking.sylowHom,MonoidHom.range_comp,inclusion_range]
  rw [←d.original_right_borel_image h hTH hp e hi U hs,he]
  exact (map_mono hn).trans (le_normalizer_map e.right)
end Preparation

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
