module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicSourceAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixNormalizer

/-!
# Naturality of the actual marked Sylow action

The original seed normal closure supplies its actual reduced action and B.5
conclusion. The full central cover from L/O₂(L) to its image transports the
proved natural action back through the literal quotient maps. Both central
kernels remain accounted for. No whole-block or Q₁-Sylow premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem cover_naturality {A B : Type*} [Group A] [Group B]
    (c : PerfectCentralCovering.Cover A B)
    (e : (A ⧸ center A) ≃* alternatingGroup (Fin 6))
    (a : MulAut A) (b : MulAut B)
    (hab : ∀ x, c.toMonoidHom (a x) = b (c.toMonoidHom x)) :
    MulAut.centralQuotientAction e a =
      MulAut.centralQuotientAction (c.quotientCenterEquiv.symm.trans e) b := by
  let d := c.quotientCenterEquiv
  have hd (x : A) : d (QuotientGroup.mk' (center A) x) =
      QuotientGroup.mk' (center B) (c.toMonoidHom x) := rfl
  let eB := d.symm.trans e
  have he (x : A) : eB (QuotientGroup.mk' (center B) (c.toMonoidHom x)) =
      e (QuotientGroup.mk' (center A) x) := by
    change e (d.symm _) = _
    rw [←hd,d.symm_apply_apply]
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := e.surjective x
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (center A) y
  rw [MulAut.centralQuotientAction_apply]
  change e (QuotientGroup.mk' (center A) (a z)) =
    MulAut.centralQuotientAction eB b (e (QuotientGroup.mk' (center A) z))
  rw [←he z,MulAut.centralQuotientAction_apply,←hab,he]

/-- The original marked Sylow has natural action on the same central core
quotient. The actual seed action supplies every classifier input internally. -/
theorem PreparedChosenModule.raw_six_cubic_sylow_natural
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    ∀ hn : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (L : Set G),
      ∀ x : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G) : Subgroup G),
        MulAut.centralQuotientAction e (pCoreNormalizerAction 2 L (inclusion hn x)) ∈
          _root_.AlternatingSix.ShadowLocal.natural := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let K := (L.subgroupOf H).map q
  obtain ⟨hr,_,hfit,hquasi,_,hKJ,⟨c⟩⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside houtM
  let := hr.elementary
  let : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let L0 := L.subgroupOf H
  let : L0.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer inf_le_right)
  let : K.Normal := (inferInstance : L0.Normal).map q (QuotientGroup.mk'_surjective C)
  let : IsQuasisimple K := hquasi
  have hquot : IsPGroup 2 ((H ⧸ C) ⧸ K) := by
    apply isPGroup_quotient_of_sup_eq_top K ((R.subgroupOf H).map q)
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left.trans inf_le_left)).comap_subtype.map q)
    rw [←Subgroup.map_sup,←subgroupOf_sup (show L ≤ H from le_sup_left)
      (show R ≤ H from le_sup_right),subgroupOf_self,map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  obtain ⟨f,f0,hfval,hf0,hfs,hf0s,hker,_⟩ :=
    h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside houtM
  let cover : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) K :=
    ⟨f0,hf0s,hi.quasisimple.toIsPerfect,hker⟩
  let eK := cover.quotientCenterEquiv.symm.trans e
  have hcenter : Nat.card (center K) ∣ 3 := by
    have hm : (center (L ⧸ pCore 2 L)).map f0 = center K := by
      rw [←cover.comap_center,map_comap_eq_self_of_surjective hf0s]
    rw [←hc,←hm]
    exact card_map_dvd _ f0
  intro hn x
  let y : H := ⟨x,mem_sup_right ⟨x.property,hn x.property⟩⟩
  have hnatural := raw_six_source_action_natural ρ K hquot hr.quotient_pCore_eq_bot
    hKJ c hcenter eK (q y)
  let a := pCoreNormalizerAction 2 L (inclusion hn x)
  let b : MulAut K := MulAut.conjNormal (q y)
  have hab : ∀ z, f0 (a z) = b (f0 z) := by
    intro z
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
    rw [pCoreNormalizerAction_mk,hf0,hf0]
    apply Subtype.ext
    rw [hfval]
    change q (inclusion le_sup_left (L.normalizerMonoidHom (inclusion hn x) z)) =
      q y * (f z : H ⧸ C) * (q y)⁻¹
    rw [hfval,←map_mul,←map_inv,←map_mul]
    congr 1
  have hh := cover_naturality cover e a b hab
  exact hh ▸ hnatural

end CFSG.Quasithin.Chapter15.Section01
