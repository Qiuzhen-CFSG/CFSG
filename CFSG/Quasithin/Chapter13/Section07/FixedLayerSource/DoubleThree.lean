module
public import CFSG.Quasithin.Chapter13.Section07.ComponentFaithfulness
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
public import Theory.Quasithin.NormalTwoQuotient
public import Theory.Representation.BinaryOffender.WholeSubspace
public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.TwoLayers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The doubled natural tilde module in the original fixed-layer case

Use the original best offender D inside the opposite span and the selected
component J. The smaller actor E=J∨D has a two-group quotient over J, so its
three-rank is at most one in the binary SL3 row. The faithful Irr⁺ plus action
kills O₂(E). The component-moved tilde action is faithful and not Irr⁺ by the
two-layer extraction, and B.5 therefore gives two copies with the same actual
component marking. No three-rank hypothesis on all of H/O₂(H) is needed.

The source consumer retains the original conjugator and canonical U_H/V₁
coordinates. Its PSL3(2) carrier hypothesis is the selected row of the earlier
restricted source catalogue; the natural marking of [U₀,K] is a later step.
Source: Aschbacher–Smith13.7.16(2), printed p.944, using B.5.6.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem component_overgroup_twoCore_eq_bot
    (σ : Representation (ZMod 2) G V) (hf : Function.Injective σ)
    {J : Subgroup G} (hi : IsIrrPlus σ J ⊤) (hJ : IsComponent G J)
    (E : Subgroup G) (hJE : J ≤ E) : pCore 2 E = ⊥ := by
  let P := (pCore 2 E).map E.subtype
  let : Group.IsNilpotent (pCore 2 E) := pCore_isNilpotent
  have hc : P ≤ centralizer (J : Set G) := by
    have hh := le_centralizer_iff.mp ((hJ.subgroupOf hJE).le_centralizer_of_solvable_normal (pCore 2 E))
    rintro p ⟨q,hq,rfl⟩ j hj
    exact congrArg Subtype.val (hh hq ⟨j,hJE hj⟩ hj)
  have hfix := IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes σ hi
    (show IsPGroup 2 P from pCore_isPGroup.map E.subtype) hc
    (le_subspaceStabilizer σ ⊤ (by intros; trivial))
  have hb : P = ⊥ := by
    apply bot_unique
    intro p hp
    apply mem_bot.mpr
    apply hf
    ext v
    simpa only [map_one,Module.End.one_apply,MonoidHom.comp_apply,Subgroup.subtype_apply]
      using hfix Submodule.mem_top ⟨p,hp⟩
  exact (map_eq_bot_iff_of_injective (pCore 2 E) E.subtype_injective).mp hb



theorem doubleThree_of_component_overgroup
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]
    (σ : Representation (ZMod 2) G V) (hf : Function.Injective σ)
    (σ₀ : Representation (ZMod 2) G V₀) (hf₀ : Function.Injective σ₀)
    (cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple G)
    {J D : Subgroup G} [J.Normal] [IsSimpleGroup J]
    (hi : IsIrrPlus σ₀ J ⊤) (hJ : IsComponent G J)
    (hc : Nat.card J = 168) (hD2 : IsPGroup 2 D)
    (hD : IsBestOffender σ D) (hcomm : ⁅J,D⁆ = J)
    (hm : moved σ J = ⊤) (hn : ¬ IsIrrPlus σ J ⊤) :
    Nonempty (ChapterB.QuasisimpleSource.ActionEquiv (σ.comp J.subtype)
      (ChapterB.QuasisimpleSource.repeated
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3) 2)) := by
  let E := J ⊔ D
  let C := J.subgroupOf E
  have hJE : J ≤ E := le_sup_left
  have hDE : D ≤ E := le_sup_right
  let : C.Normal := inferInstance
  let : IsQuasisimple J := hJ.2
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hJE).symm
  have hcore := component_overgroup_twoCore_eq_bot σ₀ hf₀ hi hJ E hJE
  have hC : IsComponent E C := hJ.subgroupOf hJE
  have hD' := hD.subgroupOf σ hDE
  have hcomm' : ⁅C,D.subgroupOf E⁆ = C := by
    apply Subgroup.map_injective E.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hJE,map_subgroupOf_eq_of_le hDE,hcomm]
  have hCN := (ChapterB.SourceInduction.moved_component_in_offenderSubgroup
    (σ.comp E.subtype) (hf.comp E.subtype_injective) hC hD' hcomm').1
  have hquot : IsPGroup 2 (E ⧸ C) := by
    apply isPGroup_quotient_of_sup_eq_top C (D.subgroupOf E) hD2.comap_subtype
    rw [← Subgroup.subgroupOf_sup hJE hDE, Subgroup.subgroupOf_self]
  have hc' : Nat.card C = 168 :=
    (Nat.card_congr (subgroupOfEquivOfLe hJE).toEquiv).trans hc
  have hrC : primeRank 3 C ≤ 1 := by
    obtain ⟨P,_,hPc⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 3)
    have hd : 3 ^ primeRank 3 C ∣ Nat.card C := hPc ▸ P.card_subgroup_dvd_card
    by_contra hn'
    have h9 : 9 ∣ Nat.card C :=
      (Nat.pow_dvd_pow 3 (show 2 ≤ primeRank 3 C by omega)).trans hd
    norm_num [hc'] at h9
  have hr : primeRank 3 E ≤ 1 :=
    (primeRank_le_of_normal_two_quotient C hquot 3 (by decide)).trans hrC
  have hm' : moved (σ.comp E.subtype) C = ⊤ := by
    change subspaceCommutator (σ.comp E.subtype) ⊤ C = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hJE]
    exact hm
  have hn' : ¬ IsIrrPlus (σ.comp E.subtype) C ⊤ := by
    intro hh
    exact hn ((IsIrrPlus.subgroupOf_iff σ J E hJE ⊤).mp hh)
  obtain ⟨e⟩ := PlusAction.OddFFRows.doubleThree_of_not_irrPlus σ hf hcore
    (cover.subgroup E) hCN hr hm' hc' hn'
  let j := (subgroupOfEquivOfLe hJE).symm
  exact ⟨⟨j.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (j g) v⟩⟩



omit [Finite G] in
theorem simple_component_commutator_of_faithful_two_actor
    {J D : Subgroup G} [J.Normal] [IsSimpleGroup J] [Group.IsPerfect J]
    (hD : D ≠ ⊥) (hc : D ⊓ centralizer (J : Set G) = ⊥) : ⁅J,D⁆ = J := by
  rcases simple_subnormal_commutator_dichotomy J D
      (inferInstance : J.Normal).isSubnormal with hb | he
  · exfalso
    apply hD
    have hle : D ≤ centralizer (J : Set G) := by
      rw [commutator_comm] at hb
      exact commutator_eq_bot_iff_le_centralizer.mp hb
    rw [inf_eq_left.mpr hle] at hc
    exact hc
  · rw [he]
    have hh : (fun x : D => J.map (MulAut.conj (x : G)).toMonoidHom) = fun _ : D => J := by
      funext x
      exact mem_normalizer_iff_map_conj_eq.mp (J.normalizer_eq_top ▸ mem_top (x : G))
    rw [hh]
    exact iSup_const

theorem component_tilde_doubleThree
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]
    (ρ : Representation (ZMod 2) G V)
    (σ₀ : Representation (ZMod 2) G V₀) (hf₀ : Function.Injective σ₀)
    (cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple G)
    {J D : Subgroup G} [J.Normal] [IsSimpleGroup J]
    (hi : IsIrrPlus σ₀ J ⊤) (hJ : IsComponent G J) (hc : Nat.card J = 168)
    (hp : ∀ k : G, (∀ v ∈ subspaceCommutator ρ ⊤ J,ρ k v = v) → k = 1)
    (hn : ¬ IsIrrPlus ρ J (subspaceCommutator ρ ⊤ J))
    (hD : IsBestOffender (subspaceImageRepresentation ρ (subspaceCommutator ρ ⊤ J))
      (restrictedSubgroup ρ (subspaceCommutator ρ ⊤ J) D))
    (hD2 : IsPGroup 2 D) (hDne : D ≠ ⊥)
    (hDC : D ⊓ centralizer (J : Set G) = ⊥) :
    let I := subspaceCommutator ρ ⊤ J
    ∃ hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I,
      Nonempty (ActionEquiv ((wholeSubspaceAction ρ I hs).comp J.subtype)
        (repeated (linearNatural BinaryField.two 3) 2)) := by
  dsimp only
  let I := subspaceCommutator ρ ⊤ J
  have hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) (by rw [J.normalizer_eq_top])
  let τ := wholeSubspaceAction ρ I hs
  have hf := wholeSubspaceAction_faithful ρ I hs hp
  have hDτ := wholeSubspaceAction_bestOffender ρ I hs hp hD
  let : IsQuasisimple J := hJ.2
  let : Group.IsPerfect J := inferInstance
  have hm : moved τ J = ⊤ := by
    apply Submodule.map_injective_of_injective I.subtype_injective
    have hh := subspaceCommutator_map_embedding ρ τ (MonoidHom.id G)
      I.subtype (fun g v => (wholeSubspaceAction_apply ρ I hs g v).symm) J ⊤
    simpa only [Subgroup.map_id,Submodule.map_top,Submodule.range_subtype, I,
      subspaceCommutator_idempotent_of_perfect] using hh.symm
  have hnτ : ¬ IsIrrPlus τ J ⊤ := by
    intro hι
    apply hn
    have hι' : IsIrrPlus τ (J.map (MonoidHom.id G)) ⊤ := by
      simpa only [Subgroup.map_id] using hι
    have hh := IsIrrPlus.map_embedding ρ τ (MonoidHom.id G) I.subtype
      I.subtype_injective (fun g v => (wholeSubspaceAction_apply ρ I hs g v).symm) J ⊤ hι'
    simpa only [Submodule.map_top,Submodule.range_subtype] using hh
  have hcomm := simple_component_commutator_of_faithful_two_actor hDne hDC
  exact ⟨hs,doubleThree_of_component_overgroup τ hf σ₀ hf₀ cover hi hJ hc hD2 hDτ
    hcomm hm hnτ⟩

end CFSG.Quasithin.Chapter13.Section07

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_tilde_component_doubleThree_of_fixed_layer_movement
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (hm : ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),
      K.map H.subtype⁆ ≠ ⊥)
    (hl : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 H))) 3 2) :
    let U := Section08.Source.UH H V₃
    let π := QuotientGroup.mk' (pCore 2 H)
    ∃ hE : IsElementaryAbelian 2 U, letI := hE;
      ∃ (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ V₁.subgroupOf U)))
        (c : BinaryConjugationSection H U V₁ (ρ.comp π)),
        let I := subspaceCommutator ρ ⊤ (K.map π)
        (∀ u : U, (c.coordinates u).toAdd = Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf U) u)) ∧
        ∃ hsI : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ subspaceStabilizer ρ I,
          Nonempty (ActionEquiv ((wholeSubspaceAction ρ I hsI).comp (K.map π).subtype)
            (repeated (linearNatural BinaryField.two 3) 2)) := by
  dsimp only
  obtain ⟨hE,ρ,c,_,hcoord,hpoint,hnot,D,hDle,hD,_,hDimage,_⟩ :=
    source_tilde_component_FF_of_fixed_layer_movement d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm
  let := hE
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  have hnK := source_plus_component_normal d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  let : J.Normal := Subgroup.Normal.map hnK π (QuotientGroup.mk'_surjective _)
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hl
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let eJ := a.trans ((Atlas.fieldEquivPSL 3 f).trans Matrix.PSL3Two.equiv.symm)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup J := eJ.isSimpleGroup
  have hc : Nat.card J = 168 :=
    (Nat.card_congr eJ.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hwhole := source_plus_component_whole d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  rw [hwhole] at hi
  obtain ⟨hUgA,_,_,_⟩ := pair_conjugate_seed_quotient_nontrivial d h hU hV g hs hout
  have hUgT : conjugate (Section08.Source.UH H V₃) (g : G) ≤ (T : Subgroup G) :=
    hUgA.trans inf_le_right |>.trans (h.sylow_centralizer.symm.le.trans inf_le_left)
  have hDS : D ≤ ((T : Subgroup G).subgroupOf H).map π :=
    hDle.trans (map_mono (comap_mono hUgT))
  have hcS := source_plus_sylow_centralizer_eq_bot d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  have hDC : D ⊓ centralizer (J : Set (H ⧸ pCore 2 H)) = ⊥ := by
    apply bot_unique
    rw [← hcS]
    exact inf_le_inf_right _ hDS
  obtain ⟨hsI,e⟩ := component_tilde_doubleThree ρ σ
    (source_plus_faithful_of_kernel_eq σ s hk) (source_plus_sqtk_cover d h)
    hi hK hc hpoint hnot hDimage hD.1.2.isPGroup hD.1.1 hDC
  exact ⟨hE,ρ,c,hcoord,hsI,e⟩

end CFSG.Quasithin.Chapter13.Section07
