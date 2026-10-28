module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoreAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2ThompsonBorel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveSylowFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Excluding the moving blocks on the original doubled orbit

For a natural rank-one block, its Borel normalizes the Thompson subgroup
of the original core, hence lies in the control group and preserves W.
A core element exchanging the block with a commuting conjugate fixes W
pointwise. Borel displacement on W consequently lies in the other block
and centralizes the first. Two-perfect commutator idempotence kills that
displacement, and pointwise Borel rigidity makes the whole block centralize W.

For the deleted A₅ block, restrict the core to the component normalizer.
Its full Sylow intersection and the original residual supplement reduce
to the proved one-dimensional Sylow-fixed-space calculation. The full
central kernel is retained in both arguments.

NonFFSourceDoubledBinaryCoreNormalization supplies these inputs on the
actual chosen doubled orbit, proving source 7.7.8. Ambient containment and
the final non-FF assembly remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, 7.7.8–9, printed pp.707–708, and C.1.9;
the natural-block argument uses Borel rigidity in place of odd normalizer escape.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMovingBlocks
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_mover_centralizes (W C B : Subgroup G)
    (hW : IsPGroup 2 W) (hB : IsPPerfect 2 B)
    (hBC : B ≤ C) (hBW : B ≤ normalizer (W : Set G))
    (hWC : W ≤ normalizer (C : Set G)) (a : G)
    (ha : a ∈ centralizer (W : Set G))
    (hcomm : C.map (MulAut.conj a).toMonoidHom ≤ centralizer (C : Set G)) :
    W ≤ centralizer (B : Set G) := by
  have hCW : ⁅W,B⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hBW
  have hCC : ⁅W,B⁆ ≤ C := (commutator_mono le_rfl hBC).trans
    (le_normalizer_iff_commutator_le_right.mp hWC)
  have hfix (x : G) (hx : x ∈ ⁅W,B⁆) : a*x*a⁻¹=x := by
    rw [←ha x (hCW hx),mul_inv_cancel_right]
  have hconj : ⁅W,B⁆ ≤ C.map (MulAut.conj a).toMonoidHom := by
    intro x hx
    exact ⟨x,hCC hx,hfix x hx⟩
  have hcent : ⁅W,B⁆ ≤ centralizer (B : Set G) :=
    hconj.trans (hcomm.trans (centralizer_le hBC))
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←commutator_isPPerfect_idempotent B W hB hW hBW]
  exact commutator_eq_bot_iff_le_centralizer.mpr hcent

/-- A moving natural block is incompatible with a core-central orbit
whose normalizer contains the original characteristic-normalizer control. -/
theorem natural_block_normalized
    (Q M W C : Subgroup G) (hq : IsPRadical 2 Q)
    (hc : HasCharacteristicTwo G) (hcontrol : Q.characteristicNormalizerClosure ≤ M)
    (hC : C.IsCComponent) [IsQuasisimple (C ⧸ pCore 2 C)]
    (hout : ¬ C ≤ M) {n : ℕ} (hb : ChapterC.IsL2EvenBlock C n)
    (P : Sylow 2 C) (hPQ : (P : Subgroup C).map C.subtype ≤ Q)
    (hW : IsPGroup 2 W) (hWC : W ≤ normalizer (C : Set G))
    (hWQ : W ≤ centralizer (Q : Set G))
    (hMW : M ≤ normalizer (W : Set G))
    (hWM : centralizer (W : Set G) ≤ M) : Q ≤ normalizer (C : Set G) := by
  by_contra hn
  obtain ⟨a,ha,han⟩ := Set.not_subset.mp hn
  have hne : C ≠ C.map (MulAut.conj a).toMonoidHom := by
    intro he
    exact han (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hblock : ChapterC.IsBlock C := ⟨inferInstance,hb.2.1,hC.subnormal⟩
  have hcomm := hblock.commutator_eq_bot_of_quasisimple_quotient
    (hblock.map_equiv (MulAut.conj a)) inferInstance hne
  have hJN := ChapterC.Section02Source.thompson_le_component_normalizer_of_characteristicTwo
    Q M C hq hc hcontrol hout hC
  have hBN := hb.borel_normalizes_thompson C Q hq.isPGroup P hPQ hJN
  have hBM : (normalizer (P : Set C)).map C.subtype ≤ M :=
    hBN.trans ((normalizer_maxJ_le_characteristicNormalizerClosure Q Q
      (sSup_le fun _ hA => hA.1) le_rfl
      (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q hq.isPGroup hq.1)).trans hcontrol)
  let B := (normalizer (P : Set C)).map C.subtype
  have hpB : IsPPerfect 2 B := (hb.borel_twoPerfect P).of_surjective
    (C.subtype.subgroupMap (normalizer (P : Set C)))
    (C.subtype.subgroupMap_surjective _)
  have hWB : W ≤ centralizer (B : Set G) := fixed_mover_centralizes W C B hW hpB
    (map_subtype_le _) (hBM.trans hMW) hWC a (le_centralizer_iff.mp hWQ ha)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
  have hCW : C ≤ centralizer (W : Set G) := by
    apply le_centralizer_iff.mp
    intro w hw c hcC
    let α : MulAut C := C.normalizerMonoidHom ⟨w,hWC hw⟩
    have hα : α = 1 := hb.borel_fixer P α (by
      intro x hx
      apply Subtype.ext
      change w*(x:G)*w⁻¹=(x:G)
      rw [←hWB hw x (mem_map_of_mem C.subtype hx),mul_inv_cancel_right])
    have he := congrArg (fun f : MulAut C => ((f ⟨c,hcC⟩ : C) : G)) hα
    change w*c*w⁻¹=c at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact hout (hCW.trans hWM)

/-- The deleted A₅ block is excluded by the original residual supplement
and its one-dimensional Sylow-fixed space. -/
theorem alternating_five_no_escape
    (Q M W C A U : Subgroup G) (hq : IsPRadical 2 Q)
    (hC : C.IsCComponent) [IsQuasisimple (C ⧸ pCore 2 C)]
    (hout : ¬ C ≤ M) (hb : ChapterC.IsAlternatingBlock C 5)
    (P : Sylow 2 C) (hPQ : (P : Subgroup C).map C.subtype ≤ Q)
    (hWcore : W ≤ pCore 2 G)
    (hWcent : W ≤ centralizer (Q : Set G))
    (hAQ : A ≤ normalizer (Q : Set G)) (hAC : A ≤ normalizer (C : Set G))
    (hUC : U ≤ centralizer (C : Set G)) (hsup : U ⊔ ⁅W,A⁆ = W)
    (hWM : centralizer (W : Set G) ≤ M) : False := by
  let R := Q ⊓ normalizer (C : Set G)
  let J := C ⊔ R
  have hcoreQ : pCore 2 G ≤ Q := pCore_le_of_pCore_normalizer_le Q hq.isPGroup hq.2.le
  have hcoreR : pCore 2 G ≤ R := le_inf hcoreQ (hC.pCore_le_normalizer 2)
  have hPR : (P : Subgroup C).map C.subtype ≤ R :=
    le_inf hPQ ((map_subtype_le _).trans C.le_normalizer)
  obtain ⟨S,hS⟩ := hC.full_sylow_join (hq.isPGroup.to_le inf_le_left) hcoreR P hPR
  have hSyl : Chapter1.IsSylowIn 2 R J := ⟨S,by rw [hS,map_subgroupOf_eq_of_le le_sup_right]⟩
  have hWR : W ≤ R := hWcore.trans hcoreR
  have hWJ : W ≤ J := hWR.trans le_sup_right
  have hcoreJ : (pCore 2 G).subgroupOf J ≤ pCore 2 J :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  have hWJcore : W ≤ J.pCoreIn 2 := by
    intro w hw
    exact ⟨⟨w,hWJ hw⟩,hcoreJ (hWcore hw),rfl⟩
  have hAR : A ≤ normalizer (R : Set G) :=
    (le_inf hAQ (hAC.trans (normalizer (C : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hcomm : ⁅W,A⁆ ≤ centralizer (C : Set G) :=
    ChapterC.IsAlternatingBlock.commutator_le_centralizer_of_sylow_fixed C R A W hb
      inf_le_right hAC hAR hSyl hWJcore (hWcent.trans (centralizer_le inf_le_left))
  have hWC : W ≤ centralizer (C : Set G) := by
    rw [←hsup]
    exact sup_le hUC hcomm
  exact hout ((le_centralizer_iff.mp hWC).trans hWM)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMovingBlocks
