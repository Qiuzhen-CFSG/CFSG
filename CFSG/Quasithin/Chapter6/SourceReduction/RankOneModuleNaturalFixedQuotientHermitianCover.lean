module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusFirstCohomology
public import Theory.Representation.FirstCohomologyConjugationSplitting
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# A Hermitian moved layer exhausts the fixed-free original module

The model uses the literal quotient L/O₂(L) and the original subgroup
[W,L]. Reducedness makes its quotient kernel centralize W. Every
conjugation displacement in W lies in [W,L], so the proved vanishing of
Hermitian first cohomology gives W=[W,L] C_W(L). When C_W(L)=1, the
original module equals its moved layer and retains the same model.

Source: Aschbacher--Smith 5.1.3, final paragraph, printed p.631,
using I.1.6(3), printed p.408; refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
  {T : Sylow 2 G} {L W : Subgroup G} {n s : ℕ} [NeZero s]

attribute [local instance] SL2.BinarySmall.spaceBinaryModule

private theorem hermitian_H1 : Subsingleton (H1 (SL2.BinarySmall.hermitian s)) := by
  let := binaryPSL2Action_H1_subsingleton s
  let E := @H1Congr (ZMod 2) _ _ (Space s) (Space s) _ _ _ _
    (SL2.BinarySmall.spaceBinaryModule s) _ AddSubgroupClass.instZModModule
    (SL2.BinarySmall.hermitian s) (binaryPSL2Action s)
    (sl2EquivPSL2 s) (@AddEquiv.toLinearEquiv (ZMod 2) _ _ _ _ _
      (SL2.BinarySmall.spaceBinaryModule s) AddSubgroupClass.instZModModule
      (AddEquiv.refl (Space s))
      (@ZMod.map_smul 2 _ _ _ _ _ _ _ (SL2.BinarySmall.spaceBinaryModule s)
        AddSubgroupClass.instZModModule (AddEquiv.refl (Space s)))) (by
      intro g v
      change action s g v = binaryPSL2Action s (sl2EquivPSL2 s g) v
      exact (binaryPSL2Action_mk_apply s g v).symm)
  exact E.injective.subsingleton

private theorem core_centralizes_original
    (h : Input κ T L W n) :
    L.pCoreIn 2 ≤ centralizer (W : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf J
  let U := W.subgroupOf J
  let := h.reduced.2.1
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  obtain ⟨hU,hcore⟩ := h.reduced.2.2
  let : U.Normal := hU
  have hr : IsPReduced 2 U :=
    ⟨hU,IsElementaryAbelian.subgroupOf h.reduced.1,hcore⟩
  let e : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  have hm : (pCore 2 B).map B.subtype ≤ pCore 2 J :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map B.subtype⟩
  rintro x ⟨l,hl,rfl⟩ w hw
  have hb : e.symm l ∈ pCore 2 B := by
    have he := pCore_map_iso 2 e
    rw [←he] at hl
    exact (mem_map_equiv).mp hl
  have hbc : (e.symm l : J) ∈ centralizer (U : Set J) :=
    le_centralizer_iff.mp hr.le_centralizer_pCore
      (hm (mem_map_of_mem B.subtype hb))
  exact congrArg J.subtype (hbc ⟨w,h.reduced.1 hw⟩ hw)

/-- The original fixed-free module is its actual Hermitian moved layer.
The quotient action and its vanishing first cohomology are constructed
from the supplied full model, with no extension or cohomology premise. -/
theorem Input.eq_layer_of_hermitian_layer
    (h : Input κ T L W n)
    (hc : W ⊓ centralizer (L : Set G) = ⊥)
    (hm : IsConjugationModel L (layer L W) (SL2.BinarySmall.hermitian s)) :
    W = layer L W := by
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hLW : L ≤ normalizer (W : Set G) :=
    le_sup_left.trans (reduced_normalizes h.reduced)
  have hDW : layer L W ≤ W := le_normalizer_iff_commutator_le_left.mp hLW
  let := hermitian_H1 (s := s)
  have he := sup_centralizer_eq_of_conjugation_H1 L W (layer L W) hDW q hq
    (SL2.BinarySmall.hermitian s) f (by
      intro l v
      have hh := hf l (f.symm (Multiplicative.ofAdd v))
      simpa only [q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        f.apply_symm_apply,toAdd_ofAdd] using hh) (by
      intro l hl
      have hk : l ∈ pCore 2 L := by
        apply (QuotientGroup.eq_one_iff l).mp
        apply e.injective
        exact hl.trans e.map_one.symm
      exact core_centralizes_original h (mem_map_of_mem L.subtype hk)) (by
      intro l w
      change (l : G) * (w : G) * (l : G)⁻¹ * (w : G)⁻¹ ∈ ⁅W,L⁆
      rw [commutator_comm]
      exact commutator_mem_commutator l.property w.property)
  rw [hc,sup_bot_eq] at he
  exact he.symm

/-- The same Hermitian quotient marking describes the whole original
module once its fixed subgroup is trivial. -/
theorem Input.hermitian_model_of_layer
    (h : Input κ T L W n)
    (hc : W ⊓ centralizer (L : Set G) = ⊥)
    (hm : IsConjugationModel L (layer L W) (SL2.BinarySmall.hermitian s)) :
    IsConjugationModel L W (SL2.BinarySmall.hermitian s) := by
  exact (h.eq_layer_of_hermitian_layer hc hm).symm ▸ hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
