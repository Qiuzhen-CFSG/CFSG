module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceSelectedBlockCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeFiveAction
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeSelectedCover

/-!
# The original selected M₂₂-code block core

On the unchanged selected degree-one pair, the earlier T-normalization of
VA identifies the actual core commutators and the full component-action
kernel. The whole-code automizer marking retains the original quintet map
and its complete native affine image. Mutual normalization puts the literal
[A,R] in A ∩ R. The selected kernel A ∩ C(V) = U lies in V, so the full
central-double-cover comparison removes O₂(L)/V.

The only retained earlier normalization premise is T-normalization of VA,
from 8.2.9(2). No local cover, native image, or kernel premise remains.
Source: Aschbacher--Smith 8.2.10(1,3), printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The actual selected M22-code pair supplies both block commutators,
the entire component-map kernel, and V = O₂(L), retaining only 8.2.9(2). -/
theorem sourceOrbit_m22_code_selected_block_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hA : offenderNormalizer D.sourceOrbit i.val⁻¹ =
      D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)
    (hAT : offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T)
    (hfix : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hker : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) =
      offenderNormalizer D.sourceOrbit i.val⁻¹ ⊓ centralizer (D.sourceOrbit : Set G))
    (hcent : I ≤ centralizer ((D.sourceOrbit ⊓ centralizer
      (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) : Subgroup G) : Set G))
    (hfour : rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) = 4)
    (hfive : rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)) = 5)
    (hcomm : let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
      ⁅localResidual L U,centralizer (U : Set G)⁆ ≤ (localResidual L U).pCoreIn 2)
    (hRP : localResidual L (D.sourceOrbit ⊓ centralizer
      (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) ≤ normalizer (I.pCoreIn 2 : Set G))
    (hTVA : (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
      offenderNormalizer D.sourceOrbit i.val⁻¹ : Subgroup G) : Set G)) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit ∧
      ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit ∧
      D.orbitComponentHom.ker = pCore 2 L ∧ D.sourceOrbit = L.pCoreIn 2 := by
  have hTVA' := hTVA
  rw [hA] at hTVA'
  have hbase := @sourceOrbit_selected_block_core G _ _ T L V D h hmany hV hnon H I i S 1 s hTVA'
  rcases hbase with ⟨hJ,hL,hkernel⟩
  have hfivefull := @sourceOrbit_m22_code_five_section_full G _ _ T L V D
    h.toHypothesis1221 d H I i S s hA hAT hfix hfour hfive
  rcases hfivefull with ⟨f,hfk,hs,hfull,p,q,F,hp,hqsur,hqker,hF,hpA,hq,hval⟩
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let U := W ⊓ centralizer (A : Set G)
  let R := localResidual L U
  have hRL : R ≤ L := (localResidual_le L U).trans inf_le_left
  have hRV : R ≤ normalizer (W : Set G) := hRL.trans D.sourceOrbit_component_normalizes
  have hIR : I ≤ normalizer (R : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono le_rfl hcent).trans hcomm).trans (pCoreIn_le 2 R))
  have hAI : A ≤ I := by
    rw [show A = W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 from hA]
    exact inf_le_right.trans (pCoreIn_le 2 I)
  have hRA : R ≤ normalizer (A : Set G) := by
    have he : R.map (MulAut.conj i.val⁻¹).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hIR (I.inv_mem i.property))
    have hRiV : R ≤ normalizer (W.map (MulAut.conj i.val⁻¹).toMonoidHom : Set G) := by
      rw [←map_equiv_normalizer_eq W (MulAut.conj i.val⁻¹)]
      simpa only [he] using map_mono (f := (MulAut.conj i.val⁻¹).toMonoidHom) hRV
    rw [show A = W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 from hA]
    exact (le_inf hRiV hRP).trans inf_normalizer_le_normalizer_inf
  let K := L.subgroupOf (L ⊔ (T : Subgroup G))
  let : Group.IsPerfect K := h.maximal_faithful.1.1.1.perfect
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  have hWC : D.sourceOrbit ≤ L.pCoreIn 2 := hV ▸ D.le_componentCore
  have hcore : W = L.pCoreIn 2 := marked_pair_core_eq W L A R
    D.sourceOrbit_component_normalizes (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes)
    hRL (hAI.trans hIR) hRA (hker ▸ inf_le_left) hWC hL.le
    p hp hpA q hqsur (hqker.trans hkernel) hq
    (f.comp (inclusion (localResidual_le L U))) hfull
    (fun r => hval (inclusion (localResidual_le L U) r))
  exact ⟨hJ,hL,hkernel,hcore⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
