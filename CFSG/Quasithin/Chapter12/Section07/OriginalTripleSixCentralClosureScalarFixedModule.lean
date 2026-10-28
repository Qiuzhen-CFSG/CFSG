module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureCoreScalarSplitting
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The actual secondary module in the original scalar-fixed core

The full fixed factor C=C_{O₂(KT)}(X) is normalized by KT. If the core
exceeds the chosen module U, C is nontrivial and has a nonzero intersection
Z with Ω₁Z(T). The literal K-span V of Z is a reduced elementary module,
is disjoint from U, and remains in C. Its join with the whole chosen U is
also reduced. The original almost-special W has quadratic action on V:
[V,W,W] lies both in V and in the original line ⟨z⟩≤U.

Source: the secondary module in Aschbacher--Smith12.7.20, printed p.846.
The preceding scalar proof retains N=(W∩Wᵍ)U; this construction neither
changes that denominator nor drops the fixed factor from the whole core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Construct the original secondary reduced module, with its nonzero
Sylow-central seed whenever the full core exceeds U, and prove the actual
quadratic W-action on that same module. -/
theorem original_tripleSix_central_closure_scalar_fixed_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let Q := M.pCoreIn 2
    let C := Q ⊓ centralizer (X : Set G)
    let Z := C ⊓ omegaCenterIn (T : Subgroup G)
    let V := conjugateSpanBy Z K
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    M ≤ normalizer (C : Set G) ∧
      (Q ≠ U → Z ≠ ⊥ ∧ V ≠ ⊥) ∧ V ≤ C ∧
      V = conjugateSpanBy Z M ∧ IsPReduced 2 (V.subgroupOf M) ∧
      IsPReduced 2 ((U ⊔ V).subgroupOf M) ∧ Disjoint U V ∧ ⁅⁅V,W⁆,W⁆ = ⊥ := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let Q := M.pCoreIn 2
  let C := Q ⊓ centralizer (X : Set G)
  let Z := C ⊓ omegaCenterIn (T : Subgroup G)
  let V := conjugateSpanBy Z K
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  have hMQ : M ≤ normalizer (Q : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hMX : M ≤ normalizer (X : Set G) :=
    (sup_le K.le_normalizer D.sylow_normalizes_component).trans
      (tripleSixScalarResidual_normalizer_at K)
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf hMQ (hMX.trans (normalizer_le_normalizer_centralizer X))).trans
      inf_normalizer_le_normalizer_inf
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow M (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from le_sup_right)] at hh
  obtain ⟨_,hsplit,hdis⟩ := original_tripleSix_central_closure_core_scalar_splitting
    h structural D a z hz hzT hnot houter
  change Q=U ⊔ C at hsplit
  change Disjoint U C at hdis
  have hne (hq : Q ≠ U) : Z ≠ ⊥ ∧ V ≠ ⊥ := by
    have hC : C ≠ ⊥ := by
      intro he
      apply hq
      simpa only [he,sup_bot_eq] using hsplit
    have hZ : Z ≠ ⊥ := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
      C T (inf_le_left.trans hQT) T.isPGroup' (le_sup_right.trans hMC) hC
    exact ⟨hZ,fun he => hZ (bot_unique ((le_conjugateSpanBy Z K).trans_eq he))⟩
  have hZC : Z ≤ centralizer (T : Set G) :=
    fun x hx => ((mem_omegaCenterIn_iff T x).mp hx.2).2.1
  have hZT : Z ≤ (T : Subgroup G) := inf_le_left.trans (inf_le_left.trans hQT)
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)
  have hVe : V=conjugateSpanBy Z M :=
    (conjugateSpanBy_sup_of_normalizes_seed Z K T hTZ D.sylow_normalizes_component).symm
  have hVC : V ≤ C := conjugateSpanBy_le inf_le_left (le_sup_left.trans hMC)
  have hVM : V ≤ M := hVC.trans (inf_le_left.trans (pCoreIn_le 2 M))
  have hUM : U ≤ M := D.le_component.trans le_sup_left
  have hQne : Q ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_core.trans_eq he))
  have hMchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h.simpleQTKE.evenCharacteristic T) ⟨hQne,show (T : Subgroup G) ≤ M from le_sup_right⟩)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le
    (show Z ≤ omegaCenterIn (T : Subgroup G) from inf_le_right)
  have hred : IsPReduced 2 (V.subgroupOf M) := by
    rw [hVe]
    exact reduced_conjugateSpan_of_sylow_central T M Z le_sup_right hZT hZC hMchar
  have hjoin : IsPReduced 2 ((U ⊔ V).subgroupOf M) := by
    rw [subgroupOf_sup hUM hVM]
    exact ((structural K h).2.2 U D).2.1.sup hred
  have hUV : Disjoint U V := hdis.mono_right hVC
  have hMV : M ≤ normalizer (V : Set G) := by
    rw [hVe]
    exact le_normalizer_conjugateSpanBy Z M
  have hWT : W ≤ (T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot).1
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    have he := hc.2.1
    change W = _ at he
    rw [he]
    exact le_sup_right.trans (le_normalizer_conjugateSpanBy _ _)
  have hVW : ⁅V,W⁆ ≤ W := le_normalizer_iff_commutator_le_right.mp
    (hVC.trans (inf_le_left.trans (hQT.trans hTW)))
  have hWV : W ≤ normalizer (V : Set G) := hWT.trans (le_sup_right.trans hMV)
  have hder : ⁅W,W⁆ ≤ zpowers (z:G) :=
    derived_le_of_frattini_image_le (T.isPGroup'.to_le hWT) hc.2.2.2.1
  have hquad : ⁅⁅V,W⁆,W⁆=⊥ := by
    apply bot_unique
    apply le_trans _ hUV.symm.eq_bot.le
    apply le_inf
    · exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp hWV) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hWV)
    · exact ((commutator_mono hVW le_rfl).trans hder).trans (zpowers_le.mpr z.property)
  exact ⟨hMC,hne,hVC,hVe,hred,hjoin,hUV,hquad⟩

end CFSG.Quasithin.Chapter12.Section07
