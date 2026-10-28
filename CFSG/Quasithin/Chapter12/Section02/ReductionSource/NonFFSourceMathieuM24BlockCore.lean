module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Normalization
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoGeneration

/-!
# The original M24 cocode block core

The actual selected degree-two actor and T-normalization of VA identify
[O₂(LT),L] and [O₂(L),L] with the chosen orbit. The argument adapts the
core-commutator proof of NonFFSourceNonMathieuHermitianFieldFourBlockCore:
it uses actor escape and quasisimple generation, independently of the
selected degree. The genuine M24 multiplier then eliminates the central
covering kernel O₂(L)/V in the literal perfect quotient L/V.

The final application constructs the selected pair from the cocode marking;
no normalization or covering premise remains. Module recognition and ambient
J4 recognition remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher–Smith 8.2.10(3), printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original selected actor and its Sylow-normalized product identify both
actual core commutators. The full core of LT is retained. -/
theorem sourceOrbit_m24_selected_core_commutators
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hTVA : (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G)) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit ∧
      ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  obtain ⟨hAT,hAC,_,hker,_⟩ := selected_core_actor_data s D.sourceOrbit_weakClosure_setup
  have hVQ : D.sourceOrbit ≤ Q := hV ▸ D.le_core
  have hQC : Q ≤ centralizer (D.sourceOrbit : Set G) := hV ▸ D.core_centralizes
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hJQ : J ≤ normalizer (Q : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hQA : ⁅Q,A⁆ ≤ D.sourceOrbit :=
    Chapter8.Section02.Normalizer.core_commutator_le Q D.sourceOrbit A T hVQ hQC
      (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes)
      ((hAT.trans le_sup_right).trans hJQ)
      (hker ▸ inf_le_left) hQT hTVA
  let K := L.subgroupOf J
  let W := D.sourceOrbit.subgroupOf J
  let QJ := Q.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hWJ : D.sourceOrbit ≤ J := hVQ.trans (pCoreIn_le 2 J)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes)
  let : QJ.Normal := normal_subgroupOf_of_le_normalizer hJQ
  let N := centralizerModulo (⊤ : Subgroup J) QJ W
  let : N.Normal := centralizerModulo_top_normal QJ W
  have hAN : A.subgroupOf J ≤ N := by
    intro a ha
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_top _,?_⟩
    intro q hq
    exact hQA (commutator_mem_commutator hq ha)
  have hK : K.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect K := hK.perfect
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let e : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hgen : K ⊔ (P : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  obtain ⟨x,hx,hxC⟩ := SetLike.not_le_iff_exists.mp hAC
  let y : J := ⟨x,mem_sup_right (hAT hx)⟩
  have hyQ : y ∉ pCore 2 J := fun hh => hxC (hQC (mem_map_of_mem J.subtype hh))
  have hNP := normal_sup_eq_top_of_two_escape K N (P : Subgroup J) hK P.isPGroup'
    hgen (pCore_isPGroup.le_sylow_of_normal P) y (hAT hx) (hAN hx) hyQ
  let : Group.IsNilpotent (J ⧸ N) :=
    (isPGroup_quotient_of_sup_eq_top N (P : Subgroup J) P.isPGroup' hNP).isNilpotent
  have hKN := le_of_isPerfect_of_solvable_quotient K N
  have hQL : ⁅Q,L⁆ ≤ D.sourceOrbit := by
    apply commutator_le.mpr
    intro q hq l hl
    exact (mem_centralizerModulo_iff.mp (hKN (show
      (⟨l,mem_sup_left hl⟩ : J) ∈ K from hl))).2
      ⟨q,(pCoreIn_le 2 J) hq⟩ hq
  have hLW : D.sourceOrbit ≤ ⁅L.pCoreIn 2,L⁆ := by
    rw [←hV,D.eq_commutator]
    exact commutator_mono D.le_componentCore le_rfl
  have hLQ : L.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact ⟨le_antisymm hQL (hLW.trans (commutator_mono hLQ le_rfl)),
    le_antisymm ((commutator_mono hLQ le_rfl).trans hQL) hLW⟩

/-- The M24 multiplier removes the full central two-core quotient once
the original core commutator is the chosen orbit. -/
theorem sourceOrbit_m24_core_eq_of_commutator
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hcomm : ⁅L.pCoreIn 2,L⁆ ≤ D.sourceOrbit) :
    D.sourceOrbit = L.pCoreIn 2 := by
  let W := D.sourceOrbit.subgroupOf L
  have hWC : D.sourceOrbit ≤ L.pCoreIn 2 := hV ▸ D.le_componentCore
  have hWL := hWC.trans (pCoreIn_le 2 L)
  let : W.Normal := normal_subgroupOf_of_le_normalizer D.sourceOrbit_component_normalizes
  have hWcore : W ≤ pCore 2 L := by
    have hh := comap_mono (f := L.subtype) hWC
    rw [pCoreIn,comap_map_eq_self_of_injective L.subtype_injective] at hh
    exact hh
  let K := L.subgroupOf (L ⊔ (T : Subgroup G))
  have hK : K.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect K := hK.perfect
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let eZ := (D.orbitCentralQuotientEquiv h).trans hq.some
  have hZ : center (L ⧸ pCore 2 L) = ⊥ :=
    SchurMultipliers.m24_center_eq_bot_of_centralQuotientEquiv eZ
  let e : (L ⧸ pCore 2 L) ≃* M24 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eZ
  let q : (L ⧸ W) →* (L ⧸ pCore 2 L) := QuotientGroup.map W (pCore 2 L)
    (MonoidHom.id L) (by simpa using hWcore)
  have hqsur : Function.Surjective q := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
    exact ⟨QuotientGroup.mk' W x,rfl⟩
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp hqsur
  have hc : f.ker ≤ center (L ⧸ W) := by
    intro x hx
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective W x
    have hl : l ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff l).mp
      apply e.injective
      exact (show e (QuotientGroup.mk' (pCore 2 L) l) = 1 from hx).trans e.map_one.symm
    apply mem_center_iff.mpr
    intro y
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective W y
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hcomm (commutator_mem_commutator (mem_map_of_mem L.subtype hl) k.property)
  let c : PerfectCentralCovering.Cover (L ⧸ W) M24 := {
    toMonoidHom := f
    surjective := hf
    isPerfect := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective W)
    ker_le_center := hc }
  have hinj := (MonoidHom.ker_eq_bot_iff f).mp (SchurMultipliers.m24_cover_kernel_eq_bot c)
  have heq : pCore 2 L = W := le_antisymm (by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply hinj
    change e (QuotientGroup.mk' (pCore 2 L) x) = f 1
    have hxq : QuotientGroup.mk' (pCore 2 L) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq,map_one,map_one]) hWcore
  have hm := congrArg (Subgroup.map L.subtype) heq
  rw [map_subgroupOf_eq_of_le hWL] at hm
  exact hm.symm

/-- The actual normalized cocode pair supplies the full block-core
commutators and proves V=O₂(L), without a cover or normalization premise. -/
theorem sourceOrbit_m24_cocode_block_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit ∧
      ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit ∧ D.sourceOrbit = L.pCoreIn 2 := by
  obtain ⟨g,hg,hAT,rest⟩ := D.sourceOrbit_m24_exists_normalized_pair h hmany hV hq hnon a E hE
  obtain ⟨H,I,i,S,_,_,_,_,s,_,ha,_,_,_,_,_,_,_,_,hVA⟩ := rest
  rw [ha] at hVA
  obtain ⟨hJ,hL⟩ := D.sourceOrbit_m24_selected_core_commutators h.toHypothesis1221 hV s hVA
  exact ⟨hJ,hL,D.sourceOrbit_m24_core_eq_of_commutator h.toHypothesis1221 hV hq hL.le⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
