module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.NaturalSubmodule
public import CFSG.Quasithin.Chapter3.Section02.ThompsonCommutator
public import Theory.GroupTheory.Commutator.FullActorNormalLayer

/-!
# Full component generation and centralization modulo the original V

The literal V_K is T-normalized and has order q², while C_{V_K}(V)=V₁
has order q. It therefore moves V. The FSU actor theorem applied to the
unchanged chosen module gives L=[L,V_K]. Inside LT, both O₂(LT) and V
are normal; transfer of centralization from [O₂(LT),V_K]≤V₁≤V gives
[O₂(LT),L]≤V. The chosen full commutator yields equality, and restriction
to O₂(L) gives [O₂(L),L]=V, the literal block module.

The counterexample application discharges all local generation premises.
Only the preceding 11.3.7 action, flag and Cartan inputs remain explicit,
with final discharge owned by qt-d-1222-shadow-common-core. This retains
q=4 and makes no covering-kernel or complement assumption.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774, third paragraph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

include D S in
/-- A T-normalized subgroup moving the original V generates the full L commutator. -/
theorem component_commutator_of_moving_sylow_subgroup (W : Subgroup G)
    (hWT : W ≤ (T : Subgroup G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hmoves : ¬ W ≤ centralizer (V : Set G)) : L = ⁅L,W⁆ := by
  let E := D.fundamentalSetup S.source.toHypothesis1221
  let M := Chapter3.Section02.localJoin T L
  let X := (Chapter3.Section02.localOrbit T L).subgroupOf M
  let R : Sylow 2 M := T.subtype le_sup_right
  let J := W.subgroupOf M
  let ρ := ReducedNormal.representation M
  let U := orbitSpan ρ ⊤ E.seedSpace
  let f := invariantActionHom ρ U
    (orbitSpan_invariant ρ ⊤ E.seedSpace)
  have hWM : W ≤ M := by
    change W ≤ Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G)
    exact hWT.trans le_sup_right
  have hjmap : J.map M.subtype = W := map_subgroupOf_eq_of_le hWM
  have hJT : J ≤ (R : Subgroup M) := fun _ hx => hWT hx
  have hTJ : (R : Subgroup M) ≤ normalizer (J : Set M) := by
    apply le_normalizer_iff.mpr
    intro t ht w hw
    exact le_normalizer_iff.mp hTW (t : G) ht (w : G) hw
  have hjker : ¬ J ≤ f.ker := by
    intro hj
    apply hmoves
    rw [←hjmap]
    rintro _ ⟨g,hg,rfl⟩ v hv
    have hv' : v ∈ E.moduleSubgroup := by
      rwa [S.unchanged_seed]
    rw [←E.local_orbitImage_eq_module] at hv'
    obtain ⟨_,⟨w,hw,rfl⟩,rfl⟩ := hv'
    have hfix := hj hg
    rw [invariantActionHom_ker] at hfix
    have he := congrArg (fun z : Additive (ReducedNormal.ModuleGroup M) => z.toMul.val.val)
      (hfix.2 (Additive.ofMul w) hw)
    change (g : G) * w.val.val * (g : G)⁻¹ = w.val.val at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hgen : X ⊔ (R : Subgroup M) = ⊤ := by
    change (Chapter3.Section02.localOrbit T L).subgroupOf M ⊔
      (T : Subgroup G).subgroupOf M = ⊤
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have he := (E.local_internal_module hu).actor_eq_commutator_of_moving_twoGroup
    hgen hJT hTJ hjker
  have hm := congrArg (map M.subtype) he
  change X.map M.subtype = (⁅X,J⁆).map M.subtype at hm
  rw [map_commutator,map_subgroupOf_eq_of_le le_sup_left,hjmap,D.localOrbit_eq] at hm
  exact hm

include D S in
theorem core_commutator_of_moving_sylow_subgroup (W : Subgroup G)
    (hWT : W ≤ (T : Subgroup G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hmoves : ¬ W ≤ centralizer (V : Set G))
    (hbound : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,W⁆ ≤ V) :
    L = ⁅L,W⁆ ∧ ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = V ∧
      ⁅L.pCoreIn 2,L⁆ = V := by
  have hfull := component_commutator_of_moving_sylow_subgroup (D := D) (S := S) W hWT hTW hmoves
  let M := L ⊔ (T : Subgroup G)
  let Q := M.pCoreIn 2
  have hWM : W ≤ M := hWT.trans le_sup_right
  have hQM : Q ≤ M := pCoreIn_le 2 M
  have hVM : V ≤ M := D.le_core.trans hQM
  have hMQ : M ≤ normalizer (Q : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 M))
  let : (Q.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMQ
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes S.sylow_normalizes)
  have hb : ⁅Q.subgroupOf M,W.subgroupOf M⁆ ≤ V.subgroupOf M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    simpa only [map_commutator,map_subgroupOf_eq_of_le hQM,
      map_subgroupOf_eq_of_le hWM,map_subgroupOf_eq_of_le hVM] using hbound
  have hf : ⁅L.subgroupOf M,W.subgroupOf M⁆ = L.subgroupOf M := by
    apply map_injective M.subtype_injective
    simpa only [map_commutator,map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left),
      map_subgroupOf_eq_of_le hWM] using hfull.symm
  have hm := map_mono (f := M.subtype) (commutator_le_of_full_actor
    (Q.subgroupOf M) (L.subgroupOf M) (W.subgroupOf M) (V.subgroupOf M) hb hf)
  have hQL : ⁅Q,L⁆ ≤ V := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hQM,
      map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left),
      map_subgroupOf_eq_of_le hVM] using hm
  have hLQ : L.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact ⟨hfull,le_antisymm hQL
    (D.eq_commutator.le.trans (commutator_mono D.le_core le_rfl)),
    le_antisymm ((commutator_mono hLQ le_rfl).trans hQL)
      (D.eq_commutator.le.trans (commutator_mono D.le_componentCore le_rfl))⟩

open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {H : Subgroup G} {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

theorem source_pair_core_centralization
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    L = ⁅L,pairNaturalSpan T V H h⁆ ∧
      ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = V ∧ ⁅L.pCoreIn 2,L⁆ = V := by
  obtain ⟨hW,hWP,hWO,hWe,hcard,hrank,hfix,hint,hcomm,hmarked⟩ :=
    source_pair_natural_span a f hu s p hc hh hm hfixed hf hnot hmodel R hR cK
      A X hA hHall hX hAX
  have hWT := hWO.trans (source_omegaClosure_le_sylow s)
  have hTW : (T : Subgroup G) ≤ normalizer (pairNaturalSpan T V H h : Set G) :=
    s.outside.1.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hmove : ¬ pairNaturalSpan T V H h ≤ centralizer (V : Set G) := by
    intro hz
    have he : pairNaturalSpan T V H h = f.Vi 0 := by
      rwa [inf_eq_left.mpr hz] at hfix
    have hline : Nat.card (f.Vi 0) = Nat.card S.field.Carrier :=
      source_flag_line_card (.sl3 a) f rfl hfixed
    rw [he,hline,S.field.card_eq] at hcard
    have hq : 1 < 2 ^ S.field.degree := one_lt_pow₀ (by decide) (by
      have hn := S.nonbinary
      omega)
    nlinarith
  exact core_commutator_of_moving_sylow_subgroup (D := D) (S := S) _ hWT hTW hmove
    (hcomm.trans (D.centralQuotientPreimage_le _))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
