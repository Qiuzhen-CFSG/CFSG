module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryGeneration
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerReduction
public import CFSG.Quasithin.Chapter4.Section04.OddActorQuotient
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Action

/-!
# The original binary doubled orbit in the odd-normalizer argument

For an odd subgroup A centralizing the whole orbit W, the actual residual
R = C_L(A)^∞ covers L modulo O₂(L) and contains W in O₂(R). Its literal
quotient R/O₂(R) is SL₃(2). The same multiplication coordinates retain
both the chosen seed and its original conjugate, with the natural–dual
action on all of W. The faithful residual action is non-FF and is neither
Fano core under any marking of that full quotient.

The order-64 orbit centralizes O(N_G(A)); that odd core lies in N_G(L).
If R has the original unique maximal overgroup, generalized-Fitting
detection supplies an outside component K with [K,W] = K, retaining its
central cover and the quasithin K-group hypotheses. Failure of uniqueness
instead supplies the actual maximal pushing-up pair, with W in its two-core.
The final theorem applies these alternatives to the original H-star
prime-order witness produced when w > 1, without an added local callback.

Excluding these two ambient configurations is still required for 4.4.3
and hence for w ≤ 1 and the binary Baer–Suzuki endgame. No equality of the
chosen seed with W, or of a commutator subgroup with an entire two-core,
is used. The other doubled rows remain separate obligations of this task.
Source: Aschbacher–Smith 4.4.3–10, printed pp.619–621, and 7.3.4/7.6.1,
printed pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original binary pair marking has the full two-core as its kernel. -/
theorem sourceOrbit_binary_quotient_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* BinaryLinearThree.Group, Function.Surjective q ∧ q.ker = pCore 2 L ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ l v, E (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l v) = NaturalDual.action (q l) (E v)) ∧
        (∀ v, (E v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (E v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨t,ht,hnt,q,hq,E,hE,hV,hVt⟩ := D.sourceOrbit_binary_pair_coordinates h hd F hF hmodel
  obtain ⟨m⟩ := hmodel
  let model := m.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv
  have hseed : (centralizer (V : Set G)).subgroupOf L = pCore 2 L :=
    D.seedComparison.centralizer_eq_twoCore
      (D.seedComparison.projection_injective_of_linearThree h.quasisimple model)
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hQC : L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
    simpa only [D.fundamentalSetup_module,Chapter3.Section02.localJoin,D.localOrbit_eq,
      D.sourceOrbit_eq] using (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module
  have hk : q.ker = pCore 2 L := by
    apply le_antisymm
    · intro l hl
      rw [←hseed]
      intro v hv
      let w : Additive D.sourceOrbit := Additive.ofMul ⟨v,hVW hv⟩
      have hw : doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l w = w := by
        apply E.injective
        rw [hE,show q l = 1 from hl,map_one]
        rfl
      have he : (l : G) * v * (l : G)⁻¹ = v :=
        congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G)) hw
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro l hl
      apply natural_injective
      apply LinearMap.ext
      intro v
      let w := E.symm (v,0)
      have hw : doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l w = w := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change (l : G) * (w.toMul : G) * (l : G)⁻¹ = (w.toMul : G)
        have hc : (w.toMul : G) * (l : G) = (l : G) * (w.toMul : G) :=
          hQC (mem_map_of_mem L.subtype hl) _ w.toMul.property
        exact mul_inv_eq_iff_eq_mul.mpr hc.symm
      have he := hE l w
      rw [hw] at he
      rw [show E w = (v,0) from E.apply_symm_apply _] at he
      have hz := (congrArg Prod.fst he).symm
      change W (q l) v = v at hz
      simpa only [map_one,Module.End.one_apply] using hz
  exact ⟨t,ht,hnt,q,hq,hk,E,hE,hV,hVt⟩

/-- The actual odd fixed residual contains the whole original orbit in its
two-core, and its quotient carries the same two marked summands. -/
theorem sourceOrbit_binary_odd_residual_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    let R := oddActorResidual L A
    (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
    D.sourceOrbit = ⁅D.sourceOrbit,R⁆ ∧ D.sourceOrbit ≤ R.pCoreIn 2 ∧
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* BinaryLinearThree.Group, Function.Surjective q ∧ q.ker = pCore 2 L ∧
      ∃ e : (R ⧸ pCore 2 R) ≃* BinaryLinearThree.Group,
        (∀ r : R, e (QuotientGroup.mk' (pCore 2 R) r) =
          q (inclusion ((oddActorResidual_le L A).trans inf_le_left) r)) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ r v, E (doubledSeedAction R D.sourceOrbit
          (((oddActorResidual_le L A).trans inf_le_left).trans
            D.sourceOrbit_component_normalizes) r v) =
            NaturalDual.action (e (QuotientGroup.mk' (pCore 2 R) r)) (E v)) ∧
        (∀ v, (E v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (E v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  obtain ⟨hc,hm,hcore,_⟩ := D.doubledOrbit_oddActorResidual_cover h A hA ho
  rw [←D.sourceOrbit_eq] at hm hcore
  refine ⟨hc,hm,hcore,?_⟩
  obtain ⟨t,ht,hnt,q,hq,hk,E,hE,hV,hVt⟩ := D.sourceOrbit_binary_quotient_coordinates h hd F hF hmodel
  obtain ⟨f,hf⟩ := chosen_oddActorResidual_quotient h.toHypothesis1221 D A
    (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T)))
  let b : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let e := f.trans b
  have he (r : oddActorResidual L A) : e (QuotientGroup.mk' _ r) =
      q (inclusion ((oddActorResidual_le L A).trans inf_le_left) r) := by
    change b (f (QuotientGroup.mk' _ r)) = _
    rw [hf]
    rfl
  refine ⟨t,ht,hnt,q,hq,hk,e,he,E,?_,hV,hVt⟩
  intro r v
  rw [he]
  exact hE (inclusion ((oddActorResidual_le L A).trans inf_le_left) r) v

/-- Both exceptional module types in the binary-three row of 4.4.3 are
excluded on the whole odd fixed residual, for every marking of its quotient.
This does not assume that the chosen three-space equals its six-space orbit. -/
theorem sourceOrbit_binary_odd_residual_module_exclusions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    let R := oddActorResidual L A
    let ρ := doubledSeedAction R D.sourceOrbit
      (((oddActorResidual_le L A).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
    ¬ IsFFModule (imageRepresentation ρ) ∧
    ∀ b : (R ⧸ pCore 2 R) ≃* BinaryLinearThree.Group,
      (¬ Nonempty (ρ.Equiv (U₂.comp (b.toMonoidHom.comp (QuotientGroup.mk' _))))) ∧
      (¬ Nonempty (ρ.Equiv (FanoDecomposition.lineCoreRepresentation.comp
        (b.toMonoidHom.comp (QuotientGroup.mk' _))))) := by
  obtain ⟨_,_,_,t,ht,hnt,q,hq,hker,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  let R := oddActorResidual L A
  let ρ := doubledSeedAction R D.sourceOrbit
    (((oddActorResidual_le L A).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
  let qR := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hs : Function.Surjective qR := e.surjective.comp (QuotientGroup.mk'_surjective _)
  refine ⟨DoubledBinaryOddAction.not_ff ρ qR E hE,?_⟩
  intro b
  let a : MulAut BinaryLinearThree.Group := e.symm.trans b
  have ha : a.toMonoidHom.comp qR = b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R)) := by
    apply MonoidHom.ext
    intro r
    exact congrArg b (e.symm_apply_apply _)
  have hp := DoubledBinaryOddAction.not_point_core ρ qR E hE hs a
  have hl := DoubledBinaryOddAction.not_line_core ρ qR E hE hs a
  rw [ha] at hp hl
  exact ⟨hp,hl⟩

omit D [Finite G] [_root_.Group G] in
private theorem perfect_twoPerfect {X : Type*} [_root_.Group X] [Finite X]
    [_root_.Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact _root_.Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

/-- Source 4.4.8 on the whole binary orbit: its odd normalizer's odd core
centralizes the orbit and is contained in the original maximal local. -/
theorem sourceOrbit_binary_oddNormalizer_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (A : Set G))).map
      (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      normalizer (L : Set G) := by
  let W := D.sourceOrbit
  let N := normalizer (A : Set G)
  let R := oddActorResidual L A
  have hRN : R ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hWN : W ≤ N := (le_centralizer_iff.mp hAC).trans
    (Subgroup.centralizer_le_normalizer _)
  have hm := (D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho).2.1
  let : _root_.Group.IsPerfect R := oddActorResidual_isPerfect L A
  let : _root_.Group.IsPerfect (R.subgroupOf N) := _root_.Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRN).symm.toMonoidHom) (subgroupOfEquivOfLe hRN).symm.surjective
  have hmN : W.subgroupOf N = ⁅W.subgroupOf N,R.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,map_subgroupOf_eq_of_le hRN]
    exact hm
  have hc : Nat.card W = 64 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_binary_dimension h hd F hF hmodel] at hh
    exact hh
  have hsize : 8 < Nat.card (W.subgroupOf N) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv,hc]
    decide
  let : IsElementaryAbelian 2 (W.subgroupOf N) := IsElementaryAbelian.subgroupOf hWN
  have hh := ChapterA.large_elementary_commutator_centralizes_oddCore
    (h.simpleQTKE.quasithin.subgroup N) (R.subgroupOf N) (W.subgroupOf N)
      perfect_twoPerfect hsize hmN
  have hcomm : ⁅W,(pPrimeCore 2 N).map N.subtype⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hWN,Subgroup.map_bot] using
      congrArg (Subgroup.map N.subtype) hh
  exact ⟨hcomm,(le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
    (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le⟩

/-- In the unique-residual branch, the actual escaping odd normalizer has
an outside component fully moved by the whole orbit. Only quasithinness of
this odd local is used; strong quasithinness is not inferred. -/
theorem sourceOrbit_binary_oddNormalizer_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  let W := D.sourceOrbit
  let N := normalizer (A : Set G)
  let Y := (normalizer (L : Set G)).subgroupOf N
  have hWN : W ≤ N := (le_centralizer_iff.mp hAC).trans
    (Subgroup.centralizer_le_normalizer _)
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hcore : pCore 2 N = ⊥ := (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2
  have hvY : W.subgroupOf N ≤ Y.pCoreIn 2 := by
    apply (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWN,map_pCoreIn_of_injective 2 Y N.subtype N.subtype_injective]
    have hh := D.doubledOrbit_oddNormalizer_intersection_core h A hA ho
    simpa only [Y,subgroupOf_map_subtype,N,←D.sourceOrbit_eq] using hh
  have hvne : W.subgroupOf N ≠ ⊥ := by
    intro hb
    have hh := congrArg (Subgroup.map N.subtype) hb
    rw [map_subgroupOf_eq_of_le hWN,Subgroup.map_bot] at hh
    exact D.sourceOrbit_weakClosure_setup.nontrivial hh
  have hvodd : ⁅W.subgroupOf N,pPrimeCore 2 N⁆ = ⊥ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,Subgroup.map_bot]
    exact (D.sourceOrbit_binary_oddNormalizer_oddCore h hd F hF hmodel A hAC ho).1
  have hp : IsPGroup 2 (W.subgroupOf N) :=
    (IsElementaryAbelian.isPGroup 2 W).comap_subtype
  obtain ⟨K,hK,hm,houtK⟩ := exists_component_moved_outside_of_centralizes_oddCore
    (W.subgroupOf N) Y hp hvne hcore hvodd hvY
  have hout' : ¬ K.map N.subtype ≤ normalizer (L : Set G) :=
    fun he => houtK (map_le_iff_le_comap.mp he)
  have hKcore : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1,hcore,MonoidHom.comap_bot]
    exact K.subtype.ker_eq_bot K.subtype_injective
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK h.simpleQTKE A hne
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨_,hRK,_⟩ := chosen_oddNormalizer_component_normalization h.toHypothesis1221 D
    A (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T))) K hK
  have hWR : W ≤ oddActorResidual L A :=
    (D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho).2.2.1.trans
      (pCoreIn_le 2 _)
  have hWK := (comap_mono (f := N.subtype) hWR).trans hRK
  exact ⟨K,hK,hK.commutator_eq_self_of_normalizes hWK hm,hout',hKcore,hqt.subgroup K,
    hkg.simple_quotient K (center K),hRK,hWK⟩

/-- The original failure of w≤1 produces a genuine pushing-up pair or a
moved component in the same prime-order odd normalizer. Both alternatives
retain the whole orbit and their full two-cores. Their exclusion is the
remaining ambient odd-normalizer argument. -/
theorem sourceOrbit_binary_globalW_or_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ChapterE.globalW D.sourceOrbit T ≤ 1 ∨
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        (∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
          (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
            normalizer (K : Set (normalizer (A : Set G))) ∧
          D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
            normalizer (K : Set (normalizer (A : Set G))))) := by
  rcases D.sourceOrbit_binary_globalW_or_odd_escape h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,_,p,hp,hpo,A,hAH,hAC,hcard,hout⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  have ho : Odd (Nat.card A) := hcard.symm ▸ hpo
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · apply Or.inr
    let : Fact p.Prime := ⟨hp⟩
    let : IsCyclic A := isCyclic_of_prime_card hcard
    have hne : A ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      have := hp.one_lt
      omega
    exact D.sourceOrbit_binary_oddNormalizer_component h hd F hF hmodel A hne hAC ho hu
      (fun he => hout (inf_le_right.trans he))
  · apply Or.inl
    have hA : A ≤ normalizer (L : Set G) ⊓
        centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      rw [←D.sourceOrbit_eq]
      exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
    simpa only [←D.sourceOrbit_eq] using D.doubledOrbit_oddNormalizer_pushingUp h A hA ho hu

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
