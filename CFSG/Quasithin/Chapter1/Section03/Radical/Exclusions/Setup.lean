module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Defs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Global
public import CFSG.Quasithin.ChapterC.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The radical exclusion configuration and its pushing-up setup

The inputs below are the intermediate results supplied by the structure and
characteristic-normalizer arguments in the proof of 1.3.8. In particular,
maximality means maximal **two-local** subgroup, and every normalizer and
Frattini action is taken on the indicated actual subgroup.

A.4.2(7) makes R = O₂(XT) a globally maximal X-signalizer. Restricting this
maximality proves R = O₂(N_H(R)); restricting the section-centralizer Sylow
condition proves that R is Sylow in its normal closure under H ∩ M.
Characteristic normalizers transport through the actual subgroup equivalence.
These deductions construct the hypotheses of C.2.3, without assuming a block
or an exclusion of any model. The full exclusion still requires the model
comparison in C.2.7 and the commuting-block argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.513–514; A.4.2(7), p.57;
Hypothesis C.2.3, p.144.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open XiEmbedding ChapterA.Section04

universe u
variable {G : Type u} [Group G]

/-- The genuine intermediate inputs of the radical argument. No noncontainment,
embedding alternative, or block decomposition occurs among the fields. -/
structure Configuration (p : ℕ) (T X P L₀ M : Subgroup G) : Prop where
  prime : p.Prime
  odd : Odd p
  large : 3 < p
  xi : X ∈ Xi G T
  radical : X = XiP p L₀
  maximal_local : L₀ ∈ LStar G T
  quotient : XiOddQuotient p (XiQuotient X)
  sylow : IsSylowIn p P X
  automizer_not_cyclic : ¬ IsCyclic (automizer T P)
  irreducible : ∀ A : Subgroup (P ⧸ frattini P),
    (∀ s : (L₀ ⊓ normalizer P : Subgroup G), ∀ a ∈ A,
      frattiniConjugationAction (L₀ ⊓ normalizer P) P inf_le_right s a ∈ A) →
    A = ⊥ ∨ A = ⊤
  normalizer_local : M = normalizer L₀
  normalizer_radical : M = normalizer X
  maximal_twoLocal : IsMaximalTwoLocal M
  characteristic_control : ((X ⊔ T).pCoreIn 2).characteristicNormalizerClosure ≤ M

/-- The intrinsic 1.3.4 implication, retaining its necessary Sylow premise.
This is an earlier-source theorem parameter, not an asserted theorem. -/
def Source134 (κ : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∀ (p : ℕ) (T X P H₀ : Subgroup G), IsSQTK κ H₀ →
    LocalInput p T X P H₀ → IsSylowIn 2 T H₀ → Conclusion p T X P H₀

/-- Exactly the hypotheses of C.2.3, in ambient-subgroup notation.
The normal closure is formed inside M₀, not inside H₀ or G. -/
structure PushingUpSetup (κ : GroupClass.{u}) (H₀ R M₀ : Subgroup G) : Prop where
  sqtk : IsSQTK κ H₀
  radical_le : R ≤ H₀
  overgroup_le : M₀ ≤ H₀
  radical : IsPRadical 2 (R.subgroupOf H₀)
  characteristic_control : (R.subgroupOf H₀).characteristicNormalizerClosure ≤ M₀.subgroupOf H₀
  sylow : IsSylowIn 2 R ((normalClosure (R.subgroupOf M₀ : Set M₀)).map M₀.subtype)

/-- The two branches left after p > 3 and noncyclicity of Aut_T(P). -/
def SurvivingAlternatives (p : ℕ) (T P K : Subgroup G) : Prop :=
  Nonempty (P ≃* Plane p) ∧
    ((SwappedFactors T P K ∧ SwappedModel p (XiQuotient K)) ∨
      (T ≤ normalizer K ∧ LinearThreeModel p (XiQuotient K)))

/-- Eliminate the exceptional-prime and cyclic-automizer branches, retaining
both the swapped rank-one and the invariant linear-three possibilities. -/
theorem surviving_alternatives {p : ℕ} {T P K : Subgroup G}
    (hp : 3 < p) (hcyc : ¬ IsCyclic (automizer T P))
    (h : Alternatives p T P K) : SurvivingAlternatives p T P K := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hs | ⟨hn, hl | hs | he⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hn, hl⟩
  · exact (hcyc hs.2).elim
  · omega

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply (a (e y))

private theorem characteristic_control_restrict {R H₀ M : Subgroup G}
    (hRH : R ≤ H₀) (hcontrol : R.characteristicNormalizerClosure ≤ M) :
    (R.subgroupOf H₀).characteristicNormalizerClosure ≤ (H₀ ⊓ M).subgroupOf H₀ := by
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hC hne
  let e := subgroupOfEquivOfLe hRH
  let D := C.map e.toMonoidHom
  let _ := hC
  let _ : D.Characteristic := characteristic_map_equiv e C
  have hD : D ≠ ⊥ := by
    intro he
    exact hne ((C.map_eq_bot_iff_of_injective e.injective).mp he)
  have he : (C.map (R.subgroupOf H₀).subtype).map H₀.subtype = D.map R.subtype := by
    rw [map_map, map_map]
    rfl
  intro g hg
  have hgN : (g : G) ∈ normalizer (D.map R.subtype : Set G) := by
    rw [← he]
    exact (C.map (R.subgroupOf H₀).subtype).le_normalizer_map H₀.subtype
      (mem_map.mpr ⟨g, hg, rfl⟩)
  exact ⟨g.property, hcontrol (normalizer_le_characteristicNormalizerClosure R D hD hgN)⟩

private theorem normalClosure_le_sectionCentralizer {X R M₀ M : Subgroup G}
    (hM₀M : M₀ ≤ M) (hMX : M ≤ normalizer X)
    (hRC : R ≤ twoSectionCentralizer X M) :
    (normalClosure (R.subgroupOf M₀ : Set M₀)).map M₀.subtype ≤
      twoSectionCentralizer X M := by
  let C := twoSectionCentralizer X M
  let _ : (C.subgroupOf M₀).Normal := normal_subgroupOf_of_le_normalizer
    (hM₀M.trans (twoSectionCentralizer_normalized X M hMX))
  exact (map_le_iff_le_comap).mpr (normalClosure_le_normal (N := C.subgroupOf M₀)
    (fun _ hr => hRC hr))

private theorem radical_restrict_of_maximal_signalizer {X R H₀ : Subgroup G}
    (hne : R ≠ ⊥) (hXH : X ≤ H₀) (hRH : R ≤ H₀)
    (hR : IsMaximalTwoSignalizer X ⊤ R) : IsPRadical 2 (R.subgroupOf H₀) := by
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp hR
  let N := H₀ ⊓ normalizer (R : Set G)
  have hXN : X ≤ N := le_inf hXH hm.1.normalizes
  have hRN : R ≤ N := le_inf hRH le_normalizer
  have hRB : R ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes hm.1.isPGroup hRN inf_le_right
  have hBN : X ≤ normalizer (N.pCoreIn 2 : Set G) := hXN.trans
    (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  have hBR : N.pCoreIn 2 ≤ R := hm.2 _
    ((isTwoSignalizer_iff _ _ _).mpr ⟨le_top, isPGroup_pCoreIn 2 N, hBN⟩) hRB
  have he : N.pCoreIn 2 = R := le_antisymm hBR hRB
  refine ⟨?_, ?_⟩
  · intro hb
    apply hne
    simpa only [map_subgroupOf_eq_of_le hRH, Subgroup.map_bot] using
      congrArg (map H₀.subtype) hb
  · apply map_injective H₀.subtype_injective
    change ((normalizer (R.subgroupOf H₀ : Set H₀)).pCoreIn 2).map H₀.subtype = _
    rw [map_pCoreIn_of_injective 2 _ H₀.subtype H₀.subtype_injective,
      ← subgroupOf_normalizer_eq hRH, subgroupOf_map_subtype]
    simpa only [inf_comm, map_subgroupOf_eq_of_le hRH] using he

/-- Construct C.2.3 in H ∩ M from the actual radical normalizer control.
A.4.2(7) is used as a proved theorem, with every relative Sylow condition
and every normal-closure inclusion supplied explicitly. -/
theorem pushingUp_setup [Finite G] {κ : GroupClass.{u}}
    {T X H₀ M : Subgroup G} (hX : X ∈ Xi G T)
    (hT : IsSylowIn 2 T M) (hXM : X ≤ M) (hMX : M ≤ normalizer X)
    (hXH : X ⊔ T ≤ H₀) (hH : IsSQTK κ H₀)
    (hcontrol : ((X ⊔ T).pCoreIn 2).characteristicNormalizerClosure ≤ M) :
    PushingUpSetup κ H₀ ((X ⊔ T).pCoreIn 2) (H₀ ⊓ M) := by
  let R := (X ⊔ T).pCoreIn 2
  have hne : R ≠ ⊥ := hX.join_mem_H
  have hRM : R ≤ M := (pCoreIn_le 2 (X ⊔ T)).trans
    (sup_le hXM (isSylowIn_iff.mp hT).2.1)
  have hRH : R ≤ H₀ := (pCoreIn_le 2 (X ⊔ T)).trans hXH
  have hNR : normalizer (R : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure_self R hne).trans hcontrol
  obtain ⟨S, hS⟩ := hT
  have hc := normal_sylow_core_conclusions X M hXM hMX hX.perfect S
    (by simpa only [hS] using hNR)
  simp only [hS] at hc
  have hmax : IsMaximalTwoSignalizer X ⊤ R := hc.2.2.1
  have hlocal := (isMaximalTwoSignalizer_iff _ _ _).mp hc.2.2.2.1
  have hn : (X.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMX
  have hRC := signalizer_le_twoSectionCentralizer X M R hXM hn.isSubnormal hX.perfect hlocal.1
  have hsyl : IsSylowIn 2 R (twoSectionCentralizer X M) :=
    (maximal_signalizer_iff_sylow X M R hXM hn.isSubnormal hX.perfect).mp hc.2.2.2.1
  refine ⟨hH, hRH, inf_le_left,
    radical_restrict_of_maximal_signalizer hne (le_sup_left.trans hXH) hRH hmax,
    characteristic_control_restrict hRH hcontrol, ?_⟩
  apply hsyl.restrict
  · have hr := map_mono (f := (H₀ ⊓ M).subtype)
      (le_normalClosure (H := R.subgroupOf (H₀ ⊓ M)))
    simpa only [map_subgroupOf_eq_of_le (le_inf hRH hRM)] using hr
  · exact normalClosure_le_sectionCentralizer inf_le_right hMX hRC

/-- The ambient Sylow subgroup restricts to M = N_G(X), so the actual
configuration supplies every input to the preceding construction. -/
theorem Configuration.pushingUp_setup [Finite G] {κ : GroupClass.{u}}
    (T : Sylow 2 G) {p : ℕ} {X P L₀ M H₀ : Subgroup G}
    (h : Configuration p T X P L₀ M) (hH : IsSQTK κ H₀)
    (hXH : X ⊔ (T : Subgroup G) ≤ H₀) :
    PushingUpSetup κ H₀ ((X ⊔ (T : Subgroup G)).pCoreIn 2) (H₀ ⊓ M) := by
  have hTM : (T : Subgroup G) ≤ M := h.normalizer_radical ▸ h.xi.invariant
  have hXM : X ≤ M := h.normalizer_radical ▸ X.le_normalizer
  have hs : IsSylowIn 2 (T : Subgroup G) M :=
    ⟨T.subtype hTM, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]⟩
  exact RadicalExclusions.pushingUp_setup h.xi hs hXM h.normalizer_radical.le
    hXH hH h.characteristic_control

/-- The simple QTKE hypotheses give SQTK for a subgroup with nontrivial
two-core, by embedding it into the normalizer of that core. -/
theorem sqtk_of_mem_H [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) {H₀ : Subgroup G} (hH : H₀ ∈ H G) : IsSQTK κ H₀ := by
  let R := H₀.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H₀ ≤ N := H₀.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H₀ (pCore 2 H₀))
  have hN : IsTwoLocal N := ⟨R, hH, isPGroup_pCoreIn 2 H₀, rfl⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((hG.twoLocal_sqtk hN).subgroup (H₀.subgroupOf N))

/-- A C-component of an H-overgroup of T has F* = O₂, using the genuine
global 1.1.4(6) bridge and inheritance by subnormal subgroups. -/
theorem component_fitting_of_global_He [Finite G] {T H₀ K : Subgroup G}
    (h114 : HOver G (T : Set G) ⊆ He G) (hH : H₀ ∈ HOver G (T : Set G))
    (hK : K ∈ cComponentsIn H₀) : generalizedFitting K = pCore 2 K := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hK.1)).mp
    (subnormal_core_selfCentralizing (mem_He_iff.mp (h114 hH)) _ hK.2.subnormal)

/-- An overgroup outside N_G(X) cannot be the normal alternative of 1.3.4. -/
theorem embedding_outside_normalizer [Finite G] {κ : GroupClass.{u}}
    (h134 : Source134 κ G) {p : ℕ} {T X P L₀ M H₀ : Subgroup G}
    (h : Configuration p T X P L₀ M) (hH : IsSQTK κ H₀)
    (hT : IsSylowIn 2 T H₀) (hXH : X ⊔ T ≤ H₀) (hout : ¬ H₀ ≤ M) :
    ∃ K : Subgroup G, K ∈ cComponentsIn H₀ ∧ IsQuasisimple (XiQuotient K) ∧
      X ≤ componentOrbit K T ∧ SurvivingAlternatives p T P K := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨S, hS⟩ := h.sylow
  have hinput : LocalInput p T X P H₀ := by
    simpa only [hS] using localInput_of_mem_Xi h.xi hT hXH h.odd h.quotient S
  rcases h134 p T X P H₀ hH hinput hT with hn | ⟨K, hK, hq, hXK, ha⟩
  · exact (hout (h.normalizer_radical ▸
      (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hXH)).mp hn)).elim
  · exact ⟨K, hK, hq, hXK, surviving_alternatives h.large h.automizer_not_cyclic ha⟩

end CFSG.Quasithin.Chapter1.RadicalExclusions
