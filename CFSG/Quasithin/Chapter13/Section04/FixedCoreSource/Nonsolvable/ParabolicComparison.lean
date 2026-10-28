module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ParabolicInterval
public import Theory.SpecificGroups.PSL3Two.Parabolics.TwoKernel

/-!
# Parabolic uniqueness and fixed residuals in the nonsolvable branch

Lift the actual PSL₃(2) Sylow-overgroup lattice through N→N/O₂(N).
If N escapes M while a proper overgroup of T lies inside M, the other
parabolic is the unique member of H*(T,M) inside N. It is solvable,
generates N with the inside parabolic, and intersects it in exactly T.
This constructs the parabolic in the linear-three centralizer row and
supplies generation and uniqueness in the Thompson-normalizer comparison.

The marked module proves both fixed lines, and condition (E) proves the
required characteristic-two bound. The final comparison applies these
facts to the existing normalizer obstruction. The residual calculations
use O²(P) with its literal embedding and the actual Sylow supplement;
they prove the fixed-line and index-two premises on V∩Ω₁Z(T).

The component and model constructions in 13.4.10, equality of the full
Ω₁Z(T) with this seed, and the two 13.4.7 alternatives remain obligations
of qt-d-1341-nonsolvable-source. These conditional applications do not
establish the full nonsolvable contradiction. Earlier local inputs retain
final discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, 13.4.10(7–8) and 13.4.12, pp.909–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Construct the unique outside parabolic from the literal linear-three quotient and inside Sylow overgroup. -/
theorem linear_three_unique_outside
    (T : Sylow 2 G) (M N A : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hN : N ∈ Chapter1.HOver G (T : Set G)) (hNM : ¬ N ≤ M)
    (hTA : (T : Subgroup G) < A) (hAN : A < N) (hAM : A ≤ M)
    (e : (N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) M ∧ P < N ∧
      Group.IsSolvable P ∧ A ⊔ P = N ∧ A ⊓ P = (T : Subgroup G) ∧
      (∀ U ∈ Chapter3.HStar (T : Subgroup G) M, U ≤ N → U = P) := by
  let S := T.subtype hN.2
  let f : N →* Matrix.PSL3Two.PSL :=
    (e.trans Matrix.PSL3Two.equiv).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hf : Function.Surjective f :=
    (e.trans Matrix.PSL3Two.equiv).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 N := by
    ext x
    change (e.trans Matrix.PSL3Two.equiv) (QuotientGroup.mk' (pCore 2 N) x) = 1 ↔ _
    rw [(e.trans Matrix.PSL3Two.equiv).map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hk : IsPGroup 2 f.ker := hker ▸ pCore_isPGroup
  exact unique_outside_of_sylow_pair T M N A hTM hN hNM hTA hAN hAM
    (Matrix.PSL3Two.two_kernel_parabolics S f hf hk)

open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- In the linear-three centralizer row, construct its unique outside parabolic
and its literal fixed line. The proper inside parabolic and quotient marking
are the remaining 13.4.10 inputs, supplied by this source owner. -/
theorem linear_three_centralizer_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (A : Subgroup G) (hTA : (T : Subgroup G) < A)
    (hAC : A < centralizer ({z.val} : Set G)) (hAM : A ≤ normalizer (L : Set G))
    (e : (centralizer ({z.val} : Set G) ⧸ pCore 2 (centralizer ({z.val} : Set G))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ChapterB.IsMinimalParabolicOver T P ∧
      P < centralizer ({z.val} : Set G) ∧ Group.IsSolvable P ∧
      A ⊔ P = centralizer ({z.val} : Set G) ∧
      A ⊓ P = (T : Subgroup G) ∧
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
        centralizer (P : Set G) = zpowers z.val ∧
      (∀ U ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        U ≤ centralizer ({z.val} : Set G) → U = P) := by
  obtain ⟨P, hP, hPC, hs, hgen, hi, hu⟩ := linear_three_unique_outside T _ _ A
    D.sylow_normalizes_component
    (Solvable.centralizer_mem_HOver hzT (fun he => hz1 (Subtype.ext he)))
    hzout hTA hAC hAM e
  exact ⟨P, hP, Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component hP
      (Or.inl hNT), hPC, hs, hgen, hi,
    m.central_four_fixed_of_escape h structural z hz1 hzT P hPC.le hP.1.2, hu⟩

/-- Apply the comparison obstruction after deriving both fixed lines,
characteristic two, generation and uniqueness in the actual Thompson
normalizer. The remaining model recognition, solvability of the four-choice
parabolic and the two 13.4.7 alternatives remain explicit source obligations. -/
theorem false_of_linear_three_join
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (L₂ P₂ P₄ : Subgroup G) (hL₂ : L₂ ≤ L)
    (z w : V) (hz : m.weight z = 2) (hw : m.weight w = 4)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hP₂ : P₂ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP₄ : P₄ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP₂z : P₂ ≤ centralizer ({z.val} : Set G))
    (hP₄w : P₄ ≤ centralizer ({w.val} : Set G))
    (hP₂N : P₂ ≤ thompsonNormalizer T)
    (hTA : (T : Subgroup G) < L₂ ⊔ (T : Subgroup G))
    (hAN : L₂ ⊔ (T : Subgroup G) < thompsonNormalizer T)
    (hmax : IsMaximalTwoLocal (thompsonNormalizer T))
    (e : (thompsonNormalizer T ⧸ pCore 2 (thompsonNormalizer T)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hsolv : Group.IsSolvable P₄)
    (hfour : L₂ ⊔ (T : Subgroup G) ≤ normalizer ((pResidual 2 P₄).map P₄.subtype : Set G) ∨
      (L₂ ⊔ (T : Subgroup G)) ⊔ P₄ ≤ thompsonNormalizer T)
    (hpair : (pResidual 2 P₂).map P₂.subtype ≤
        normalizer ((pResidual 2 P₄).map P₄.subtype : Set G) ∨
      P₂ ⊔ P₄ ≤ thompsonNormalizer T) : False := by
  have hN : thompsonNormalizer T ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hmax.1, hTA.le.trans hAN.le⟩
  obtain ⟨P, _, _, _, hgen, _, hu⟩ := linear_three_unique_outside T _ _
    (L₂ ⊔ (T : Subgroup G)) D.sylow_normalizes_component hN
    (fun hh => hP₂.1.2 (hP₂N.trans hh)) hTA hAN
    (sup_le (hL₂.trans L.le_normalizer) D.sylow_normalizes_component) e
  have he : P₂ = P := hu P₂ hP₂ hP₂N
  have hz1 : z ≠ 1 := by intro he; rw [he, m.weight_one] at hz; omega
  have hw1 : w ≠ 1 := by intro he; rw [he, m.weight_one] at hw; omega
  let C : ParabolicComparison T (normalizer (L : Set G)) L₂
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) z.val w.val := {
    two := P₂
    four := P₄
    two_mem := hP₂
    four_mem := hP₄
    two_fixed := m.central_four_fixed_of_escape h structural z hz1 hzT P₂ hP₂z hP₂.1.2
    four_fixed := m.central_four_fixed_of_escape h structural w hw1 hwT P₄ hP₄w hP₄.1.2
    four_solvable := hsolv
    four_characteristic := Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hP₄.1.1)
    maximal := hmax
    quotient := e
    generation := by simpa only [he] using hgen
    unique_parabolic := fun U hU hUN => (hu U hU hUN).trans he.symm
    four_alternatives := hfour
    pair_alternatives := hpair }
  exact C.false_of_weights m L₂ z w hz hw

/-- The literal two-residual fixes the same central line as its Sylow
supplement. This supplies C_Z(K_i), not just C_Z(H_i), in 13.4.7. -/
theorem escaping_residual_fixed_line
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (P : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G)) :
    (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer ((pResidual 2 P).map P.subtype : Set G) = zpowers z.val := by
  rw [← m.central_four_fixed_of_escape h structural z hz1 hzT P hPz hP.1.2]
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (map_subtype_le _)))
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hTP : (T : Subgroup G) ≤ P := hP.1.1.2
  have hs : (pResidual 2 P).map P.subtype ⊔ (T : Subgroup G) = P :=
    embedded_pResidual_sup_of_common_sylow P T (T.subtype hTP)
      (map_subgroupOf_eq_of_le hTP)
  have hc : P ≤ centralizer ({x} : Set G) := by
    rw [← hs]
    refine sup_le (fun r hr => mem_centralizer_singleton_iff.mpr (hx.2 r hr)) ?_
    exact fun t ht => mem_centralizer_singleton_iff.mpr
      (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx.1.2).2.2 t ht)
  exact fun p hp => mem_centralizer_singleton_iff.mp (hc hp)

/-- The fixed subgroup of the actual residual has index two in V∩Ω₁Z(T).
Identifying this seed with full Ω₁Z(T) remains the source 13.4.10(5) step. -/
theorem escaping_residual_fixed_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (P : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G)) :
    ((V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer ((pResidual 2 P).map P.subtype : Set G)).relIndex
        (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2 := by
  rw [escaping_residual_fixed_line h structural m z hz1 hzT P hP hPz]
  have hle : zpowers z.val ≤ V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    zpowers_le.mpr ⟨z.property, hzT⟩
  have hc : Nat.card (zpowers z.val) = 2 := by
    rw [Nat.card_zpowers]
    let := D.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
      (fun he => hz1 (Subtype.ext he))
  have hm : Nat.card (zpowers z.val) * (zpowers z.val).relIndex
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) =
        Nat.card (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact ((zpowers z.val).subgroupOf
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))).card_mul_index
  rw [hc, m.central_four_card_eq_four h structural z hz1 hzT
    (fun hh => hP.1.2 (hPz.trans hh))] at hm
  omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
