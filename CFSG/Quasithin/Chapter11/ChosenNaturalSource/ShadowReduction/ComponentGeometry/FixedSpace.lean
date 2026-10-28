module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.Reductions
public import Theory.GroupTheory.PGroup.OmegaCenterDetection

/-!
# Fixed vectors and escaping point centralizers in §11.4

A nonzero fixed subgroup C_V(L) meets the Sylow omega-center. If an outside
H-star subgroup centralized that omega-center, the intersection would give a
nontrivial two-subgroup whose centralizer contains LT and H. Nonsolvable
uniqueness rules this out. Source 11.0.3(3) and the full 11.3.2 implication
then force C_V(L) = 1. Neither fixed-space vanishing nor an H-star witness
is assumed in that conclusion.

The same 11.3.2 implication forces C_G(z) outside M for a source central
involution z in V1. These results retain the original chosen quotient and
M = N_G(L). The preceding SL3 fixed-space fact and Proposition 11.3.2
remain explicit inputs, owned by the preceding geometry and shadow tasks.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.4.1(1) and the paragraph following 11.4.2, printed pp.776--777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)

include D S

private theorem normalizer_le_of_central_seed (P : Subgroup G)
    (hP : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hc : L ⊔ (T : Subgroup G) ≤ centralizer (P : Set G)) :
    normalizer (P : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (P : Set G)) from ⟨P, hne, hP, rfl⟩)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have he := hu.normalizer_unique M hM
    ((hc.trans (Subgroup.centralizer_le_normalizer _)).trans hNM)
  have horb : componentOrbit L (T : Subgroup G) = L := D.localOrbit_eq
  rw [horb] at he
  exact he ▸ hNM

/-- Every outside H-star moves the Sylow omega-center when the original
chosen module has nonzero fixed space. No §11.4 conclusion is used. -/
theorem omega_moves_of_fixed_nontrivial {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    ⁅omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype), H⁆ ≠ ⊥ := by
  let C := V ⊓ centralizer (L : Set G)
  let Z := omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S.sylow_normalizes (D.sylow_normalizes_component.trans
      (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _)))).trans
      inf_normalizer_le_normalizer_inf
  have hneP : Z ⊓ C ≠ ⊥ := fun he => hne
    (eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G) C
      T.isPGroup' (inf_le_left.trans D.le_sylow) hTC he)
  have hZT : Z ≤ centralizer (T : Set G) := by
    rintro z hz t ht
    obtain ⟨c, hc, rfl⟩ := omegaOneAmbient_le _ hz
    exact congrArg (T : Subgroup G).subtype (mem_center_iff.mp hc ⟨t, ht⟩)
  have hCP : L ⊔ (T : Subgroup G) ≤ centralizer ((Z ⊓ C : Subgroup G) : Set G) := by
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans inf_le_right))
      (le_centralizer_iff.mp (inf_le_left.trans hZT))
  let := D.elementary
  have hP : IsPGroup 2 (Z ⊓ C : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (inf_le_right.trans inf_le_left)
  have hN := normalizer_le_of_central_seed D S (Z ⊓ C) hP hneP hCP
  intro hzH
  apply hH.1.2
  have hcH : H ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzH)
  exact (hcH.trans (centralizer_le inf_le_left)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)

/-- The standing multiple-overgroup hypothesis supplies the actual outside
minimal local subgroup used in 11.4.1, rather than an assumed witness. -/
theorem exists_outside :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hm := hu.normalizer_maximal
  have horb : componentOrbit L (T : Subgroup G) = L := D.localOrbit_eq
  rw [horb] at hm
  exact Chapter3.exists_HStar_of_hasMaximalOutside
    (S.outside_of_many _ hm D.sylow_normalizes_component)

/-- Source 11.4.1(1), conditional only on its genuine earlier SL3 fact and
the complete implication 11.3.2 on the original quotient-line preimage. -/
theorem fixed_trivial
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ H, Hypothesis1131At D S U₁ H → Proposition1132At D S U₁ H) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨H, hH⟩ := exists_outside D S
  have hyp : Hypothesis1131At D S U₁ H :=
    ⟨hH, omega_moves_of_fixed_nontrivial D S hH hne,
      fun hsl => (hne (hlinear hsl)).elim⟩
  exact hne (h1132 H hyp).fixed_trivial

/-- The centralizer of a source central involution cannot be contained in M.
This is the escape assertion preceding 11.4.3; it does not assume Kz = K. -/
theorem point_centralizer_outside
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient) (z : G)
    (hz : z ∈ D.centralQuotientPreimage U₁)
    (hzZ : z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype))
    (h1132 : ∀ H, Hypothesis1131At D S U₁ H → Proposition1132At D S U₁ H) :
    ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  intro hc
  obtain ⟨H, hH⟩ := exists_outside D S
  have hline : centralizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (L : Set G) :=
    (centralizer_le (Set.singleton_subset_iff.mpr hz)).trans hc
  have hmove :
      ⁅omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype), H⁆ ≠ ⊥ := by
    intro he
    apply hH.1.2
    apply le_trans ?_ hc
    intro h hh
    have hzh := (commutator_eq_bot_iff_le_centralizer.mp he hzZ) h hh
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hzh.symm
  exact (h1132 H ⟨hH, hmove, fun _ => hline⟩).centralizer_outside hline

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
