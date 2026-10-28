module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Algebra
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Containment
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Faithfulness

/-!
# Two-core vanishing for every moving invariant local component

Assume the contrary and normalize the nontrivial two-core. The checked
index-two component theorem gives the unique containing C-component K₂.
Characteristic two and movement of z put K₂ in the actual faithful family.
Hypothesis 13.3.1(4) now identifies its actual two-core quotient with A₅.
Minimal nonsolvability and the index-two arrangement force K₂ = K₀.
The uniform choice clause transfers to K₂ before the earlier centralizer
result is applied, contradicting the nonidentity element v in C_T(K₂).

This proves 13.6.16(1), conditional on the full earlier A.3.9(1), the
normalization output of 13.3.2(2), and the C_T consequence of 13.6.3(2)
for valid replacement choices. The section assembly owner must discharge
these earlier inputs under genuine Hypothesis 13.3.1 and the Section 13.6
counterexample assumption. Assertions (2) and (3) are separate obligations.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.930.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Hypothesis 13.3.1(4), with its implication and universal quantifier
unchanged. The quotient is the intrinsic two-core quotient of each actual
member of L_f(G,T). -/
def UniformA5Choice (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ K ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))

omit [Finite G] in
/-- The nonambient clause of Hypothesis 13.3.1 is preserved when replacing
L by a member of the faithful family in the A₅ branch. The simple-QTKE and
excluded-model clauses concern only G and T and do not change. -/
theorem uniformA5Choice_replacement (T : Sylow 2 G) (L K : Subgroup G)
    (hchoice : UniformA5Choice T L)
    (hL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    UniformA5Choice T K := fun _ => hchoice hL

/-- Assertion (1) of 13.6.16 from the genuine ambient QTKE setup and
explicit earlier results. `hnormal` is 13.3.2(2); `hcentralizer` is the
C_T(L)=1 consequence of 13.6.3(2), universally available when the chosen
member satisfies the A₅ branch and the unchanged uniform-A₅ clause.

No assertion of 13.6.8–16 is an input. The containing component, its
faithfulness, its A₅ quotient, the validity of the replacement choice,
and its equality with K₀ are all established before the contradiction. -/
theorem twoCore_eq_bot_of_earlier_source {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (T : Sylow 2 G) (L : Subgroup G)
    (_hL : L ∈ MainForward.faithfulLocalComponents T)
    (hA5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hchoice : UniformA5Choice T L)
    (hnormal : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hcentralizer : ∀ K ∈ MainForward.faithfulLocalComponents T,
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      UniformA5Choice T K → (T : Subgroup G) ⊓ centralizer (K : Set G) = ⊥)
    (z v : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1)
    (_hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (K₀ : Subgroup G)
    (hK₀ : K₀ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hR : Tv (T : Subgroup G) v ≤ normalizer (K₀ : Set G))
    (hmoving : ¬ K₀ ≤ centralizer ({z} : Set G)) :
    (K₀ ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ := by
  by_contra hcore
  obtain ⟨K₂, hK₂, hle, hlocal, _⟩ :=
    containing_component_of_twoCore_ne_bot hA39 hG T v K₀ hK₀ hidx hcore
  let H := K₀ ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let N := normalizer (Q : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hNM : N ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨Q, hcore, isPGroup_pCoreIn 2 H, rfl⟩,
      fun x hx => hHN ((show (T : Subgroup G) ≤ H from le_sup_right) hx)⟩
  have hfaithful : K₂ ∈ MainForward.faithfulLocalComponents T :=
    faithful_of_moving_cComponent T (hG.evenCharacteristic T) z hz N K₂ hNM hK₂
      (fun hc => hmoving (hle.trans hc))
  have hmodel := hchoice hA5 K₂ hfaithful
  have hreplace := uniformA5Choice_replacement T L K₂ hchoice hA5
  obtain ⟨e⟩ := hmodel
  let := Chapter1.mem_L_isPerfect hlocal
  have he : K₂ = K₀ := eq_of_a5_quotient_of_index_two T
    (Tv (T : Subgroup G) v) K₀ K₂ inf_le_left hidx hK₀.2 hR hle
    (hnormal K₂ hfaithful) e
  have hc := hcentralizer K₂ hfaithful ⟨e⟩ hreplace
  have hvC : v ∈ centralizer (K₂ : Set G) := by
    apply mem_centralizer_iff.mpr
    intro k hk
    have hh := hK₀.1 (he ▸ hk)
    exact mem_centralizer_singleton_iff.mp hh
  exact hv (mem_bot.mp (hc ▸ (show v ∈ (T : Subgroup G) ⊓ centralizer (K₂ : Set G)
    from ⟨hvT, hvC⟩)))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
