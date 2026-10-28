module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
/-!
# Source index and action transport on the chosen flag

The nonsingular normalizer orbit has length ten.  The local odd-index
calculation and the Sylow odd index show that the centralizer of the chosen
vector has index two in the original Sylow subgroup.  Relabelling also
supplies the full normalizer action on the exact chosen flag module.  These
are the literal index and action interfaces needed by 13.6.17--19.

Source: Aschbacher--Smith 13.2.6 and the marking preceding 13.6.5,
printed pp.879,926.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry FlagCoordinates
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

theorem FlagSource.flag_centralizer_index (d : FlagSource T L V V₁ V₂) :
    (Tv (T : Subgroup G) (markedV d.flag.module)).relIndex (T : Subgroup G) = 2 := by
  let N := normalizer (V : Set G)
  let C := N ⊓ Gv (markedV d.flag.module)
  let S := Tv (T : Subgroup G) (markedV d.flag.module)
  have hSC : S ≤ C := inf_le_inf d.T_normalizes le_rfl
  have hCN : C ≤ N := inf_le_left
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hCi : C.relIndex N = 10 := by
    obtain ⟨g,hg⟩ := d.flag_relabel
    change ((normalizer (V : Set G) ⊓ Gv (markedV d.flag.module)).subgroupOf
      (normalizer (V : Set G))).index = 10
    rw [hg]
    change ((normalizer (V : Set G) ⊓
      Gv (d.module.map (Multiplicative.ofAdd (rho g v)))).subgroupOf
        (normalizer (V : Set G))).index = 10
    rw [d.stabilizer_comap,index_comap_of_surjective _ d.normalizerAction.rangeRestrict_surjective]
    apply FlagCoordinates.SylowCalculation.nonsingular_index d.image d.alternating_le_image
    rw [FlagCoordinates.SylowCalculation.form_invariant]
    decide +kernel
  have hoddC : ¬ 2 ∣ S.relIndex C := d.flag_localIndex
  have hoddN : ¬ 2 ∣ (T : Subgroup G).relIndex N := (T.subtype d.T_normalizes).not_dvd_index
  have h₁ := relIndex_mul_relIndex S C N hSC hCN
  have h₂ := relIndex_mul_relIndex S (T : Subgroup G) N hST d.T_normalizes
  rw [hCi] at h₁
  obtain ⟨n,hn⟩ := T.isPGroup'.index (S.subgroupOf (T : Subgroup G))
  change S.relIndex (T : Subgroup G) = 2 ^ n at hn
  have hcop : Nat.Coprime (S.relIndex (T : Subgroup G)) (S.relIndex C) := by
    rw [hn]
    exact ((Nat.prime_two.coprime_iff_not_dvd).mpr hoddC).pow_left n
  have hd : S.relIndex (T : Subgroup G) ∣ 10 := by
    apply hcop.dvd_of_dvd_mul_left
    rw [h₁,←h₂]
    exact dvd_mul_right _ _
  have h5 : Nat.Coprime (S.relIndex (T : Subgroup G)) 5 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 5).pow_left n
  have hd2 : S.relIndex (T : Subgroup G) ∣ 2 := by
    apply h5.dvd_of_dvd_mul_right
    exact hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with he | he
  · have hh : S.relIndex C * 10 = (T : Subgroup G).relIndex N := by
      rw [he,one_mul] at h₂
      exact h₁.trans h₂.symm
    exact False.elim (hoddN (hh ▸ (show 2 ∣ S.relIndex C * 10 from
      dvd_mul_of_dvd_right (by decide) _)))
  · exact he
/-- The chosen flag retains the full original normalizer action. -/
theorem FlagSource.exists_source_on_flag (d : FlagSource T L V V₁ V₂) :
    ∃ D : FlagSource T L V V₁ V₂, D.module = d.flag.module := by
  obtain ⟨g,hg⟩ := d.flag_relabel
  exact ⟨d.relabel g,hg.symm⟩

/-- Retain the literal chosen module as the defining field of the transported source. -/
@[expose] noncomputable def FlagSource.sourceOnFlag (d : FlagSource T L V V₁ V₂) :
    FlagSource T L V V₁ V₂ := by
  let D := d.exists_source_on_flag.choose
  have hD : D.module = d.flag.module := d.exists_source_on_flag.choose_spec
  exact { D with
    module := d.flag.module
    action_kernel := by rw [←hD]; exact D.action_kernel
    normalizer_equivariant := by rw [←hD]; exact D.normalizer_equivariant
    action_agrees := by rw [←hD]; exact D.action_agrees }

@[simp] theorem FlagSource.sourceOnFlag_module (d : FlagSource T L V V₁ V₂) :
    d.sourceOnFlag.module = d.flag.module := rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
