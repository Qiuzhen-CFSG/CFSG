module

public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOmega
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreCenter

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreDerivedOmega`.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}
/-- The actual ambient omega image of the derived normalizer core is F. -/
public theorem normalizer_core_derived_omega_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    (omega₁ (commutator X) (p := 2)).map
      (X.subtype.comp (commutator X).subtype) = d.F := by
  intro N X
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let W := (omega₁ (commutator X) (p := 2)).map
    (X.subtype.comp (commutator X).subtype)
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator_of_local_inputs h hlocal hproper
  have htZ : t ∈ (center (pCore 2 N)).map (N.subtype.comp (pCore 2 N).subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hXC := d.normalizer_core_eq_sylow_centralizer_of_local_inputs h hlocal hproper t htZ htz
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← hXC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  have hbounds : E ⊓ d.F ≤ W ∧ W ≤ E ⊔ d.F := by
    exact (congrArg (fun Y : Subgroup G =>
      E ⊓ d.F ≤ (omega₁ (commutator Y) (p := 2)).map
        (Y.subtype.comp (commutator Y).subtype) ∧
      (omega₁ (commutator Y) (p := 2)).map
        (Y.subtype.comp (commutator Y).subtype) ≤ E ⊔ d.F) hXC).mpr
      (d.derived_t_omega_bounds h t ht.1 htz hCcard)
  have hNX : N ≤ normalizer (X : Set G) := by
    have hh := le_normalizer_map (H := pCore 2 N) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hNW : N ≤ normalizer (W : Set G) := by
    let O := omega₁ (commutator X) (p := 2)
    let : O.Characteristic := omega₁_characteristic (commutator X)
    have hh := normalizer_le_normalizer_characteristic_image X
      (O.map (commutator X).subtype)
    rw [map_map] at hh
    exact hNX.trans hh
  have hnot : ¬ N ≤ H := by
    intro hNH
    apply hproper.ne
    apply le_antisymm hproper.le
    rw [← d.normalizer_inf_centralizer h]
    exact le_inf le_rfl hNH
  have hjoin : normalizer ((E ⊔ d.F : Subgroup G) : Set G) ≤ H :=
    normalizer_le_centralizer_of_characteristic_involution (E ⊔ d.F)
      (commutator (E ⊔ d.F : Subgroup G)) z h.involution
      (d.elementary_join_commutator h)
  rcases d.omega_image_cases_of_bounds h (commutator X)
      (X.subtype.comp (commutator X).subtype) hbounds.1 hbounds.2 with he | hf | hj | hc
  · change W = E at he
    rw [he] at hNW
    exact (hnot (hNW.trans (hlocal.derived_normalizer).le)).elim
  · exact hf
  · change W = E ⊔ d.F at hj
    rw [hj] at hNW
    exact (hnot (hNW.trans hjoin)).elim
  · exact (hnot (hNW.trans ((normalizer_le_normalizer_centralizer W).trans
      (hc ▸ hjoin)))).elim

/-- The second elementary subgroup lies in the actual derived core. -/
public theorem elementary_le_normalizer_core_derived_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    d.F ≤ (commutator X).map X.subtype := by
  intro N X
  rw [← d.normalizer_core_derived_omega_of_local_inputs h hlocal hproper]
  rintro x ⟨b, _, rfl⟩
  exact mem_map_of_mem X.subtype b.property

/-- In the actual derived core, the square-one elements are precisely F. -/
public theorem normalizer_core_derived_square_one_iff_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    ∀ x ∈ (commutator X).map X.subtype, x ^ 2 = 1 ↔ x ∈ d.F := by
  intro N X x hx
  constructor
  · intro hx2
    rw [← d.normalizer_core_derived_omega_of_local_inputs h hlocal hproper]
    obtain ⟨a, ha, rfl⟩ := hx
    let b : commutator X := ⟨a, ha⟩
    have hb : b ^ 2 = 1 := Subtype.ext (Subtype.ext hx2)
    have hbmem : b ∈ omega₁ (commutator X) (p := 2) := by
      apply Subgroup.subset_closure
      change b ^ (2 ^ 1) = 1
      simpa only [pow_one] using hb
    exact mem_map_of_mem (X.subtype.comp (commutator X).subtype) hbmem
  · intro hxF
    let : IsElementaryAbelian 2 d.F := d.elementary
    exact elemPow_eq_one_of_isElementaryAbelian x hxF

/-- The derived core meets the original derived group in exactly E∩F. -/
public theorem normalizer_core_derived_inf_original_derived_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    (commutator X).map X.subtype ⊓ E = E ⊓ d.F := by
  intro H J E N X
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  apply le_antisymm
  · intro x hx
    exact ⟨hx.2, (d.normalizer_core_derived_square_one_iff_of_local_inputs h hlocal hproper x hx.1).mp
      (elemPow_eq_one_of_isElementaryAbelian x hx.2)⟩
  · exact le_inf (inf_le_right.trans (d.elementary_le_normalizer_core_derived_of_local_inputs h hlocal hproper))
      inf_le_left

end Stellmacher.Recognition.ParrottSecondElementaryData
