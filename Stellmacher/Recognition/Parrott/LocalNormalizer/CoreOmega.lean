module

public import Stellmacher.Recognition.Parrott.NormalizerCoreOmega
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreCenter
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmegaLocal

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreOmega`.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The actual omega subgroup contains both elementary subgroups. -/
public theorem elementary_join_le_normalizer_core_omega_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    E ⊔ d.F ≤ (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) := by
  intro H J E N K
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator_of_local_inputs h hlocal hproper
  have htZ : t ∈ (center K).map (N.subtype.comp K.subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hEK : E ≤ K.map N.subtype := by
    rw [d.normalizer_core_eq_sylow_centralizer_of_local_inputs h hlocal hproper t htZ htz]
    exact d.derived_le_t_centralizer h t ht.1
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  refine sup_le ?_ d.normalizer_core_omega_inclusions.1
  intro e he
  obtain ⟨eN, heK, heq⟩ := hEK he
  let eK : K := ⟨eN, heK⟩
  have heU : eK ∈ omega₁ K (p := 2) := by
    apply Subgroup.subset_closure
    apply Subtype.ext
    apply Subtype.ext
    change (eN : G) ^ (2 ^ 1) = 1
    change (eN : G) = e at heq
    rw [heq]
    exact elemPow_eq_one_of_isElementaryAbelian e he
  exact ⟨eK, heU, heq⟩

/-- The ambient center of the actual omega subgroup lies in E∩F. -/
public theorem normalizer_core_omega_center_le_inf_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let embed := N.subtype.comp K.subtype
    (center U).map (embed.comp U.subtype) ≤ E ⊓ d.F := by
  intro H J E N K U embed
  refine le_inf ?_ d.normalizer_core_omega_inclusions.2.2
  have hEU : E ≤ U.map embed :=
    le_sup_left.trans (d.elementary_join_le_normalizer_core_omega_of_local_inputs h hlocal hproper)
  rw [← show centralizer (E : Set G) = E from parrott_derived_centralizer z h]
  rintro x ⟨xU, hxZ, rfl⟩ e he
  obtain ⟨eK, heU, rfl⟩ := hEU he
  exact congrArg (embed.comp U.subtype) (mem_center_iff.mp hxZ ⟨eK, heU⟩)

/-- The omega image cannot be the join of the two elementary subgroups:
its characteristic derived line would force the whole normalizer to fix z. -/
public theorem elementary_join_lt_normalizer_core_omega_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    E ⊔ d.F < (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) := by
  intro H J E N K
  let U := omega₁ K (p := 2)
  let W := U.map K.subtype
  let X := U.map (N.subtype.comp K.subtype)
  let A := E ⊔ d.F
  have hAX : A ≤ X := d.elementary_join_le_normalizer_core_omega_of_local_inputs h hlocal hproper
  refine lt_of_le_of_ne hAX ?_
  intro heq
  let : U.Characteristic := omega₁_characteristic K
  let : W.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNX : N ≤ normalizer (X : Set G) := by
    have hh := le_normalizer_map (H := W) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, W, X, map_map] using hh
  have hNA : N ≤ normalizer (A : Set G) := by
    change A = X at heq
    rwa [← heq] at hNX
  have hAH : normalizer (A : Set G) ≤ H :=
    normalizer_le_centralizer_of_characteristic_involution A (commutator A)
      z h.involution (d.elementary_join_commutator h)
  have hNT : N ≤ (d.sylow : Subgroup G) := by
    rw [← d.normalizer_inf_centralizer h]
    exact le_inf le_rfl (hNA.trans hAH)
  exact hproper.not_ge hNT

/-- A square-one generator witnesses strict enlargement of E∨F inside Ω₁(K).
The witness already belongs to the actual normalizer core. -/
public theorem exists_normalizer_core_involution_outside_elementary_join_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ y : G, y ∈ K.map N.subtype ∧ orderOf y = 2 ∧ y ∉ E ⊔ d.F := by
  classical
  intro H J E N K
  let i := N.subtype.comp K.subtype
  by_contra hnone
  have hU : (omega₁ K (p := 2)).map i ≤ E ⊔ d.F := by
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro k hk
    change k ^ (2 ^ 1) = 1 at hk
    change i k ∈ E ⊔ d.F
    by_contra hout
    apply hnone
    refine ⟨i k, mem_map_of_mem N.subtype k.property, ?_, hout⟩
    apply orderOf_eq_prime
    · rw [← map_pow, show k ^ 2 = 1 from hk, map_one]
    · intro heq
      exact hout (heq ▸ (E ⊔ d.F).one_mem)
  exact (d.elementary_join_lt_normalizer_core_omega_of_local_inputs h hlocal hproper).not_ge hU

/-- The actual normalizer core contains an involution outside the original
core. In particular this establishes the required involution in T−J. -/
public theorem exists_normalizer_core_involution_outside_original_core_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ y : G, y ∈ K.map N.subtype ∧ orderOf y = 2 ∧ y ∉ J.map H.subtype := by
  intro H J N K
  obtain ⟨y, hyK, hy2, hyA⟩ :=
    d.exists_normalizer_core_involution_outside_elementary_join_of_local_inputs h hlocal hproper
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator_of_local_inputs h hlocal hproper
  have htZ : t ∈ (center K).map (N.subtype.comp K.subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hKC := d.normalizer_core_eq_sylow_centralizer_of_local_inputs h hlocal hproper t htZ htz
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← hKC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  refine ⟨y, hyK, hy2, ?_⟩
  intro hyJ
  have hyt : y ∈ centralizer ({t} : Set G) := (hKC ▸ hyK).2
  exact hyA (d.t_centralizer_core_involution_mem_elementary_join h t ht htz hCcard
    y ⟨hyJ, hyt⟩ (hy2 ▸ pow_orderOf_eq_one y))

/-- The actual omega has order 256 and center of order eight. Its ambient
center lies in E∩F, and its ambient image is the centralizer of that center
inside the actual normalizer core. No outer involution is assumed. -/
public theorem normalizer_core_omega_structure_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let embed := N.subtype.comp K.subtype
    let X := U.map embed
    let Z := (center U).map (embed.comp U.subtype)
    Nat.card U = 256 ∧ Nat.card (center U) = 8 ∧ Z ≤ E ⊓ d.F ∧
      X = K.map N.subtype ⊓ centralizer (Z : Set G) := by
  intro H J E N K U embed X Z
  obtain ⟨y, hyK, hy2, hyJ⟩ :=
    d.exists_normalizer_core_involution_outside_original_core_of_local_inputs h hlocal hproper
  obtain ⟨hU, hZ, hX⟩ :=
    d.normalizer_core_omega_structure_of_outer_involution_of_local_inputs h hlocal hproper y hyK hy2 hyJ
  exact ⟨hU, hZ, d.normalizer_core_omega_center_le_inf_of_local_inputs h hlocal hproper, hX⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
