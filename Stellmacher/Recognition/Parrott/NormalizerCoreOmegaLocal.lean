module

public import Stellmacher.Recognition.Parrott.NormalizerCoreCenter
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaCentralization
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaGenerators

/-!
# Assembly of the normalizer-core omega from local element calculations

The fixed-space centralizer of an actual outer involution has order 256 and
center of order eight. Every involution of K centralizes that fixed space,
giving one containment in Ω₁(K)'s identification with the fixed-space
centralizer. The opposite containment follows from the proved
commutator-generation theorem. This module combines these calculations and
retains the actual subgroup embeddings in the resulting order and centralizer
formulas.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677, the omega calculation surrounding Lemma 6.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The two remaining element calculations identify the actual omega with
its fixed-space centralizer, including both exact orders and self-centralization.
The premises concern involutions and generation, not assumed omega orders. -/
private theorem normalizer_core_omega_structure_of_fixed_space_calculations
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
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
    ∀ y : G, y ∈ K.map N.subtype → orderOf y = 2 → y ∉ J.map H.subtype →
      let V := E ⊓ centralizer ({y} : Set G)
      (∀ k : G, k ∈ K.map N.subtype → k ^ 2 = 1 → k ∈ centralizer (V : Set G)) →
      J.map H.subtype ⊓ centralizer (V : Set G) ≤ X →
      Nat.card U = 256 ∧ Nat.card (center U) = 8 ∧
        X = K.map N.subtype ⊓ centralizer (Z : Set G) := by
  intro H J E N K U embed X Z y hy hy2 hyJ V hinvol hB
  let B := J.map H.subtype ⊓ centralizer (V : Set G)
  let C := K.map N.subtype ⊓ centralizer (V : Set G)
  obtain ⟨hVcard, _, _, hCcard, hgen, hcenter⟩ :=
    d.normalizer_core_outer_fixed_centralizer h hN hproper y hy hy2 hyJ
  change Nat.card V = 8 at hVcard
  change Nat.card C = 256 at hCcard
  change C = B ⊔ zpowers y at hgen
  change (center C).map C.subtype = V at hcenter
  have hinj : Function.Injective embed := N.subtype_injective.comp K.subtype_injective
  have hXC : X = C := by
    apply le_antisymm
    · have hcentral : X ≤ centralizer (V : Set G) := by
        apply map_le_iff_le_comap.mpr
        apply (closure_le _).mpr
        intro k hk
        apply hinvol (embed k) (mem_map_of_mem N.subtype k.property)
        change k ^ (2 ^ 1) = 1 at hk
        have hh := congrArg embed hk
        simpa only [pow_one, map_pow, map_one] using hh
      refine le_inf ?_ hcentral
      rintro k ⟨kK, _, rfl⟩
      exact mem_map_of_mem N.subtype kK.property
    · rw [hgen]
      refine sup_le hB (zpowers_le.mpr ?_)
      obtain ⟨yN, hyK, heq⟩ := hy
      let yK : K := ⟨yN, hyK⟩
      have hyeq : embed yK = y := heq
      refine ⟨yK, subset_closure ?_, hyeq⟩
      apply hinj
      change embed (yK ^ (2 ^ 1)) = embed 1
      rw [map_pow, map_one, hyeq, pow_one]
      exact hy2 ▸ pow_orderOf_eq_one y
  have hZV : Z = V := by
    apply le_antisymm
    · rintro w ⟨u, hu, rfl⟩
      rw [← hcenter]
      have huC : embed (u : K) ∈ C := hXC ▸ mem_map_of_mem embed u.property
      refine ⟨⟨embed (u : K), huC⟩, mem_center_iff.mpr ?_, rfl⟩
      intro c
      have hcX : (c : G) ∈ X := hXC.symm ▸ c.property
      obtain ⟨cK, hcK, hc⟩ := hcX
      apply Subtype.ext
      change (c : G) * embed (u : K) = embed (u : K) * (c : G)
      rw [← hc]
      exact congrArg (embed.comp U.subtype) (mem_center_iff.mp hu ⟨cK, hcK⟩)
    · intro v hv
      have hvC : v ∈ (center C).map C.subtype := hcenter.symm ▸ hv
      obtain ⟨vC, hvZ, rfl⟩ := hvC
      have hvX : (vC : G) ∈ X := hXC.symm ▸ vC.property
      obtain ⟨vK, hvK, hv⟩ := hvX
      refine ⟨⟨vK, hvK⟩, mem_center_iff.mpr ?_, hv⟩
      intro u
      apply Subtype.ext
      apply hinj
      have huC : embed (u : K) ∈ C := hXC ▸ mem_map_of_mem embed u.property
      have hh := congrArg C.subtype (mem_center_iff.mp hvZ ⟨embed (u : K), huC⟩)
      change embed ((u : K) * vK) = embed (vK * (u : K))
      rw [map_mul, map_mul, hv]
      exact hh
  have hUcard : Nat.card U = 256 := by
    rw [← card_map_of_injective (K := U) hinj]
    change Nat.card X = 256
    rw [hXC, hCcard]
  have hZcard : Nat.card (center U) = 8 := by
    rw [← card_map_of_injective (K := center U) (f := embed.comp U.subtype)
      (hinj.comp U.subtype_injective)]
    change Nat.card Z = 8
    rw [hZV, hVcard]
  exact ⟨hUcard, hZcard, by rw [hZV]; exact hXC⟩


/-- Once all square-one elements of K centralize the fixed derived space of
y, the actual omega has order 256, center of order eight, and equals the
centralizer of its own center in K. The opposite containment is proved by
commutators with the original core, not supplied as an extra premise. -/
public theorem normalizer_core_omega_structure_of_involutions_centralize
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
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
    ∀ y : G, y ∈ K.map N.subtype → orderOf y = 2 → y ∉ J.map H.subtype →
      (∀ k : G, k ∈ K.map N.subtype → k ^ 2 = 1 →
        k ∈ centralizer (E ⊓ centralizer ({y} : Set G) : Set G)) →
      Nat.card U = 256 ∧ Nat.card (center U) = 8 ∧
        X = K.map N.subtype ⊓ centralizer (Z : Set G) := by
  intro H J E N K U embed X Z y hy hy2 hyJ hinvol
  exact d.normalizer_core_omega_structure_of_fixed_space_calculations
    h hN hproper y hy hy2 hyJ hinvol
    (d.normalizer_core_outer_fixed_kernel_le_omega h hN hproper y hy hy2 hyJ)

/-- An actual involution of the normalizer core outside the original core
determines the omega structure: its order is 256, its center has order eight,
and it is the centralizer of its center in the normalizer core. -/
public theorem normalizer_core_omega_structure_of_outer_involution
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let embed := N.subtype.comp K.subtype
    let X := U.map embed
    let Z := (center U).map (embed.comp U.subtype)
    ∀ y : G, y ∈ K.map N.subtype → orderOf y = 2 → y ∉ J.map H.subtype →
      Nat.card U = 256 ∧ Nat.card (center U) = 8 ∧
        X = K.map N.subtype ⊓ centralizer (Z : Set G) := by
  intro H J N K U embed X Z y hy hy2 hyJ
  exact d.normalizer_core_omega_structure_of_involutions_centralize
    h hN hproper y hy hy2 hyJ
    (d.normalizer_core_involutions_centralize_outer_fixed h hN hproper y hy hy2 hyJ)

end Stellmacher.Recognition.ParrottSecondElementaryData
