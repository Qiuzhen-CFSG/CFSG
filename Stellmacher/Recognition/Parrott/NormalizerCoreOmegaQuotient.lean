module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeCenters
public import Theory.GroupTheory.ElementaryEightPlaneOrder24

/-!
# The symmetric-four quotient of the second normalizer

The kernel of N's conjugation action on Z(Ω₁(K)) is Ω₁(K): a kernel
element fixes z and t, hence belongs to K, where the omega centralizer
calculation applies. The image has order 24 and preserves the central
four-group Z(K). Its faithful action on the four points outside that
plane identifies the quotient with S₄.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the paragraph following Lemma 6.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The actual omega image is the centralizer of its center in N, not
only in K. -/
public theorem normalizer_omega_center_centralizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let i := N.subtype.comp K.subtype
    N ⊓ centralizer ((center U).map (i.comp U.subtype) : Set G) = U.map i := by
  intro N K U i
  let Z := (center U).map (i.comp U.subtype)
  have hX := (d.normalizer_core_omega_structure h hN hproper).2.2.2
  change U.map i = K.map N.subtype ⊓ centralizer (Z : Set G) at hX
  rw [hX]
  refine le_antisymm ?_ (inf_le_inf_right _ (map_subtype_le K))
  obtain ⟨t, _, htz, _, _, _, hZK⟩ :=
    d.exists_normalizer_core_center_generator h hN hproper
  have htZK : t ∈ (center K).map i := by
    rw [hZK]
    exact mem_sup_right (mem_zpowers t)
  have hzZ : z ∈ Z :=
    d.normalizer_core_omega_inclusions.2.1 d.z_mem_normalizer_core_center
  have htZ : t ∈ Z := d.normalizer_core_omega_inclusions.2.1 htZK
  intro x hx
  refine ⟨?_, hx.2⟩
  rw [d.normalizer_core_eq_sylow_centralizer h hN hproper t htZK htz]
  refine ⟨?_, mem_centralizer_singleton_iff.mpr (hx.2 t htZ).symm⟩
  rw [← d.normalizer_inf_centralizer h]
  exact ⟨hx.1, mem_centralizer_singleton_iff.mpr (hx.2 z hzZ).symm⟩

/-- The quotient by the ambient-in-N image of the actual omega subgroup
is the full symmetric group on four points. -/
public theorem normalizer_omega_quotient (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let V := U.map K.subtype
    letI : U.Characteristic := omega₁_characteristic K
    letI : V.Normal := ConjAct.normal_of_characteristic_of_normal
    Nonempty ((N ⧸ V) ≃* Equiv.Perm (Fin 4)) := by
  intro N K U V
  let : U.Characteristic := omega₁_characteristic K
  let : V.Normal := ConjAct.normal_of_characteristic_of_normal
  let i := N.subtype.comp K.subtype
  let Z := (center U).map (i.comp U.subtype)
  let D := (center K).map i
  have hNZ : N ≤ normalizer (Z : Set G) := d.normalizer_core_centers_normalized.2
  have hND : N ≤ normalizer (D : Set G) := d.normalizer_core_centers_normalized.1
  have hDZ : D ≤ Z := d.normalizer_core_omega_inclusions.2.1
  let f : N →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hNZ)
  have hker : f.ker = V := by
    ext x
    rw [MonoidHom.mem_ker]
    have hfix : f x = 1 ↔ (x : G) ∈ centralizer (Z : Set G) := by
      constructor
      · intro hx u hu
        have hh := congrArg (fun a : MulAut Z => (a ⟨u, hu⟩ : G)) hx
        change (x : G) * u * (x : G)⁻¹ = u at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      · intro hx
        apply MulEquiv.ext
        intro u
        apply Subtype.ext
        change (x : G) * (u : G) * (x : G)⁻¹ = u
        exact mul_inv_eq_iff_eq_mul.mpr (hx u u.property).symm
    rw [hfix]
    have hX : N ⊓ centralizer (Z : Set G) = V.map N.subtype := by
      simpa only [V, map_map, i] using d.normalizer_omega_center_centralizer h hN hproper
    constructor
    · intro hx
      have hxmap : (x : G) ∈ V.map N.subtype := hX ▸ ⟨x.property, hx⟩
      obtain ⟨y, hy, heq⟩ := hxmap
      exact (N.subtype_injective heq) ▸ hy
    · intro hx
      have hxmap := mem_map_of_mem N.subtype hx
      exact (hX.symm ▸ hxmap).2
  have hVcard : Nat.card V = 256 :=
    (card_map_of_injective K.subtype_injective).trans
      (d.normalizer_core_omega_structure h hN hproper).1
  have hRcard : Nat.card f.range = 24 := by
    have hc := f.ker.index_mul_card
    rw [index_ker, hker, hVcard, (d.normalizer_core_order h hN hproper).1] at hc
    omega
  have hZcard : Nat.card Z = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hDcard : Nat.card (D.subgroupOf Z) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDZ).toEquiv]
    exact (card_map_of_injective (K := center K) (f := i)
      (N.subtype_injective.comp K.subtype_injective)).trans
      (d.normalizer_core_order h hN hproper).2.2.2
  let : IsElementaryAbelian 2 (center U) := d.normalizer_core_omega_center_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map (i.comp U.subtype)
  obtain ⟨e⟩ := elementaryEight_plane_order24_equiv_S4 hZcard (D.subgroupOf Z)
    hDcard f.range hRcard (by
      rintro ⟨a, ha⟩ x
      obtain ⟨n, rfl⟩ := ha
      change (n : G) * (x : G) * (n : G)⁻¹ ∈ D ↔ (x : G) ∈ D
      exact (mem_normalizer_iff.mp (hND n.property) x).symm)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans e)⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
