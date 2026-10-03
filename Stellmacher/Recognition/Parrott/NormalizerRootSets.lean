module

public import Stellmacher.Recognition.Parrott.SecondNormalizer

/-!
# Root fibers and the precise involution images in Parrott's normalizer

For K = O₂(N_G(F)), the source's four families use right conjugation by
involutions i outside K centralizing m², and a generator of Z(⟨K,i⟩).
Both K and this center are represented by their actual images in G.

Self-centralization of F puts Z(⟨K,i⟩) inside F, so its elements have
square one and centralize m. Thus all four families really are roots of
m² in K. Normalizer conjugation also preserves the size of the full root
fiber. Exhaustion and the lower involution census are separate assertions.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}

/-- The entire square-root fiber in the actual ambient normalizer core. -/
@[expose] public def ParrottSecondElementaryData.normalizerCoreRoots
    (e : ParrottSecondElementaryData z) (m : G) : Set G :=
  let N := normalizer (e.F : Set G)
  let K := (pCore 2 N).map N.subtype
  {g | g ∈ K ∧ g ^ 2 = m ^ 2}

/-- The exact four families in Parrott's root census. The central generator
may depend on the involution; conjugation is on the right throughout. -/
@[expose] public def ParrottSecondElementaryData.normalizerRootInvolutionImages
    (e : ParrottSecondElementaryData z) (m : G) : Set G :=
  let N := normalizer (e.F : Set G)
  let K := (pCore 2 N).map N.subtype
  {g | ∃ i ε : G, i ∈ N ∧ i ∉ K ∧ orderOf i = 2 ∧
    i ∈ centralizer ({m ^ 2} : Set G) ∧
    zpowers ε = (center (K ⊔ zpowers i : Subgroup G)).map (K ⊔ zpowers i).subtype ∧
    (g = i⁻¹ * m * i ∨ g = i⁻¹ * m⁻¹ * i ∨
      g = i⁻¹ * (m * ε) * i ∨ g = i⁻¹ * (m⁻¹ * ε) * i)}

/-- Conjugation by a normalizer element preserves the actual core image. -/
public theorem ParrottSecondElementaryData.normalizer_core_conj_mem_iff
    (e : ParrottSecondElementaryData z) (i : G)
    (hi : i ∈ normalizer (e.F : Set G)) (g : G) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    i⁻¹ * g * i ∈ K ↔ g ∈ K := by
  intro N K
  have hNK : N ≤ normalizer (K : Set G) := by
    have hh := le_normalizer_map (H := pCore 2 N) N.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  exact (mem_normalizer_iff''.mp (hNK hi) g).symm

/-- The full root-fiber count is unchanged by normalizer conjugation. -/
public theorem ParrottSecondElementaryData.normalizerCoreRoots_conj_ncard
    (e : ParrottSecondElementaryData z) (m i : G)
    (hi : i ∈ normalizer (e.F : Set G)) :
    (e.normalizerCoreRoots (i⁻¹ * m * i)).ncard =
      (e.normalizerCoreRoots m).ncard := by
  let φ := MulAut.conj i⁻¹
  let K := (pCore 2 (normalizer (e.F : Set G))).map
    (normalizer (e.F : Set G)).subtype
  symm
  apply Nat.card_congr
  refine φ.toEquiv.subtypeEquiv (fun g => ?_)
  have hφm : i⁻¹ * m * i = φ m := by simp [φ]
  rw [hφm]
  change (g ∈ K ∧ g ^ 2 = m ^ 2) ↔ (φ g ∈ K ∧ (φ g) ^ 2 = (φ m) ^ 2)
  rw [← map_pow, ← map_pow, φ.injective.eq_iff]
  exact and_congr (by simpa only [φ, MulAut.conj_apply, inv_inv] using
    (e.normalizer_core_conj_mem_iff i hi g).symm) Iff.rfl

/-- Self-centralization of F puts the center of every overgroup ⟨K,i⟩ in F.
No hypothesis on i is needed for this containment. -/
public theorem ParrottSecondElementaryData.normalizer_join_center_le_elementary
    (e : ParrottSecondElementaryData z) (i : G) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    (center (K ⊔ zpowers i : Subgroup G)).map (K ⊔ zpowers i).subtype ≤ e.F := by
  intro N K
  rw [← e.centralizer_eq]
  rintro g ⟨c, hc, rfl⟩ b hb
  exact congrArg (K ⊔ zpowers i).subtype
    (mem_center_iff.mp hc ⟨b, mem_sup_left (e.le_normalizer_core hb)⟩)

/-- Each of the four involution-image families consists of actual roots in K.
This direction requires neither the root exhaustion nor a census hypothesis. -/
public theorem ParrottSecondElementaryData.normalizerRootInvolutionImages_subset
    (e : ParrottSecondElementaryData z) (m : G)
    (hm : m ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype) (hfour : m ^ 4 = 1) :
    e.normalizerRootInvolutionImages m ⊆ e.normalizerCoreRoots m := by
  let N := normalizer (e.F : Set G)
  let K := (pCore 2 N).map N.subtype
  rintro g ⟨i, ε, hiN, _, _, hic, hε, hg⟩
  have hεZ : ε ∈ (center (K ⊔ zpowers i : Subgroup G)).map (K ⊔ zpowers i).subtype :=
    hε ▸ mem_zpowers ε
  have hεF : ε ∈ e.F := e.normalizer_join_center_le_elementary i hεZ
  let _ := e.elementary
  have hε2 : ε ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian ε hεF
  have hmε : Commute m ε := by
    obtain ⟨c, hc, heq⟩ := hεZ
    have hh := congrArg (K ⊔ zpowers i).subtype
      (mem_center_iff.mp hc ⟨m, mem_sup_left hm⟩)
    change m * (c : G) = (c : G) * m at hh
    change (c : G) = ε at heq
    rwa [heq] at hh
  have hmi2 : (m⁻¹) ^ 2 = m ^ 2 := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_add] using hfour
  have hroot (a : G) (ha : a ∈ K) (ha2 : a ^ 2 = m ^ 2) :
      i⁻¹ * a * i ∈ e.normalizerCoreRoots m := by
    refine ⟨(e.normalizer_core_conj_mem_iff i hiN a).mpr ha, ?_⟩
    have hc := mem_centralizer_singleton_iff.mp hic
    calc
      (i⁻¹ * a * i) ^ 2 = i⁻¹ * a ^ 2 * i := by simp only [pow_two]; group
      _ = m ^ 2 := by rw [ha2, mul_assoc, ← hc, inv_mul_cancel_left]
  rcases hg with rfl | rfl | rfl | rfl
  · exact hroot m hm rfl
  · exact hroot m⁻¹ (K.inv_mem hm) hmi2
  · exact hroot (m * ε) (K.mul_mem hm (e.le_normalizer_core hεF))
      (by rw [hmε.mul_pow, hε2, mul_one])
  · exact hroot (m⁻¹ * ε) (K.mul_mem (K.inv_mem hm) (e.le_normalizer_core hεF))
      (by rw [hmε.inv_left.mul_pow, hε2, mul_one, hmi2])

end Stellmacher.Recognition
