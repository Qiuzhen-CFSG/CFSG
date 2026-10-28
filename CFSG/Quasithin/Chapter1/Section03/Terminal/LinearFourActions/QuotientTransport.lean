module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.QuotientTransport
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transport of the terminal action through nontrivial two-cores

For the actual image A of B in Y/O₂(Y), the restricted projection has
two-group kernel. Its inverse image of O₂(A) is therefore O₂(B), even
when B is not normal in Y. The resulting isomorphism B/O₂(B) ≃ A/O₂(A)
uses that projection. Lifting a conjugator in A then transports inner
action modulo O₂(A) to the shared ambient inner-action normalizer.

The pointwise displacement condition is checked against the actual
quotient automorphism. The intrinsic stabilizer premise only concerns
automorphisms of two-power order, as required for the acting two-group.
No concrete model stabilizer or forced outer action is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 1.3.9, printed p.514, and embeddings A.3.12(5),(14),(17), pp.47–48.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions
open CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G]

/-- The actual ambient automorphism is inner on the specified section. -/
def IsInnerOnTwoQuotient (A : Subgroup G) (α : MulAut G) : Prop :=
  ∃ a ∈ A, ∀ x ∈ A, a⁻¹ * α x * a * x⁻¹ ∈ A.pCoreIn 2

/-- Only automorphisms of two-power order are needed for the terminal argument. -/
def TwoStabilizerActsInner (A : Subgroup G) : Prop :=
  ∀ α : MulAut G, (∃ n : ℕ, α ^ (2 ^ n) = 1) →
    A.map α.toMonoidHom = A → IsInnerOnTwoQuotient A α

theorem IsInnerOnTwoQuotient.of_map {Q : Type*} [Group Q]
    {A : Subgroup G} (e : G ≃* Q) (α : MulAut G)
    (h : IsInnerOnTwoQuotient (A.map e.toMonoidHom) (e.symm.trans (α.trans e))) :
    IsInnerOnTwoQuotient A α := by
  obtain ⟨a, ⟨b, hb, rfl⟩, ha⟩ := h
  refine ⟨b, hb, fun x hx => ?_⟩
  have he := ha (e x) (mem_map_of_mem e.toMonoidHom hx)
  rw [← map_pCoreIn_of_injective 2 A e.toMonoidHom e.injective] at he
  have hm : e (b⁻¹ * α x * b * x⁻¹) ∈ (A.pCoreIn 2).map e.toMonoidHom := by
    simpa using he
  exact (mem_map_iff_mem e.injective).mp hm

theorem TwoStabilizerActsInner.of_map {Q : Type*} [Group Q]
    {A : Subgroup G} (e : G ≃* Q) (h : TwoStabilizerActsInner (A.map e.toMonoidHom)) :
    TwoStabilizerActsInner A := by
  intro α htwo hα
  let β := MulAut.congr e α
  have hc : β.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
    ext x
    simp [β]
  have hβ : (A.map e.toMonoidHom).map β.toMonoidHom = A.map e.toMonoidHom := by
    rw [map_map, hc, ← map_map, hα]
  have hβtwo : ∃ n : ℕ, β ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := htwo
    refine ⟨n, ?_⟩
    change (MulAut.congr e) α ^ (2 ^ n) = 1
    rw [← map_pow, hn, map_one]
  exact IsInnerOnTwoQuotient.of_map e α (h β hβtwo hβ)

theorem projection_comap_twoCore [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y) :
    (pCore 2 (twoQuotientImage B Y)).comap (twoQuotientProjection hBY) = pCore 2 B := by
  apply MonoidHom.comap_pCore_of_ker_isPGroup _ (twoQuotientProjection_surjective hBY)
  rw [twoQuotientProjection_ker]
  exact pCore_isPGroup.comap_of_injective (inclusion hBY) (inclusion_injective hBY)

def imageSectionMap {B Y : Subgroup G} (hBY : B ≤ Y) :
    B →* XiQuotient (twoQuotientImage B Y) :=
  (QuotientGroup.mk' (pCore 2 (twoQuotientImage B Y))).comp (twoQuotientProjection hBY)

theorem imageSectionMap_surjective {B Y : Subgroup G} (hBY : B ≤ Y) :
    Function.Surjective (imageSectionMap hBY) :=
  (QuotientGroup.mk'_surjective _).comp (twoQuotientProjection_surjective hBY)

theorem imageSectionMap_ker [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y) :
    (imageSectionMap hBY).ker = pCore 2 B := by
  rw [imageSectionMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', projection_comap_twoCore]

noncomputable def imageSectionEquiv [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y) :
    XiQuotient B ≃* XiQuotient (twoQuotientImage B Y) :=
  QuotientGroup.liftEquiv (pCore 2 B) (imageSectionMap_surjective hBY)
    (imageSectionMap_ker hBY).symm

theorem imageSectionEquiv_mk [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y) (b : B) :
    imageSectionEquiv hBY (QuotientGroup.mk' (pCore 2 B) b) = imageSectionMap hBY b := rfl

/-- A displacement in the image two-core lifts to the intrinsic two-core. -/
theorem mem_twoCore_of_projection_mem [Finite G] {B Y : Subgroup G}
    (hBY : B ≤ Y) (b : B)
    (hb : (twoQuotientImageMap hBY b) ∈ (twoQuotientImage B Y).pCoreIn 2) :
    b ∈ pCore 2 B := by
  rw [← projection_comap_twoCore hBY]
  obtain ⟨a, ha, he⟩ := hb
  have heq : a = twoQuotientProjection hBY b := Subtype.ext he
  change twoQuotientProjection hBY b ∈ pCore 2 (twoQuotientImage B Y)
  exact heq ▸ ha

/-- Inner action modulo the image two-core lifts to inner action on B/O₂(B). -/
theorem mem_innerNormalizer_of_image_section [Finite G] {B Y : Subgroup G}
    (hBY : B ≤ Y) (s : normalizer (Y : Set G))
    (hsB : (s : G) ∈ normalizer (B : Set G))
    (hinner : IsInnerOnTwoQuotient (twoQuotientImage B Y) (twoQuotientNormalizerAction Y s)) :
    (s : G) ∈ innerTwoQuotientNormalizer B := by
  obtain ⟨a, ha, hact⟩ := hinner
  obtain ⟨b, rfl⟩ := exists_preimage_twoQuotientImage hBY ha
  let c : G := (b : G)⁻¹ * s
  have hcN : c ∈ normalizer (B : Set G) :=
    (normalizer (B : Set G)).mul_mem (B.le_normalizer (B.inv_mem b.property)) hsB
  have hc : c ∈ twoSectionCentralizer B ⊤ := by
    refine ⟨mem_top _, hcN, ?_⟩
    intro x hx
    have hzB : ⁅c, x⁆ ∈ B := B.mul_mem
      ((mem_normalizer_iff.mp hcN x).mp hx) (B.inv_mem hx)
    have hzcore : (⟨⁅c, x⁆, hzB⟩ : B) ∈ pCore 2 B := by
      apply mem_twoCore_of_projection_mem hBY
      let q := QuotientGroup.mk' (pCore 2 Y)
      let xY : Y := inclusion hBY ⟨x, hx⟩
      let bY : Y := inclusion hBY b
      let α := Y.normalizerMonoidHom s
      have he := hact (twoQuotientImageMap hBY ⟨x, hx⟩) (mem_twoQuotientImage hBY ⟨x, hx⟩)
      change (q bY)⁻¹ * twoQuotientNormalizerAction Y s (q xY) * q bY * (q xY)⁻¹ ∈ _ at he
      rw [twoQuotientNormalizerAction_mk] at he
      have hz : inclusion hBY (⟨⁅c, x⁆, hzB⟩ : B) =
          bY⁻¹ * α xY * bY * xY⁻¹ := by
        apply Subtype.ext
        simp only [coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe,
          coe_inclusion, commutatorElement_def, c, xY, bY, α]
        group
      change q (inclusion hBY (⟨⁅c, x⁆, hzB⟩ : B)) ∈ _
      simpa only [hz, map_mul, map_inv] using he
    exact mem_map_of_mem B.subtype hzcore
  apply (mem_innerTwoQuotientNormalizer_iff B s).mpr
  exact ⟨b, b.property, c, hc, by dsimp [c]; group⟩

theorem le_innerNormalizer_of_image_stabilizer [Finite G] {B Y S : Subgroup G}
    (hBY : B ≤ Y) (hS : IsPGroup 2 S)
    (hSB : S ≤ normalizer (B : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (hinner : TwoStabilizerActsInner (twoQuotientImage B Y)) :
    S ≤ innerTwoQuotientNormalizer B := by
  intro s hs
  apply mem_innerNormalizer_of_image_section hBY ⟨s, hSY hs⟩ (hSB hs)
  apply hinner _ ?_ (twoQuotientNormalizerAction_image hBY ⟨s, hSY hs⟩ (hSB hs))
  let f := (twoQuotientNormalizerAction Y).comp (inclusion hSY)
  obtain ⟨n, hn⟩ := hS (⟨s, hs⟩ : S)
  refine ⟨n, ?_⟩
  change f ⟨s, hs⟩ ^ (2 ^ n) = 1
  rw [← map_pow, hn, map_one]

theorem le_innerNormalizer_of_model_stabilizer [Finite G] {Q : Type*} [Group Q]
    {B Y S : Subgroup G} (hBY : B ≤ Y) (hS : IsPGroup 2 S)
    (hSB : S ≤ normalizer (B : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (e : XiQuotient Y ≃* Q)
    (hinner : TwoStabilizerActsInner ((twoQuotientImage B Y).map e.toMonoidHom)) :
    S ≤ innerTwoQuotientNormalizer B :=
  le_innerNormalizer_of_image_stabilizer hBY hS hSB hSY (hinner.of_map e)

/-- The displacement convention is exactly the shared product normalizer. -/
theorem mem_innerNormalizer_iff_conjugation {B : Subgroup G}
    (s : normalizer (B : Set G)) :
    (s : G) ∈ innerTwoQuotientNormalizer B ↔
      IsInnerOnTwoQuotient B (MulAut.conj (s : G)) := by
  constructor
  · intro hs
    obtain ⟨b, hb, c, hc, he⟩ := (mem_innerTwoQuotientNormalizer_iff B s).mp hs
    refine ⟨b, hb, fun x hx => ?_⟩
    have heq : b⁻¹ * MulAut.conj (s : G) x * b * x⁻¹ = ⁅c, x⁆ := by
      change b⁻¹ * ((s : G) * x * (s : G)⁻¹) * b * x⁻¹ = _
      rw [← he, commutatorElement_def]
      group
    rw [heq]
    exact hc.2.2 x hx
  · rintro ⟨b, hb, h⟩
    let c : G := b⁻¹ * s
    have hcN : c ∈ normalizer (B : Set G) :=
      (normalizer (B : Set G)).mul_mem (B.le_normalizer (B.inv_mem hb)) s.property
    have hc : c ∈ twoSectionCentralizer B ⊤ := by
      refine ⟨mem_top _, hcN, fun x hx => ?_⟩
      have heq : ⁅c, x⁆ = b⁻¹ * MulAut.conj (s : G) x * b * x⁻¹ := by
        change (b⁻¹ * (s : G)) * x * (b⁻¹ * (s : G))⁻¹ * x⁻¹ =
          b⁻¹ * ((s : G) * x * (s : G)⁻¹) * b * x⁻¹
        group
      rw [heq]
      exact h x hx
    exact (mem_innerTwoQuotientNormalizer_iff B s).mpr
      ⟨b, hb, c, hc, by dsimp [c]; group⟩

/-- Membership means that the actual automorphism of B/O₂(B) is inner. -/
theorem mem_innerNormalizer_iff_quotient_action {B : Subgroup G}
    (s : normalizer (B : Set G)) :
    (s : G) ∈ innerTwoQuotientNormalizer B ↔
      ∃ a : XiQuotient B, twoQuotientNormalizerAction B s = MulAut.conj a := by
  let q := QuotientGroup.mk' (pCore 2 B)
  let β := B.normalizerMonoidHom s
  rw [mem_innerNormalizer_iff_conjugation]
  constructor
  · rintro ⟨b, hb, h⟩
    let a : B := ⟨b, hb⟩
    refine ⟨q a, MulEquiv.ext fun x => ?_⟩
    induction x using Quotient.inductionOn with
    | h x =>
      have hc : a⁻¹ * β x * a * x⁻¹ ∈ pCore 2 B := by
        apply (mem_map_iff_mem B.subtype_injective).mp
        exact h x x.property
      have he : q (a⁻¹ * β x * a * x⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
      simp only [map_mul, map_inv] at he
      rw [show (⟦x⟧ : XiQuotient B) = q x from rfl, twoQuotientNormalizerAction_mk]
      change q (β x) = q a * q x * (q a)⁻¹
      calc
        q (β x) = q a * ((q a)⁻¹ * q (β x) * q a * (q x)⁻¹) * q x * (q a)⁻¹ := by group
        _ = q a * q x * (q a)⁻¹ := by rw [he]; group
  · rintro ⟨a, hα⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) a
    refine ⟨b, b.property, fun x hx => ?_⟩
    let z : B := ⟨x, hx⟩
    have he := DFunLike.congr_fun hα (q z)
    rw [twoQuotientNormalizerAction_mk] at he
    change q (β z) = q b * q z * (q b)⁻¹ at he
    have hc : b⁻¹ * β z * b * z⁻¹ ∈ pCore 2 B := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (b⁻¹ * β z * b * z⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, he]
      group
    exact mem_map_of_mem B.subtype hc

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions
