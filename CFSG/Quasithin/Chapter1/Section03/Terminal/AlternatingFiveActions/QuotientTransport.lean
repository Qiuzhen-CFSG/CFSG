module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.Definitions
public import Theory.GroupTheory.InnerStabilizerAction
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Quotient transport for the terminal A₅ action argument

The quotient image is the image of the actual inclusion B ≤ Y. The
normalizer actions preserve that image and commute with the quotient maps.
If an ambient element acts on the image by an inner conjugator, lift that
conjugator to B. The remaining commutators lie in B ∩ O₂(Y) ≤ O₂(B), giving
membership in the shared inner-action normalizer.

When the image has trivial two-core, its restricted projection has kernel
exactly O₂(B). This gives the actual quotient isomorphism and its equivariance.
The stabilizer assertion remains an explicit intrinsic model premise here;
this module does not prove either of the model exclusions in 1.3.9.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, proof of Lemma 1.3.9, printed p.514, using the
quotient embeddings of Lemma 1.2.4 and Proposition A.3.12.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.ChapterA.Section04

namespace CFSG.Quasithin.Chapter1.Terminal
variable {G : Type*} [Group G]

/-- The actual image of B in Y/O₂(Y), using its inclusion in Y. -/
def twoQuotientImage (B Y : Subgroup G) : Subgroup (XiQuotient Y) :=
  (B.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))

/-- The quotient map on B induced by its specified inclusion in Y. -/
def twoQuotientImageMap {B Y : Subgroup G} (hBY : B ≤ Y) : B →* XiQuotient Y :=
  (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hBY)

/-- Every element of the quotient image has a representative in B. -/
theorem exists_preimage_twoQuotientImage {B Y : Subgroup G} (hBY : B ≤ Y)
    {x : XiQuotient Y} (hx : x ∈ twoQuotientImage B Y) :
    ∃ b : B, twoQuotientImageMap hBY b = x := by
  obtain ⟨b, hb, rfl⟩ := hx
  exact ⟨⟨b, hb⟩, rfl⟩

/-- The restricted quotient map takes values in the actual image. -/
theorem mem_twoQuotientImage {B Y : Subgroup G} (hBY : B ≤ Y) (b : B) :
    twoQuotientImageMap hBY b ∈ twoQuotientImage B Y :=
  mem_map_of_mem _ b.property

/-- The kernel is contained in O₂(B), without any normality assumption on B in Y. -/
theorem twoQuotientImageMap_ker_le {B Y : Subgroup G} (hBY : B ≤ Y) :
    (twoQuotientImageMap hBY).ker ≤ pCore 2 B := by
  intro b hb
  have hy : inclusion hBY b ∈ pCore 2 Y := (QuotientGroup.eq_one_iff _).mp hb
  have hh : (b : G) ∈ B.pCoreIn 2 := inf_pCoreIn_le_of_le 2 hBY
    ⟨b.property, mem_map_of_mem Y.subtype hy⟩
  obtain ⟨c, hc, he⟩ := hh
  have hcb : c = b := Subtype.ext he
  exact hcb ▸ hc

/-- The actual conjugation action of N(Y) on Y/O₂(Y). -/
def twoQuotientNormalizerAction (Y : Subgroup G) :
    normalizer (Y : Set G) →* MulAut (XiQuotient Y) :=
  (quotientAut (pCore 2 Y)).comp Y.normalizerMonoidHom

/-- The normalizer action commutes with the defining quotient map. -/
theorem twoQuotientNormalizerAction_mk (Y : Subgroup G)
    (s : normalizer (Y : Set G)) (y : Y) :
    twoQuotientNormalizerAction Y s (QuotientGroup.mk' (pCore 2 Y) y) =
      QuotientGroup.mk' (pCore 2 Y) (Y.normalizerMonoidHom s y) :=
  quotientAut_apply_mk (pCore 2 Y) (Y.normalizerMonoidHom s) y

/-- An element normalizing both B and Y preserves the actual quotient image of B. -/
theorem twoQuotientNormalizerAction_image {B Y : Subgroup G} (hBY : B ≤ Y)
    (s : normalizer (Y : Set G)) (hsB : (s : G) ∈ normalizer (B : Set G)) :
    (twoQuotientImage B Y).map (twoQuotientNormalizerAction Y s).toMonoidHom =
      twoQuotientImage B Y := by
  let α := Y.normalizerMonoidHom s
  let β := twoQuotientNormalizerAction Y s
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hA : (B.subgroupOf Y).map α.toMonoidHom = B.subgroupOf Y := by
    apply map_injective Y.subtype_injective
    have hc : Y.subtype.comp α.toMonoidHom =
        (MulAut.conj (s : G)).toMonoidHom.comp Y.subtype := by
      ext x
      exact normalizerMonoidHom_apply_apply_coe Y s x
    rw [map_map, hc, ← map_map, map_subgroupOf_eq_of_le hBY]
    exact mem_normalizer_iff_map_conj_eq.mp hsB
  have hc : β.toMonoidHom.comp q = q.comp α.toMonoidHom := by
    ext x
    exact quotientAut_apply_mk (pCore 2 Y) α x
  change ((B.subgroupOf Y).map q).map β.toMonoidHom = (B.subgroupOf Y).map q
  rw [map_map, hc, ← map_map, hA]

/-- Lift an inner conjugator from the image; its residual commutators lie in O₂(B). -/
theorem mem_innerTwoQuotientNormalizer_of_image_inner {B Y : Subgroup G}
    (hBY : B ≤ Y) (s : normalizer (Y : Set G))
    (hsB : (s : G) ∈ normalizer (B : Set G))
    (hinner : ∃ a ∈ twoQuotientImage B Y, ∀ x ∈ twoQuotientImage B Y,
      twoQuotientNormalizerAction Y s x = a * x * a⁻¹) :
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
    have hzker : (⟨⁅c, x⁆, hzB⟩ : B) ∈ (twoQuotientImageMap hBY).ker := by
      let q := QuotientGroup.mk' (pCore 2 Y)
      let xY : Y := inclusion hBY ⟨x, hx⟩
      let bY : Y := inclusion hBY b
      let α := Y.normalizerMonoidHom s
      have he := hact (twoQuotientImageMap hBY ⟨x, hx⟩) (mem_twoQuotientImage hBY ⟨x, hx⟩)
      change twoQuotientNormalizerAction Y s (q xY) = q bY * q xY * (q bY)⁻¹ at he
      rw [twoQuotientNormalizerAction_mk] at he
      have hz : inclusion hBY (⟨⁅c, x⁆, hzB⟩ : B) =
          bY⁻¹ * α xY * bY * xY⁻¹ := by
        apply Subtype.ext
        simp only [coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe,
          coe_inclusion, commutatorElement_def, c, xY, bY, α]
        group
      change q (inclusion hBY (⟨⁅c, x⁆, hzB⟩ : B)) = 1
      rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv, he]
      group
    exact mem_map_of_mem B.subtype (twoQuotientImageMap_ker_le hBY hzker)
  apply (mem_innerTwoQuotientNormalizer_iff B s).mpr
  exact ⟨b, b.property, c, hc, by dsimp [c]; group⟩

end CFSG.Quasithin.Chapter1.Terminal

namespace CFSG.Quasithin.Chapter1.Terminal
variable {G : Type*} [Group G]

/-- The surjection from B to its actual image in Y/O₂(Y). -/
def twoQuotientProjection {B Y : Subgroup G} (hBY : B ≤ Y) :
    B →* twoQuotientImage B Y :=
  (twoQuotientImageMap hBY).codRestrict _ (mem_twoQuotientImage hBY)

/-- The codomain restriction remains surjective. -/
theorem twoQuotientProjection_surjective {B Y : Subgroup G} (hBY : B ≤ Y) :
    Function.Surjective (twoQuotientProjection hBY) := by
  intro x
  obtain ⟨b, hb⟩ := exists_preimage_twoQuotientImage hBY x.property
  exact ⟨b, Subtype.ext hb⟩

/-- The restricted projection has exactly the intersection kernel. -/
theorem twoQuotientProjection_ker {B Y : Subgroup G} (hBY : B ≤ Y) :
    (twoQuotientProjection hBY).ker = (pCore 2 Y).comap (inclusion hBY) := by
  ext b
  change (twoQuotientProjection hBY b = 1) ↔ inclusion hBY b ∈ pCore 2 Y
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

/-- A two-core-free image identifies the projection kernel with O₂(B). -/
theorem twoQuotientProjection_ker_eq_core [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y)
    (hcore : pCore 2 (twoQuotientImage B Y) = ⊥) :
    (twoQuotientProjection hBY).ker = pCore 2 B := by
  have hp : IsPGroup 2 (twoQuotientProjection hBY).ker := by
    rw [twoQuotientProjection_ker]
    exact pCore_isPGroup.comap_of_injective (inclusion hBY) (inclusion_injective hBY)
  have he := (twoQuotientProjection hBY).comap_pCore_of_ker_isPGroup
    (twoQuotientProjection_surjective hBY) hp
  rw [hcore] at he
  exact he

/-- For a two-core-free image, O₂(B) is exactly B ∩ O₂(Y). -/
theorem core_eq_intersection_of_image_core_eq_bot [Finite G] {B Y : Subgroup G}
    (hBY : B ≤ Y) (hcore : pCore 2 (twoQuotientImage B Y) = ⊥) :
    B.pCoreIn 2 = B ⊓ Y.pCoreIn 2 := by
  apply le_antisymm ?_ (inf_pCoreIn_le_of_le 2 hBY)
  rintro x ⟨b, hb, rfl⟩
  refine ⟨b.property, inclusion hBY b, ?_, rfl⟩
  change b ∈ (pCore 2 Y).comap (inclusion hBY)
  rwa [← twoQuotientProjection_ker hBY, twoQuotientProjection_ker_eq_core hBY hcore]

/-- The first isomorphism theorem, with the kernel proved to be the intrinsic two-core. -/
noncomputable def twoQuotientImageEquiv [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y)
    (hcore : pCore 2 (twoQuotientImage B Y) = ⊥) :
    XiQuotient B ≃* twoQuotientImage B Y :=
  QuotientGroup.liftEquiv (pCore 2 B) (twoQuotientProjection_surjective hBY)
    (twoQuotientProjection_ker_eq_core hBY hcore).symm

/-- The quotient equivalence commutes with the actual inclusion and quotient maps. -/
theorem twoQuotientImageEquiv_mk [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y)
    (hcore : pCore 2 (twoQuotientImage B Y) = ⊥) (b : B) :
    twoQuotientImageEquiv hBY hcore (QuotientGroup.mk' (pCore 2 B) b) =
      twoQuotientProjection hBY b := rfl

/-- An intrinsic stabilizer theorem for the quotient image gives the ambient inner-action conclusion. -/
theorem le_innerTwoQuotientNormalizer_of_image_stabilizer {B Y S : Subgroup G}
    (hBY : B ≤ Y) (hSB : S ≤ normalizer (B : Set G))
    (hSY : S ≤ normalizer (Y : Set G))
    (hinner : (twoQuotientImage B Y).HasInnerStabilizerAction) :
    S ≤ innerTwoQuotientNormalizer B := by
  intro s hs
  exact mem_innerTwoQuotientNormalizer_of_image_inner hBY ⟨s, hSY hs⟩ (hSB hs)
    (hinner _ (twoQuotientNormalizerAction_image hBY ⟨s, hSY hs⟩ (hSB hs)))

/-- Transport a concrete model stabilizer theorem through the actual ambient quotient isomorphism. -/
theorem le_innerTwoQuotientNormalizer_of_model_stabilizer {Q : Type*} [Group Q]
    {B Y S : Subgroup G} (hBY : B ≤ Y) (hSB : S ≤ normalizer (B : Set G))
    (hSY : S ≤ normalizer (Y : Set G)) (e : XiQuotient Y ≃* Q)
    (hinner : ((twoQuotientImage B Y).map e.toMonoidHom).HasInnerStabilizerAction) :
    S ≤ innerTwoQuotientNormalizer B :=
  le_innerTwoQuotientNormalizer_of_image_stabilizer hBY hSB hSY (hinner.of_map e)

end CFSG.Quasithin.Chapter1.Terminal

namespace CFSG.Quasithin.Chapter1.Terminal
variable {G : Type*} [Group G]

/-- The quotient equivalence intertwines the two actual normalizer actions. -/
theorem twoQuotientImageEquiv_action [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y)
    (hcore : pCore 2 (twoQuotientImage B Y) = ⊥)
    (s : G) (hsB : s ∈ normalizer (B : Set G)) (hsY : s ∈ normalizer (Y : Set G))
    (x : XiQuotient B) :
    (twoQuotientImageEquiv hBY hcore (twoQuotientNormalizerAction B ⟨s, hsB⟩ x) :
        XiQuotient Y) =
      twoQuotientNormalizerAction Y ⟨s, hsY⟩ (twoQuotientImageEquiv hBY hcore x) := by
  induction x using Quotient.inductionOn with
  | h b =>
    rw [show (⟦b⟧ : XiQuotient B) = QuotientGroup.mk' (pCore 2 B) b from rfl,
      twoQuotientNormalizerAction_mk]
    rw [twoQuotientImageEquiv_mk, twoQuotientImageEquiv_mk]
    change QuotientGroup.mk' (pCore 2 Y)
      (inclusion hBY (B.normalizerMonoidHom ⟨s, hsB⟩ b)) =
      twoQuotientNormalizerAction Y ⟨s, hsY⟩ (QuotientGroup.mk' (pCore 2 Y) (inclusion hBY b))
    rw [twoQuotientNormalizerAction_mk]
    exact congrArg (QuotientGroup.mk' (pCore 2 Y)) (Subtype.ext (by
      simp only [coe_inclusion, normalizerMonoidHom_apply_apply_coe]))

end CFSG.Quasithin.Chapter1.Terminal
