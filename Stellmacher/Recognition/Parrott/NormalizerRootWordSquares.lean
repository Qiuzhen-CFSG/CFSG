module

public import Stellmacher.Recognition.Parrott.NormalizerRootWordSquareCoordinates
public import Stellmacher.Recognition.Parrott.NormalizerRootWordSquareCollection
public import Theory.GroupTheory.ElementaryCosetSquareBound

/-!
# Transferring the finite square calculation to Parrott's words

The finite square map has sixteen roots of each relevant square and eight
with a fixed head. Faithful ambient evaluation transfers these counts to K
and to an elementary coset. The disjoint cosets mF and m⁻¹F saturate the
sixteen-root bound, which proves the two-coset geometry.

Faithful coordinates and the omega test are proved from the supplied frame
and word injectivity. The ambient evaluation of the square table then gives
the word calculation without any additional collection hypotheses.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottNormalizerRootSquare
variable {G : Type*} [Group G] [Finite G]

/-- Transfer the finite square certificate through faithful ambient word
coordinates. The hypotheses separate coordinate geometry from word collection. -/
public theorem geometry_of_square_model
    (F K U : Subgroup G) [IsElementaryAbelian 2 F] (hFK : F ≤ K)
    (w : Code → G) (hinj : Function.Injective w)
    (hzero : w (0,0,0) = 1) (hcover : Set.range w = (K : Set G))
    (hF : ∀ p, w p ∈ F ↔ p.1 = 0)
    (hcoset : ∀ p q, (w p)⁻¹ * w q ∈ F ↔ p.1 = q.1)
    (hsquare : ∀ p, w (square p) = (w p) ^ 2)
    (houtside : ∀ p, w p ∉ U → outside p.1)
    (p : Code) (hpU : w p ∉ U) (hp4 : orderOf (w p) = 4) :
    (w p) ^ 2 ∉ F ∧
    Nat.card (F ⊓ centralizer ({w p} : Set G) : Subgroup G) = 8 ∧
    ∀ q : Code, (w q) ^ 2 = (w p) ^ 2 →
      (w p)⁻¹ * w q ∈ F ∨ w p * w q ∈ F := by
  have hfour : (w p) ^ 4 = 1 := hp4 ▸ pow_orderOf_eq_one (w p)
  have hmodel4 : square (square p) = (0,0,0) := hinj (by
    rw [hsquare, hsquare, ← pow_mul, hzero]
    exact hfour)
  have hsel : selected p.1 := selected_of_fourth_power
    (p.1,p.2.1) (houtside p hpU) hmodel4
  have hsq : (w p) ^ 2 ∉ F := by
    rw [← hsquare, hF]
    exact (small_fiber_counts (p.1,p.2.1) hsel).1
  have hmem (q : Code) : w q ∈ K := by
    change w q ∈ (K : Set G)
    rw [← hcover]
    exact ⟨q,rfl⟩
  have hroot (q : Code) : square q = square p ↔ (w q) ^ 2 = (w p) ^ 2 := by
    rw [← hsquare, ← hsquare]
    exact hinj.eq_iff.symm
  let T := {q : Fin 8 × Fin 4 // square (p.1,q) = square p}
  let C := {g : G // (w p)⁻¹ * g ∈ F ∧ g ^ 2 = (w p) ^ 2}
  let ψ : T → C := fun q => ⟨w (p.1,q.val),
    (hcoset p (p.1,q.val)).mpr rfl, (hroot _).mp q.property⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact congrArg Prod.snd (hinj (congrArg Subtype.val hab))
    · intro g
      have hgK : g.val ∈ K := by
        have hh := K.mul_mem (hmem p) (hFK g.property.1)
        simpa only [mul_inv_cancel_left] using hh
      have hgW : g.val ∈ Set.range w := by rw [hcover]; exact hgK
      obtain ⟨q,hq⟩ := hgW
      have hh : p.1 = q.1 := (hcoset p q).mp (hq.symm ▸ g.property.1)
      refine ⟨⟨q.2, ?_⟩, ?_⟩
      · have hqp : (p.1,q.2) = q := Prod.ext hh rfl
        rw [hqp]
        exact (hroot q).mpr (hq.symm ▸ g.property.2)
      · apply Subtype.ext
        change w (p.1,q.2) = g.val
        simpa only [hh] using hq
  have hc : Nat.card (F ⊓ centralizer ({w p} : Set G) : Subgroup G) = 8 := by
    rw [← Nat.card_congr (squareCosetEquivCentralizer F (w p)),
      ← Nat.card_congr (Equiv.ofBijective ψ hψ)]
    exact coset_root_card p hsel
  have hbound : {g : G | g ∈ K ∧ g ^ 2 = (w p) ^ 2}.ncard ≤ 16 := by
    let R := {g : G // g ∈ K ∧ g ^ 2 = (w p) ^ 2}
    let φ : {q : Code // square q = square p} → R := fun q =>
      ⟨w q.val, hmem q.val, (hroot q.val).mp q.property⟩
    have hφ : Function.Surjective φ := by
      intro g
      have hgW : g.val ∈ Set.range w := by rw [hcover]; exact g.property.1
      obtain ⟨q,hq⟩ := hgW
      exact ⟨⟨q,(hroot q).mpr (hq.symm ▸ g.property.2)⟩, Subtype.ext hq⟩
    have hh := Nat.card_le_card_of_surjective φ hφ
    rw [root_card p hsel] at hh
    exact hh
  refine ⟨hsq,hc,fun q hq => ?_⟩
  exact square_roots_mem_two_cosets_of_ncard_le F K hFK (w p) (hmem p) hfour hsq
    (by simpa only [hc] using hbound) (w q) (hmem q) hq


/-- The exact ordered-word calculation, reduced to independent coordinate
and collection identities. The supplied word injectivity remains an explicit
input, as in the parent geometry assembly. -/
public theorem word_calculation_of_square_laws {z : G}
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowGeneratorData n) (hinj : Function.Injective f.normalizerRootWord)
    (hc : CoordinateLaws f) (hs : SquareLaws f)
    (p : f.NormalizerRootParameters)
    (hpU : f.normalizerRootWord p ∉
      (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
        ((normalizer (e.F : Set G)).subtype.comp
          (pCore 2 (normalizer (e.F : Set G))).subtype))
    (hp4 : orderOf (f.normalizerRootWord p) = 4) :
    (f.normalizerRootWord p) ^ 2 ∉ e.F ∧
    Nat.card (e.F ⊓ centralizer ({f.normalizerRootWord p} : Set G) : Subgroup G) = 8 ∧
    ∀ q : f.NormalizerRootParameters,
      (f.normalizerRootWord q) ^ 2 = (f.normalizerRootWord p) ^ 2 →
      (f.normalizerRootWord p)⁻¹ * f.normalizerRootWord q ∈ e.F ∨
        f.normalizerRootWord p * f.normalizerRootWord q ∈ e.F := by
  let _ := e.elementary
  have he (q : f.NormalizerRootParameters) :
      ∃ r : Code, word f r = f.normalizerRootWord q := by
    change f.normalizerRootWord q ∈ Set.range (word f)
    rw [hc.range_eq_words]
    exact ⟨q,rfl⟩
  obtain ⟨r,hr⟩ := he p
  have hgeom := geometry_of_square_model e.F
    ((pCore 2 (normalizer (e.F : Set G))).map (normalizer (e.F : Set G)).subtype)
    ((omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
      ((normalizer (e.F : Set G)).subtype.comp
        (pCore 2 (normalizer (e.F : Set G))).subtype))
    (n.elementary_le_omega.trans n.omega_le_core) (word f) hc.injective
    (word_zero f) (hc.range_eq_words.trans (f.normalizerRootWord_range_of_injective hinj))
    hc.elementary hc.coset hs.square_eval hs.outside_omega r
    (hr.symm ▸ hpU) (hr.symm ▸ hp4)
  rw [hr] at hgeom
  refine ⟨hgeom.1,hgeom.2.1,fun q hq => ?_⟩
  obtain ⟨s,hs'⟩ := he q
  have hh := hgeom.2.2 s (by rw [hs']; exact hq)
  simpa only [hs'] using hh

/-- All three requested word-geometry conclusions follow from the single
remaining collection identity for squares. Coordinate geometry and the omega
test are proved from the supplied frame and explicit word injectivity. -/
public theorem word_calculation_of_square_eval {z : G}
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowGeneratorData n) (hinj : Function.Injective f.normalizerRootWord)
    (hsquare : ∀ p : Code, word f (square p) = (word f p) ^ 2)
    (p : f.NormalizerRootParameters)
    (hpU : f.normalizerRootWord p ∉
      (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
        ((normalizer (e.F : Set G)).subtype.comp
          (pCore 2 (normalizer (e.F : Set G))).subtype))
    (hp4 : orderOf (f.normalizerRootWord p) = 4) :
    (f.normalizerRootWord p) ^ 2 ∉ e.F ∧
    Nat.card (e.F ⊓ centralizer ({f.normalizerRootWord p} : Set G) : Subgroup G) = 8 ∧
    ∀ q : f.NormalizerRootParameters,
      (f.normalizerRootWord q) ^ 2 = (f.normalizerRootWord p) ^ 2 →
      (f.normalizerRootWord p)⁻¹ * f.normalizerRootWord q ∈ e.F ∨
        f.normalizerRootWord p * f.normalizerRootWord q ∈ e.F := by
  exact word_calculation_of_square_laws f hinj (coordinateLaws f hinj)
    ⟨hsquare, outside_omega f⟩ p hpU hp4

/-- The square geometry of every ordered word outside omega of order four.
This is the exact calculation premise of
`ParrottSylowGeneratorData.normalizer_root_geometry_of_word_calculation`.
Only the Sylow frame and explicit word injectivity are needed. -/
public theorem word_calculation {z : G}
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowGeneratorData n) (hinj : Function.Injective f.normalizerRootWord)
    (p : f.NormalizerRootParameters)
    (hpU : f.normalizerRootWord p ∉
      (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
        ((normalizer (e.F : Set G)).subtype.comp
          (pCore 2 (normalizer (e.F : Set G))).subtype))
    (hp4 : orderOf (f.normalizerRootWord p) = 4) :
    (f.normalizerRootWord p) ^ 2 ∉ e.F ∧
    Nat.card (e.F ⊓ centralizer ({f.normalizerRootWord p} : Set G) : Subgroup G) = 8 ∧
    ∀ q : f.NormalizerRootParameters,
      (f.normalizerRootWord q) ^ 2 = (f.normalizerRootWord p) ^ 2 →
      (f.normalizerRootWord p)⁻¹ * f.normalizerRootWord q ∈ e.F ∨
        f.normalizerRootWord p * f.normalizerRootWord q ∈ e.F := by
  exact word_calculation_of_square_eval f hinj (square_eval f) p hpU hp4

end Stellmacher.Recognition.ParrottNormalizerRootSquare
