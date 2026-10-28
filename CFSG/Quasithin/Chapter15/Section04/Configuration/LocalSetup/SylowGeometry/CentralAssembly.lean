module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.FixedSpaces
public import Stellmacher.BaumannNormalizer

/-!
# Central geometry from the source factor actions

For all four choices of the two factors, the raw internal decompositions and
conjugation actions construct the conclusions of 15.4.19. The order-four
central omega subgroup and its nontrivial centralizer of the whole X-factor
supply the lower bound for the common fixed space. Uniqueness of the two
maximal two-local overgroups gives both outside-factor statements and makes
this central omega subgroup disjoint from the center of the generated group.
The fixed-space calculation then supplies a nontrivial central two-subgroup
and the required intersection with the first commutator module.

The inputs are raw `Source.Geometry`, the explicit 15.4.14 and 15.4.16
conclusions, and displayed decomposition/action witnesses. The configuration
owner must realize every action witness from 15.4.12 and identify the supplied
modules with the source `V(M)`; no `Source.LocalData` is assumed or constructed.
This conditional result makes no assertion of the full Sylow theorem 15.4.20.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed p.1163, Lemma 15.4.19.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Normalizing `T` preserves its actual Thompson omega center. -/
theorem normalizer_le_normalizer_thompsonAlpha (T : Subgroup G) :
    normalizer (T : Set G) ≤ normalizer (ChapterB.thompsonAlpha T : Set G) := by
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq] at ht ⊢
  change T.map (MulAut.conj t).toMonoidHom = T at ht
  change (Stellmacher.omegaOneCenterAmbient (Stellmacher.elementaryAbelianMaxJ T)).map
    (MulAut.conj t).toMonoidHom = _
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective,
    ← Stellmacher.elementaryAbelianMaxJ_map_equiv, ht]
  rfl

/-- The conclusions of 15.4.19 from explicit factor-action witnesses. These are
raw internal decompositions and conjugation statements for the actual commutator
modules. In particular no fixed hyperplane, fixed-line order, central intersection,
or membership in `H` is assumed. Realizing the raw action witnesses from the full
15.4.12 construction remains the configuration owner's obligation. -/
theorem central_geometry_from_factor_actions
    (d : Source.Geometry G)
    (hZ : d.Z = Stellmacher.omegaOneCenterAmbient (d.T : Subgroup G))
    (hZcard : Nat.card d.Z = 4)
    (hCZ : d.Z ⊓ centralizer (d.wholeX : Set G) ≠ ⊥)
    (hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀)
    (hTX : (d.T : Subgroup G) ≤ d.M₁) (hTY : (d.T : Subgroup G) ≤ d.M₂)
    (hM₁ : IsMaximalTwoLocal d.M₁) (hM₂ : IsMaximalTwoLocal d.M₂)
    (hXgen : ∀ i, d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G))
    (hYgen : ∀ j, d.Y j ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂)
    (hne : d.M₁ ≠ d.M₂)
    (hfactor : ∀ side : Bool,
      let L := if side then d.Y else d.X
      let V := if side then d.V₂ else d.V₁
      let E := ChapterB.thompsonAlpha (d.T : Subgroup G)
      let S := ChapterB.baumann (d.T : Subgroup G)
      let C := E ⊓ centralizer ((L false ⊔ L true : Subgroup G) : Set G)
      (∀ i, V i ≤ S) ∧
      (∀ i, d.T₀ ≤ normalizer (V i : Set G)) ∧
      (∀ i, V i ≠ ⊥) ∧
      V false ≤ centralizer (V true : Set G) ∧
      Disjoint (V false) (V true) ∧
      Disjoint C (V false ⊔ V true) ∧
      C ⊔ ((V false ⊔ V true) ⊓ centralizer (S : Set G)) = E ∧
      C.relIndex E = 4 ∧
      (∀ i, V (!i) ≤ centralizer (L i : Set G)) ∧
      (V false ⊔ V true) ⊓
        centralizer ((L false ⊔ L true : Subgroup G) : Set G) = ⊥) :
    (∀ i, ¬ d.X i ≤ d.M₂) ∧ (∀ j, ¬ d.Y j ≤ d.M₁) ∧
    ∀ i j,
      ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.I i j : Set G) ≠ ⊥ ∧
      ChapterB.thompsonAlpha (d.T : Subgroup G) ⊓ centralizer (d.I i j : Set G) ≤
        (center (d.I i j)).map (d.I i j).subtype ∧
      d.I i j ∈ Chapter1.H G ∧
      d.Z ⊓ ((center (d.I i j)).map (d.I i j).subtype ⊔ d.V₁ i) ≠ ⊥ := by
  let E := ChapterB.thompsonAlpha (d.T : Subgroup G)
  let S := ChapterB.baumann (d.T : Subgroup G)
  let : IsElementaryAbelian 2 E :=
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hSp : IsPGroup 2 S := d.T.isPGroup'.to_le inf_le_left
  have hSn : d.T₀ ≤ normalizer (S : Set G) := d.T₀_le_T.trans
    (le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann _))
  have hEn : d.T₀ ≤ normalizer (E : Set G) := d.T₀_le_T.trans
    (le_normalizer.trans (normalizer_le_normalizer_thompsonAlpha _))
  have hnorm (L : Subgroup G) (hn : (d.T : Subgroup G) ≤ normalizer (L : Set G)) :
      d.T₀ ≤ normalizer ((E ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    (le_inf hEn (d.T₀_le_T.trans (hn.trans (normalizer_le_normalizer_centralizer L)))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨hVSX, hnVX, hVneX, hcommX, hdisX, hCdisX, hEX, hindexX, hcrossX, hfreeX⟩ := hfactor false
  obtain ⟨hVSY, hnVY, hVneY, hcommY, hdisY, hCdisY, hEY, hindexY, hcrossY, hfreeY⟩ := hfactor true
  obtain ⟨hfixedX, hcardX⟩ := two_factor_fixed_geometry d.V₁ d.X hSp hS hVSX hnVX hVneX
    hSn (hnorm d.wholeX hTX) hcommX hdisX hCdisX hEX hindexX inf_le_right hcrossX hfreeX
  obtain ⟨hfixedY, _⟩ := two_factor_fixed_geometry d.V₂ d.Y hSp hS hVSY hnVY hVneY
    hSn (hnorm d.wholeY hTY) hcommY hdisY hCdisY hEY hindexY inf_le_right hcrossY hfreeY
  have hZE : d.Z ≤ E := hZ ▸ TwoFactors.centralOmega_le_thompsonAlpha _
  have hZU : d.Z ≤ centralizer (d.T₀ : Set G) := by
    intro z hz
    rw [hZ] at hz
    exact mem_centralizer_iff.mpr fun t ht =>
      ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t (d.T₀_le_T ht)
  have hlarge : 4 < Nat.card (E ⊓ centralizer (d.T₀ : Set G) : Subgroup G) := by
    have hsmall := (one_lt_card_iff_ne_bot _).mpr hCZ
    have hle : d.Z ⊓ centralizer (d.wholeX : Set G) ≤
        (E ⊓ centralizer (d.wholeX : Set G)) ⊓ centralizer (d.T₀ : Set G) :=
      le_inf (inf_le_inf_right _ hZE) (inf_le_left.trans hZU)
    have hc := card_le_of_le hle
    change Nat.card (E ⊓ centralizer (d.T₀ : Set G) : Subgroup G) =
      Nat.card ((E ⊓ centralizer (d.wholeX : Set G)) ⊓ centralizer (d.T₀ : Set G) : Subgroup G) * 4 at hcardX
    omega
  obtain ⟨hx, hy⟩ := outside_factors d hXgen hYgen huniqueX huniqueY hM₁ hM₂ hTX hTY hne
  refine ⟨hx, hy, fun i j => ?_⟩
  exact central_geometry_of_fixed_hyperplanes d hS hZcard i j (le_inf hZE hZU)
    (center_image_disjoint_Z d hZ hXgen hYgen huniqueX huniqueY hne i j) hlarge
    (hfixedX i).1 (hfixedY j).1 (hfixedX i).2.1 (hfixedX i).2.2.1 (hfixedX i).2.2.2

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
