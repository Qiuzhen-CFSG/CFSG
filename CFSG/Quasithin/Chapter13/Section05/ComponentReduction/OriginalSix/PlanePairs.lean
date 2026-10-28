module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonal
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.PlaneTransport
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.PlaneClosure
public import CFSG.Quasithin.Chapter13.Section05.LocalGeometry.NonabelianClosure
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The original local two-group pair condition

F.9 reduces a non-two pair's intersection to the seed. The point residual
moves its two aligned planes to the original V₂, so their combined
conjugator normalizes V₂. The actual G.2 application there makes the
conjugate module normalize V. Their join is therefore a two-group.
This supplies the literal pair premise used in13.5.20 without global
plane fusion. Source: Aschbacher–Smith13.5.13 and13.5.20, pp.919,923.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
include d h

private theorem plane_pair_two
    (hU : ¬IsMulCommutative D.UH)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.conjBy l)
    (hN : ∀ n ∈ normalizer (V₂ : Set G),
      D.V.conjBy n ≤ normalizer (D.V : Set G))
    {k : G} (hk : k ∈ D.H) (hplane : V₂ ≤ D.V ⊓ D.V.conjBy k) :
    IsPGroup 2 (D.V ⊔ D.V.conjBy k : Subgroup G) := by
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  have hinv : (D.V ⊔ D.V.conjBy k⁻¹).conjBy k = D.V ⊔ D.V.conjBy k := by
    change (D.V ⊔ D.V.conjBy k⁻¹).map _ = _
    rw [Subgroup.map_sup]
    change D.V.conjBy k ⊔ (D.V.conjBy k⁻¹).conjBy k = _
    rw [conjBy_inv',sup_comm]
  rcases LocalGeometry.conjugate_pair_reduction h hi hU (D.H.inv_mem hk) with hp | hs
  · have hm := hp.map (MulAut.conj k).toMonoidHom
    change IsPGroup 2 ((D.V ⊔ D.V.conjBy k⁻¹).conjBy k) at hm
    rwa [hinv] at hm
  let W := V₂.conjBy k⁻¹
  have hWcard : Nat.card W = 4 := by
    dsimp only [W,conjBy]
    rw [card_map_of_injective (MulAut.conj k⁻¹).injective,d.plane_card]
  have hfix : D.V₁.conjBy k⁻¹ = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp
      ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) (D.H.inv_mem hk))
  have hPW : D.V₁ ≤ W := by
    rw [←hfix]
    exact map_mono d.line_le_plane
  have hPWlt : D.V₁ < W := lt_of_le_of_ne hPW (by
    intro he
    have hc := congrArg (fun A : Subgroup G => Nat.card A) he
    rw [d.line_card,hWcard] at hc
    omega)
  have hWI : W ≤ D.V ⊓ D.V.conjBy k⁻¹ := by
    have hm := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hplane
    change W ≤ (D.V ⊓ D.V.conjBy k).map _ at hm
    rw [map_inf _ _ _ (MulAut.conj k⁻¹).injective] at hm
    change W ≤ D.V.conjBy k⁻¹ ⊓ (D.V.conjBy k).conjBy k⁻¹ at hm
    rwa [conjBy_inv,inf_comm] at hm
  obtain ⟨r,hr,hrW⟩ := hmove W hPWlt (hWI.trans hs)
  have he : W.conjBy r = V₂ := (eq_of_le_of_card_ge hrW (by
    change Nat.card (W.map _) ≤ Nat.card V₂
    rw [card_map_of_injective (MulAut.conj r).injective,hWcard,d.plane_card])).symm
  have hn : r * k⁻¹ ∈ normalizer (V₂ : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change V₂.conjBy (r * k⁻¹) = V₂
    rwa [conjBy_mul]
  have hrV : r⁻¹ ∈ normalizer (D.V : Set G) := by
    apply (normalizer (D.V : Set G)).inv_mem
    exact ((((map_subtype_le _).trans inf_le_left).trans le_sup_left).trans d.normalizes_V) hr
  have hkV : D.V.conjBy k ≤ normalizer (D.V : Set G) := by
    have hh := hN (r * k⁻¹)⁻¹ ((normalizer (V₂ : Set G)).inv_mem hn)
    have hre : D.V.conjBy r⁻¹ = D.V := mem_normalizer_iff_map_conj_eq.mp hrV
    rw [mul_inv_rev,inv_inv,conjBy_mul,hre] at hh
    exact hh
  exact h.elementary.isPGroup.to_sup_of_normal_left'
    (h.elementary.isPGroup.map (MulAut.conj k).toMonoidHom) hkV

/-- The local F.9 pair condition needs only actual plane-normalizer control.
The contrary pair intersects in the seed on both sides, so the point
residual aligns its two planes inside that seed. -/
theorem twoGroup_pairs_of_plane_normalizer
    (hU : ¬IsMulCommutative D.UH)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.conjBy l)
    (hN : ∀ n ∈ normalizer (V₂ : Set G),
      D.V.conjBy n ≤ normalizer (D.V : Set G))
    {g : G} (hg : g ∈ D.H)
    (hinter : D.V₁ < D.V ⊓ D.V.conjBy g) :
    IsPGroup 2 (D.V ⊔ D.V.conjBy g : Subgroup G) := by
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  rcases LocalGeometry.conjugate_pair_reduction h hi hU hg with hp | hs
  · exact hp
  obtain ⟨r,hr,hW⟩ := hmove _ hinter hs
  have hn : D.L₁ ≤ normalizer (D.V : Set G) :=
    (((map_subtype_le _).trans inf_le_left).trans le_sup_left).trans d.normalizes_V
  have hrV : D.V.conjBy r = D.V := mem_normalizer_iff_map_conj_eq.mp (hn hr)
  have hplane : V₂ ≤ D.V ⊓ D.V.conjBy (r*g) := by
    change V₂ ≤ (D.V ⊓ D.V.conjBy g).map _ at hW
    rw [map_inf _ _ _ (MulAut.conj r).injective] at hW
    change V₂ ≤ D.V.conjBy r ⊓ (D.V.conjBy g).conjBy r at hW
    rwa [hrV,conjBy_conjBy] at hW
  have hp := plane_pair_two d h hU hmove hN
    (D.H.mul_mem (h.local_le (mem_sup_left hr)) hg) hplane
  have he : (D.V ⊔ D.V.conjBy g).conjBy r = D.V ⊔ D.V.conjBy (r*g) := by
    change (D.V ⊔ D.V.conjBy g).map _ = _
    rw [Subgroup.map_sup]
    change D.V.conjBy r ⊔ (D.V.conjBy g).conjBy r = _
    rw [hrV,conjBy_conjBy]
  rw [←he] at hp
  exact hp.of_equiv ((D.V ⊔ D.V.conjBy g).equivMapOfInjective
    (MulAut.conj r).toMonoidHom (MulAut.conj r).injective).symm
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix

namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Subgroup Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
/-- The literal pair condition for the selected F.9 application, from
point-residual transport and the original G.2 plane-normalizer action. -/
theorem twoGroup_pairs
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
    (hU : ¬IsMulCommutative D.UH) {g : G} (hg : g ∈ D.H)
    (hinter : D.V₁ < D.V ⊓ D.V.conjBy g) :
    IsPGroup 2 (D.V ⊔ D.V.conjBy g : Subgroup G) := by
  apply twoGroup_pairs_of_plane_normalizer d h hU
    (fun W hW hWU => plane_transport d h W hW hWU) ?_ hg hinter
  intro n hn
  exact (PlaneGeometry.source_plane_normalizer_conjugate d n hn).1
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
