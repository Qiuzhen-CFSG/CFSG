module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.PairedCoordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.FixedCenter

/-!
# Original odd-Hall fixed centers with the paired inputs discharged

The original general-field component and moving H-star context now supply
the paired coordinate maps, their Sylow exchanger, and the central-alpha
seed bound. Their joint action kernel is a two-group, so the nontrivial
original odd Hall has a nontrivial natural-factor image. Its fixed points
on Ω₁Z(T) are exactly those of L₀. Maximal-local uniqueness then proves
C_{Ω₁Z(T)}(H)=1.

Only containment of the original Hall in L₀ is required here; the earlier
Hall-placement argument must still establish its stronger Borel bound.
Vanishing of C_{Ω₁Z(T)}(L₀) still needs the comparison component action.
Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {B : Subgroup H}
variable {F : Type*} [Field F] [CharP F 2]
local instance originalFixedCenterFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite G] in
private theorem sylow_normalizes_central_alpha :
    (T : Subgroup G) ≤ normalizer
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) : Set G) := by
  have hTa : (T : Subgroup G) ≤ normalizer (thompsonAlpha (T : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G))).map
      (MulAut.conj t).toMonoidHom = _
    have hT : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective,
      ←elementaryAbelianMaxJ_map_equiv,hT]
    rfl
  exact (le_inf hTa ((le_normalizer_componentOrbit L T).trans
    (normalizer_le_normalizer_centralizer (localOrbit T L)))).trans
      inf_normalizer_le_normalizer_inf

/-- The literal odd Hall and natural pair eliminate the original H-star
fixed center without selecting a cubic or splitting the central cover. -/
private theorem hall_fixed_center_of_two_kernel (ctx : Context D H B)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (q₁ q₂ : localOrbit T L →* SL(2,F))
    (htwo : IsPGroup 2 (q₁.ker ⊓ q₂.ker : Subgroup (localOrbit T L)))
    (c : BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
      (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤
      ⁅D.moduleSubgroup,localOrbit T L⁆ ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : D.moduleSubgroup,
      ((c.coordinates ⟨t * a * t⁻¹,
        (mem_normalizer_iff.mp (D.sylow_normalizes_module ht) a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B.map H.subtype : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ∧
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ := by
  let P := (B.map H.subtype).subgroupOf (localOrbit T L)
  have hodd : Odd (Nat.card P) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv]
    exact ctx.odd_card_of_le_hall_image _ le_rfl
  have hne : ¬ P ≤ q₁.ker ⊓ q₂.ker := by
    intro hle
    have hcard : Nat.card P = 1 := (htwo.to_le hle).card_eq_or_dvd.resolve_right hodd.not_two_dvd_nat
    have hbot : P = ⊥ := Subgroup.card_eq_one.mp hcard
    apply ctx.hall_image_ne_bot
    have hm := congrArg (map (localOrbit T L).subtype) hbot
    simpa only [P,map_subgroupOf_eq_of_le hBR,Subgroup.map_bot] using hm
  have hfixed := c.paired_natural_odd_fixed_eq_of_central_supplement q₁ q₂ inf_le_right
    (omegaOneCenterAmbient (T : Subgroup G))
    (hZ.trans (sup_le_sup (le_normalizer_iff_commutator_le_left.mp D.orbit_normalizes_module) le_rfl))
    t (D.sylow_normalizes_module ht) (sylow_normalizes_central_alpha ht)
    (show omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer ({t} : Set G) from by
      intro z hz y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht)
    f hswap P hodd hne
  dsimp only [P] at hfixed
  rw [map_subgroupOf_eq_of_le hBR] at hfixed
  refine ⟨hfixed,source_hstar_fixed_center_eq_bot_of_le D ctx.hstar ?_⟩
  exact ((inf_le_inf_left _ (centralizer_le (map_subtype_le B))).trans hfixed.le).trans inf_le_right

/-- The actual general-field moving context discharges every paired-module,
seed-splitting and exchanger premise in the original Hall fixed-center step. -/
theorem Context.original_hall_fixed_center [Finite F]
    (ctx : Context D H B) (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B.map H.subtype : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ∧
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ := by
  obtain ⟨⟨E,q₁,q₂,c,htwo,t,f,hswap⟩,hZ⟩ :=
    ctx.original_paired_coordinates_and_seed D n hn hF e
  exact hall_fixed_center_of_two_kernel ctx hBR q₁ q₂ htwo c hZ t.property f hswap

end CFSG.Quasithin.Chapter10.MovingHall
