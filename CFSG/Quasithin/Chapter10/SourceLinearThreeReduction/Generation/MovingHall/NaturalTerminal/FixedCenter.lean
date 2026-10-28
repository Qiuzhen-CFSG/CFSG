module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HallNontrivial
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.FixedCenter
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.Quotient
public import Theory.Representation.BinaryConjugationSection.PairedOddFixed

/-!
# Fixed-center elimination for the original odd Hall subgroup

The original Hall is nontrivial, and its image in the marked quotient
L₀/O₂(L₀) has a nontrivial natural factor. The Sylow exchanger identifies
the two coordinates of an element of Ω₁Z(T), even with the original
central-alpha supplement retained. The odd fixed-point calculation then
identifies C_Z(B_H) with C_Z(L₀). Since B_H lies in the original H, maximal
local uniqueness eliminates C_Z(H).

This is the general-field fixed-center step of 10.2.3(4), printed p.746.
The paired-section and seed-split constructions remain with the moving-Hall
assembly owner. Vanishing of C_Z(L₀) additionally needs the comparison
component's natural action; it is not asserted here.
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
local instance fixedCenterFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Construct the actual paired quotient and coordinate maps, with the
same marking on both original components and a nontrivial original Hall image. -/
theorem Context.exists_marked_natural_pair (ctx : Context D H B)
    (hB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ (eR : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
      (q₁ q₂ : localOrbit T L →* SL(2,F)),
      (∀ x : localOrbit T L,
        eR (QuotientGroup.mk' (pCore 2 (localOrbit T L)) x) = (q₁ x,q₂ x)) ∧
      (∀ l : L, eR (QuotientGroup.mk' _ ⟨l,le_componentOrbit L T l.property⟩) =
        (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, eR (QuotientGroup.mk' _ (originalConjugateOrbitInclusion ht l)) =
        (1,e (QuotientGroup.mk' _ l))) ∧
      ¬ (B.map H.subtype).subgroupOf (localOrbit T L) ≤ q₁.ker ⊓ q₂.ker := by
  obtain ⟨eR,hfirst,hsecond⟩ :=
    source_original_natural_pair_quotient D n hn hF e ctx.nonnormal ht htn
  let q := eR.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))
  let q₁ := (MonoidHom.fst SL(2,F) SL(2,F)).comp q
  let q₂ := (MonoidHom.snd SL(2,F) SL(2,F)).comp q
  have he : ∀ x : localOrbit T L,
      eR (QuotientGroup.mk' (pCore 2 (localOrbit T L)) x) = (q₁ x,q₂ x) := fun _ => rfl
  have hBR : B.map H.subtype ≤ localOrbit T L := hB.trans
    ((map_subtype_le (pResidual 2 (sourceOrbitSylowNormalizer T L))).trans inf_le_left)
  exact ⟨eR,q₁,q₂,he,hfirst,hsecond,ctx.hall_not_le_pair_kernel eR q₁ q₂ he hBR⟩

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
theorem source_original_hall_fixed_center (ctx : Context D H B)
    (hB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (e : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
    (q₁ q₂ : localOrbit T L →* SL(2,F))
    (he : ∀ x : localOrbit T L,
      e (QuotientGroup.mk' (pCore 2 (localOrbit T L)) x) = (q₁ x,q₂ x))
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
  have hBR : B.map H.subtype ≤ localOrbit T L := hB.trans
    ((map_subtype_le (pResidual 2 (sourceOrbitSylowNormalizer T L))).trans inf_le_left)
  let P := (B.map H.subtype).subgroupOf (localOrbit T L)
  have hodd : Odd (Nat.card P) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv]
    exact ctx.odd_card_of_le_hall_image _ le_rfl
  have hne := ctx.hall_not_le_pair_kernel e q₁ q₂ he hBR
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

end CFSG.Quasithin.Chapter10.MovingHall
