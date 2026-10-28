module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.BorelLift
public import Theory.Representation.HigherFieldBorelFixedSpaces.Sylow

/-!
# The source Borel contradiction on natural coordinates

Each component Sylow normalizer lifts through the literal action quotient to
H ∩ M. Its two-perfectness makes those lifts centralize V under the original
residual-centralizer hypothesis. Hence every such normalizer fixes a quotient
seed that comes from V. A natural SL₂ coordinate over a field of order at least
four must therefore vanish. Applying this to one natural coordinate, or both
coordinates of a paired natural module, gives the field-exclusion contradiction.

This module proves the coordinate-vanishing step; identifying the essential
simple quotient's natural coordinates is a separate chief-matching argument.
Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof of 3.1.9(5), printed p.578.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3
open ChapterB Theory.GroupTheory HigherFieldBorelFixedSpaces
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.component_sylowNormalizer_lifts_fixing_module
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    {L : Subgroup D} (hL : IsComponent D L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L)
    (P : Sylow 2 L) (hPS : (P : Subgroup L) =
      (((T.subtype h.right_mem.1.1.2).mapSurjective hq : Sylow 2 D) : Subgroup D).subgroupOf L)
    (hB : IsPPerfect 2 (normalizer (P : Set L))) :
    ∀ b ∈ normalizer (P : Set L), ∃ x : H, q x = (b : D) ∧
      (x : G) ∈ centralizer (V : Set G) := by
  let S := (T.subtype h.right_mem.1.1.2).mapSurjective hq
  let B := (normalizer (P : Set L)).map L.subtype
  have hperf : IsPPerfect 2 B := hB.of_surjective
    ((normalizer (P : Set L)).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom
    ((normalizer (P : Set L)).equivMapOfInjective L.subtype L.subtype_injective).surjective
  have hBL : B ≤ L ⊓ normalizer ((S : Subgroup D) ⊓ L : Set D) := by
    refine le_inf (map_subtype_le _) ?_
    have hn := (P : Subgroup L).le_normalizer_map L.subtype
    have he : (P : Subgroup L).map L.subtype = (S : Subgroup D) ⊓ L := by
      rw [hPS]
      change ((S : Subgroup D).subgroupOf L).map L.subtype = _
      rw [← inf_subgroupOf_right (S : Subgroup D) L,
        map_subgroupOf_eq_of_le (inf_le_right : (S : Subgroup D) ⊓ L ≤ L)]
    exact hn.trans_eq (congrArg (fun A : Subgroup D => normalizer (A : Set D)) he)
  intro b hb
  exact h.twoPerfect_component_image_lifts_fixing_module hP hres q hq hc hn
    hL heven B hperf hBL b (mem_map_of_mem L.subtype hb)
end CFSG.Quasithin.Chapter3

namespace CFSG.Quasithin.Chapter3
open ChapterB Theory.GroupTheory HigherFieldBorelFixedSpaces
variable {G D W F : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.natural_component_fixed_seed_coordinate_zero
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (v : W)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    {L : Subgroup D} (hL : IsComponent D L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L) (hF : 4 ≤ Nat.card F)
    (e : L ≃* SL(2,F)) (f : W →ₗ[ZMod 2] (Fin 2 → F))
    (hf : ∀ (g : L) w, f (ρ (g : D) w) = binaryNatural 2 (e g) (f w)) :
    f v = 0 := by
  let S := (T.subtype h.right_mem.1.1.2).mapSurjective hq
  obtain ⟨P,hPS⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.1
  obtain ⟨hB,hfix⟩ := natural_sylowNormalizer hF P (ρ.comp L.subtype) e f hf
  apply hfix v
  intro b
  obtain ⟨x,hx,hxc⟩ := h.component_sylowNormalizer_lifts_fixing_module hP hres q hq hc hn
    hL heven P hPS hB b b.property
  change ρ (b : L) v = v
  rw [←hx]
  exact hv x hxc
end CFSG.Quasithin.Chapter3
