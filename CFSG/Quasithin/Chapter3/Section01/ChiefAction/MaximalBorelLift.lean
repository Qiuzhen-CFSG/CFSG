module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentSylowNormalizer
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SpanSetup
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.PerfectCover


public import Theory.Representation.HigherFieldBorelFixedSpaces.Sylow

/-!
# Borel lifts from the actual maximal Sylow overgroup

The maximal subgroup is supplied literally. Its two-residual centralizes the
original seed subgroup; no ambient QRC intersection or restriction on the full
action kernel is needed. This applies to the escape subgroup in original
15.1.12 as well as to the Borel step of original 3.1.9(5).
-/

public section

open Subgroup Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.MaximalBorel
open ChapterB Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
  {H V : Subgroup G}

omit [Finite D] in
theorem twoPerfect_image_le_maximal_residual
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (B : Subgroup D) (hB : IsPPerfect 2 B)
    (hBM : B ≤ minimalParabolicMax (S.mapSurjective hq)
      (minimalParabolic_reduced_image S hP q hq hc hn).2) :
    B ≤ ((pResidual 2 N).map N.subtype).map q := by
  have hk := (minimalParabolic_reduced_image S hP q hq hc hn).1
  have hmax : N.map q =
      minimalParabolicMax (S.mapSurjective hq)
        (minimalParabolic_reduced_image S hP q hq hc hn).2 := by
    rw [minimalParabolicMax_unique S hP hN hSN]
    exact minimalParabolicMax_map_core S hP q hq hk
  have hm := embedded_pResidual_mono 2 hBM
  rw [(pResidual_eq_top_iff 2 B).mpr hB,←MonoidHom.range_eq_map,range_subtype] at hm
  rw [map_embedded_pResidual,hmax]
  exact hm

theorem twoPerfect_component_image_lifts_fixing_seed
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    {L : Subgroup D} (hL : IsComponent D L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L)
    (B : Subgroup D) (hB : IsPPerfect 2 B)
    (hBL : B ≤ L ⊓ normalizer
      (((S.mapSurjective hq : Sylow 2 D) : Subgroup D) ⊓ L : Set D)) :
    ∀ b ∈ B, ∃ x : H, q x = b ∧ (x : G) ∈ centralizer (V : Set G) := by
  have hb := twoPerfect_image_le_maximal_residual S N hN hSN hP q hq hc hn B hB
    (hBL.trans (component_sylow_normalizer_le_maximal
      (S.mapSurjective hq)
      (minimalParabolic_reduced_image S hP q hq hc hn).2
      hL heven))
  intro b hbB
  obtain ⟨x,hx,hxb⟩ := hb hbB
  exact ⟨x,hxb,hres hx⟩
end CFSG.Quasithin.Chapter3.MaximalBorel

open Subgroup Representation Representation.BinaryOffender
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3.MaximalBorel
open ChapterB Theory.GroupTheory HigherFieldBorelFixedSpaces
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
  {H V : Subgroup G}

theorem component_sylowNormalizer_lifts_fixing_module
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    {L : Subgroup D} (hL : IsComponent D L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L)
    (P : Sylow 2 L) (hPS : (P : Subgroup L) =
      ((S.mapSurjective hq : Sylow 2 D) : Subgroup D).subgroupOf L)
    (hB : IsPPerfect 2 (normalizer (P : Set L))) :
    ∀ b ∈ normalizer (P : Set L), ∃ x : H, q x = (b : D) ∧
      (x : G) ∈ centralizer (V : Set G) := by
  let Simage := S.mapSurjective hq
  let B := (normalizer (P : Set L)).map L.subtype
  have hperf : IsPPerfect 2 B := hB.of_surjective
    ((normalizer (P : Set L)).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom
    ((normalizer (P : Set L)).equivMapOfInjective L.subtype L.subtype_injective).surjective
  have hBL : B ≤ L ⊓ normalizer ((Simage : Subgroup D) ⊓ L : Set D) := by
    refine le_inf (map_subtype_le _) ?_
    have hn := (P : Subgroup L).le_normalizer_map L.subtype
    have he : (P : Subgroup L).map L.subtype = (Simage : Subgroup D) ⊓ L := by
      rw [hPS]
      change ((Simage : Subgroup D).subgroupOf L).map L.subtype = _
      rw [← inf_subgroupOf_right (Simage : Subgroup D) L,
        map_subgroupOf_eq_of_le (inf_le_right : (Simage : Subgroup D) ⊓ L ≤ L)]
    exact hn.trans_eq (congrArg (fun A : Subgroup D => normalizer (A : Set D)) he)
  intro b hb
  exact twoPerfect_component_image_lifts_fixing_seed S N hN hSN hP hres q hq hc hn
    hL heven B hperf hBL b (mem_map_of_mem L.subtype hb)
end CFSG.Quasithin.Chapter3.MaximalBorel

namespace CFSG.Quasithin.Chapter3.MaximalBorel
open ChapterB Theory.GroupTheory HigherFieldBorelFixedSpaces
variable {G D W F : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {H V : Subgroup G}

theorem natural_component_fixed_seed_coordinate_zero
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (v : W)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    {L : Subgroup D} (hL : IsComponent D L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L) (hF : 4 ≤ Nat.card F)
    (e : L ≃* SL(2,F)) (f : W →ₗ[ZMod 2] (Fin 2 → F))
    (hf : ∀ (g : L) w, f (ρ (g : D) w) = binaryNatural 2 (e g) (f w)) :
    f v = 0 := by
  let Simage := S.mapSurjective hq
  obtain ⟨P,hPS⟩ := Simage.exists_subgroupOf_eq_of_subnormal L hL.1
  obtain ⟨hB,hfix⟩ := natural_sylowNormalizer hF P (ρ.comp L.subtype) e f hf
  apply hfix v
  intro b
  obtain ⟨x,hx,hxc⟩ := component_sylowNormalizer_lifts_fixing_module S N hN hSN hP hres q hq hc hn
    hL heven P hPS hB b b.property
  change ρ (b : L) v = v
  rw [←hx]
  exact hv x hxc
end CFSG.Quasithin.Chapter3.MaximalBorel
