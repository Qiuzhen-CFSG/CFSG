module
public import Theory.SpecificGroups.Alternating.SixSylowFiveSection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.StarResidual
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingStarSixExclusion

/-!
# Small alternating exclusions on the original fixed component

The original Sylow in C_G(u) supplies a full Sylow in Lᵤ*. Its marked
stabilizer has the actual perfect A₅ residual. This excludes A₅ by properness,
and A₆ and its central covers by the Sylow-normalizer obstruction. In A₈,
the radical image is a nontrivial permutation two-subgroup normalized by
both a subgroup with a factor five and a full Sylow, which is impossible.
No block, parabolic, or C.2.7 alternative is assumed.

Source: Aschbacher--Smith 14.7.68(2), pp.1071--1072, using C.2.7,
pp.145--147, and the literal original fixed-centralizer Sylow placement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedStarM_contains_sylow (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    ∃ S : Sylow 2 (starImage Lu (d.fixedCore u) Lu),
      (S : Subgroup _) ≤ (starM Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u)).subgroupOf (starImage Lu (d.fixedCore u) Lu) := by
  obtain ⟨P,hP⟩ := h.sylow
  let A := Lu.subgroupOf (d.fixedCentralizer u)
  let : A.Normal := h.normal
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal A
  let e := subgroupOfEquivOfLe h.le_centralizer
  let f := (toStarImage Lu (d.fixedCore u)).comp e.toMonoidHom
  refine ⟨Q.mapSurjective (f := f)
    ((toStarImage_surjective Lu (d.fixedCore u)).comp e.surjective),?_⟩
  rintro x ⟨a,ha,rfl⟩
  have haP : a.val ∈ (P : Subgroup (d.fixedCentralizer u)) := by
    change a ∈ (Q : Subgroup A) at ha
    rw [hQ] at ha
    exact ha
  have haT : (a.val : G) ∈ d.fixedSylow u := by
    rw [←hP]
    exact mem_map_of_mem _ haP
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel Lu (d.fixedCore u)))
    (show (a.val : G) ∈ (F.H ⊓ d.fixedCentralizer u) ⊓ Lu from
      ⟨⟨F.invariant 1 haT.1,a.val.property⟩,a.property⟩)

theorem fixedComponent_C27_alternatingFive_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : starImage Lu (d.fixedCore u) Lu ≃* alternatingGroup (Fin 5)) : False := by
  let A := starImage Lu (d.fixedCore u) Lu
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  have hres := d.fixedStarM_hasA5TwoResidual_of_source u h
  have hcard : Nat.card A = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have h60 : 60 ∣ Nat.card M := by
    obtain ⟨B,hB,hp,⟨b⟩,_⟩ := hres
    have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
      rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    exact hc ▸ ((card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _)).trans B.card_subgroup_dvd_card)
  have he : M = A := eq_of_le_of_card_ge (starM_le _ _ _) (by
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos h60)
  exact (d.fixedComponent_C27_thompson_control u h).2.ne he

theorem fixedComponent_C27_centralSix_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (q : starImage Lu (d.fixedCore u) Lu →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) [Group.IsSolvable q.ker] : False := by
  let A := starImage Lu (d.fixedCore u) Lu
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  let i : M →* A := inclusion (starM_le _ _ _)
  obtain ⟨S,hS⟩ := d.fixedStarM_contains_sylow u h
  obtain ⟨B,hB,hperfect,⟨e⟩,_⟩ := d.fixedStarM_hasA5TwoResidual_of_source u h
  let := hB
  let := hperfect
  let C := B.map i
  let t : B ≃* C := B.equivMapOfInjective i (inclusion_injective (starM_le _ _ _))
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := t.toMonoidHom) t.surjective
  let c := ((QuotientGroup.congr _ _ t (pCore_map_iso 2 t)).symm).trans e
  have hMC : M.subgroupOf A ≤ normalizer (C : Set A) := by
    intro m hm
    exact B.le_normalizer_map i (mem_map_of_mem i
      (show (⟨m.val,hm⟩ : M) ∈ normalizer (B : Set M) from
        le_normalizer_of_normal (mem_top _)))
  exact Theory.SpecificGroups.Alternating.SixSylowNormalizer.no_sylow_normalizes_perfect_five_section
    S C c (hS.trans hMC) q hq

theorem fixedComponent_C27_alternatingSix_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : starImage Lu (d.fixedCore u) Lu ≃* alternatingGroup (Fin 6)) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    infer_instance
  exact d.fixedComponent_C27_centralSix_row_impossible u h e.toMonoidHom e.surjective

theorem fixedComponent_C27_tripleSix_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : (starImage Lu (d.fixedCore u) Lu ⧸ center (starImage Lu (d.fixedCore u) Lu)) ≃*
      alternatingGroup (Fin 6)) : False := by
  let A := starImage Lu (d.fixedCore u) Lu
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center A))
  let : Group.IsSolvable q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    infer_instance
  exact d.fixedComponent_C27_centralSix_row_impossible u h q
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

/-- The actual marked stabilizer normalizes the whole radical image. -/
theorem fixedStarM_le_starRadicalNormalizer
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) ≤
      normalizer (starImage Lu (d.fixedCore u) (d.fixedCore u) :
        Set (StarQuotient Lu (d.fixedCore u))) := by
  let J := Lu ⊔ d.fixedCore u
  let B := ((F.H ⊓ d.fixedCentralizer u) ⊓ Lu).subgroupOf J
  have hn : B ≤ normalizer ((d.fixedCore u).subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (show d.fixedCore u ≤ J from le_sup_right)]
    intro a ha
    exact d.H_normalizes_fixedCore u h.member h.fixed ha.1.1
  exact (map_mono (f := QuotientGroup.mk' (starKernel Lu (d.fixedCore u))) hn).trans
    (le_normalizer_map _)

theorem fixedComponent_C27_alternatingEight_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (e : starImage Lu (d.fixedCore u) Lu ≃* alternatingGroup (Fin 8)) : False := by
  have input := d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  obtain ⟨f,hf,hfe⟩ := ChapterC.C27Source.alternating_star_embedding input
    (by decide : 5 ≤ 8) (by decide : 8 ≠ 6) e
  let A := starImage Lu (d.fixedCore u) Lu
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  let R := starImage Lu (d.fixedCore u) (d.fixedCore u)
  let Q := R.map f
  let N := M.map f
  have hR : IsPGroup 2 (d.fixedCore u) := by
    have hh := input.setup.radical.isPGroup.map (d.fixedCentralizer u).subtype
    rwa [map_subgroupOf_eq_of_le input.setup.radical_le] at hh
  have hQ : IsPGroup 2 Q := (hR.comap_subtype.map
    (QuotientGroup.mk' (starKernel Lu (d.fixedCore u)))).map f
  have hQne : Q ≠ ⊥ := by
    intro he
    exact ChapterC.C27Source.star_radical_ne_bot input
      ((R.map_eq_bot_iff_of_injective hf).mp he)
  have hN : N ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨m,hm,rfl⟩
    rw [show f m = (e ⟨m,starM_le _ _ _ hm⟩ : Equiv.Perm (Fin 8)) from
      hfe ⟨m,starM_le _ _ _ hm⟩]
    exact (e ⟨m,starM_le _ _ _ hm⟩).property
  have hMR : M ≤ normalizer (R : Set (StarQuotient Lu (d.fixedCore u))) :=
    d.fixedStarM_le_starRadicalNormalizer u h
  have hNQ : N ≤ normalizer (Q : Set _) :=
    (map_mono hMR).trans (R.le_normalizer_map f)
  have h5 : 5 ∣ Nat.card N := by
    rw [card_map_of_injective hf]
    exact (d.fixedStarM_hasA5TwoResidual_of_source u h).five_dvd_card
  obtain ⟨S,hS⟩ := d.fixedStarM_contains_sylow u h
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  apply Theory.SpecificGroups.AlternatingSixNormalizer.eight_no_normalized_two Q N hQ hQne
    hN hNQ h5 P
  rintro _ ⟨x,⟨a,ha,rfl⟩,rfl⟩
  change (e a : Equiv.Perm (Fin 8)) ∈ normalizer (Q : Set _)
  rw [←hfe]
  exact hNQ (mem_map_of_mem f (hS ha))

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
