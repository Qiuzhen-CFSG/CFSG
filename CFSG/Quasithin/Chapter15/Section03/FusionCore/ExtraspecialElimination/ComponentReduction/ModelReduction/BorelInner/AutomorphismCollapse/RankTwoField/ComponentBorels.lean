module
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.LieBorels

/-!
# Component Borels inside the whole star closure

Lift the actual closure Sylow to the product of all distinct conjugate star
components. A Sylow of this finite product is the product of its coordinate
Sylows. The coordinate inclusions therefore send their full normalizers into
the product Sylow normalizer, and multiplication sends these into the actual
closure normalizer. Sylow maximality identifies each coordinate image with
the intersection of the specified Sylow and that component.

This construction keeps every conjugate and permits central overlaps: the
multiplication map is only required to be surjective. The actual star Borel
identification then gives both fields of `ComponentBorel` for the selected
component. Quasisimplicity is the explicit earlier classification output used
to prove that distinct conjugates commute.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, printed p.1144,
proof of 15.3.49(k).
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField

private theorem sylow_factor_normalizer {D : Type*} [Group D] [Finite D]
    {ι : Type*} [Fintype ι] (C : ι → Subgroup D)
    (hcomm : Pairwise fun i j => C i ≤ centralizer (C j : Set D))
    (hgen : iSup C = ⊤) (S : Sylow 2 D) (i : ι) :
    ∃ Q : Sylow 2 (C i),
      (Q : Subgroup (C i)).map (C i).subtype = (S : Subgroup D) ⊓ C i ∧
      (normalizer (Q : Set (C i))).map (C i).subtype ≤ normalizer (S : Set D) := by
  classical
  let f : (∀ j, C j) →* D :=
    noncommPiCoprod (fun j k hne x y hx hy => (hcomm hne hx y hy).symm)
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (noncommPiCoprod_range.trans hgen)
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 2 S
  have hPS : P.map f = (S : Subgroup D) :=
    congrArg (fun R : Sylow 2 D => (R : Subgroup D)) hP
  let Q (j : ι) : Sylow 2 (C j) :=
    P.mapSurjective (f := Pi.evalMonoidHom (fun j => C j) j) (Function.surjective_eval j)
  let R : Subgroup (∀ j, C j) := Subgroup.pi Set.univ (fun j => (Q j : Subgroup (C j)))
  have hR : IsPGroup 2 R := by
    intro x
    choose k hk using fun j => (Q j).isPGroup' ⟨x.val j, x.property j (Set.mem_univ j)⟩
    refine ⟨∑ j, k j, Subtype.ext (funext fun j => ?_)⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (orderOf_dvd_of_pow_eq_one (congrArg Subtype.val (hk j))).trans
      (pow_dvd_pow 2 (Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) (Finset.mem_univ j)))
  have hPR : (P : Subgroup (∀ j, C j)) = R := by
    symm
    apply P.is_maximal' hR
    intro x hx j _
    exact mem_map_of_mem (Pi.evalMonoidHom (fun j => C j) j) hx
  have hPi (x : ∀ j, C j) : x ∈ (P : Subgroup (∀ j, C j)) ↔
      ∀ j, x j ∈ (Q j : Subgroup (C j)) := by
    rw [hPR]
    simp only [R, Subgroup.mem_pi, Set.mem_univ, forall_const]
  have hsingle (x : C i) (hx : x ∈ (Q i : Subgroup (C i))) :
      Pi.mulSingle i x ∈ (P : Subgroup (∀ j, C j)) := by
    rw [hPi]
    intro j
    by_cases hij : i = j
    · subst j
      simpa using hx
    · simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]
  have hQle : (Q i : Subgroup (C i)).map (C i).subtype ≤ (S : Subgroup D) := by
    rintro x ⟨y, hy, rfl⟩
    apply hPS.le
    exact ⟨Pi.mulSingle i y, hsingle y hy, noncommPiCoprod_mulSingle i y⟩
  have hQeq : (Q i : Subgroup (C i)) = (S : Subgroup D).subgroupOf (C i) := by
    symm
    apply (Q i).is_maximal' S.isPGroup'.comap_subtype
    intro x hx
    exact hQle (mem_map_of_mem (C i).subtype hx)
  refine ⟨Q i, ?_, ?_⟩
  · rw [hQeq, subgroupOf_map_subtype]
  · rintro x ⟨g, hg, rfl⟩
    have hng : Pi.mulSingle i g ∈ normalizer (P : Set (∀ j, C j)) := by
      apply mem_normalizer_iff.mpr
      intro x
      rw [hPi, hPi]
      apply forall_congr'
      intro j
      by_cases hij : i = j
      · subst j
        simpa using (mem_normalizer_iff.mp hg (x i))
      · simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]
    have hm := (P : Subgroup (∀ j, C j)).le_normalizer_map f (mem_map_of_mem f hng)
    rw [hPS] at hm
    have he : f (Pi.mulSingle i g) = (g : D) := noncommPiCoprod_mulSingle i g
    rw [he] at hm
    exact hm

open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open ModelSelection LieBorels

universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- All conjugate components supply the selected component’s actual Sylow and Borel. -/
theorem exists_componentBorel
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L)) :
    Nonempty (ComponentBorel H L T) := by
  classical
  let _ := Fintype.ofFinite ↥(conjugateFactors H L T)
  let K := starImage H L
  let D := starImage H (localSpan L T)
  have hK : K ≤ D := map_mono (comap_mono (le_conjugateSpanBy L T))
  have hi : K ∈ conjugateFactors H L T := by
    apply mem_conjugateFactors.mpr
    refine ⟨1, ?_⟩
    have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    change K = starImage H (L.map (MulAut.conj (1 : G)).toMonoidHom)
    rw [he, Subgroup.map_id]
  let i : ↥(conjugateFactors H L T) := ⟨K, hi⟩
  obtain ⟨Q, hQ, hN⟩ := sylow_factor_normalizer factor (factor_commute d hq)
    (factor_sup d) (closureSylow d) i
  let e : factor i ≃* K := subgroupOfEquivOfLe hK
  let P : Sylow 2 K := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap (U : Subgroup (factor i)) :
      (U.map e.toMonoidHom).map K.subtype = (U.map (factor i).subtype).map D.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hS : starImage H (sylowIntersection L T) ≤ D := map_mono (comap_mono inf_le_right)
  have hSco : (closureSylow d : Subgroup D) =
      (starImage H (sylowIntersection L T)).subgroupOf D := closureSylow_coe d
  have hPeq : (P : Subgroup K).map K.subtype =
      starImage H (sylowIntersection L T) ⊓ K := by
    rw [show (P : Subgroup K) = (Q : Subgroup (factor i)).map e.toMonoidHom from rfl,
      hmap, hQ, map_inf _ _ _ D.subtype_injective, hSco,
      map_subgroupOf_eq_of_le hS]
    rw [show factor i = K.subgroupOf D from rfl, map_subgroupOf_eq_of_le hK]
  have hNB : (normalizer (closureSylow d : Set D)).map D.subtype =
      starImage H (relativeBorel L T) := by
    change (normalizer ((closureSylow d : Subgroup D) : Set D)).map D.subtype = _
    have hBN : (starImage H (relativeBorel L T)).subgroupOf D =
        normalizer ((starImage H (sylowIntersection L T)).subgroupOf D : Set D) :=
      star_borel_eq_normalizer d
    rw [hSco, ← hBN]
    exact map_subgroupOf_eq_of_le (show starImage H (relativeBorel L T) ≤ D from
      map_mono (comap_mono (show relativeBorel L T ≤ localSpan L T from inf_le_left)))
  refine ⟨⟨P, hPeq, ?_⟩⟩
  have hnP : normalizer (P : Set K) =
      (normalizer (Q : Set (factor i))).map e.toMonoidHom :=
    (map_equiv_normalizer_eq (Q : Subgroup (factor i)) e).symm
  rw [hnP, hmap]
  exact (map_mono hN).trans_eq hNB

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField
