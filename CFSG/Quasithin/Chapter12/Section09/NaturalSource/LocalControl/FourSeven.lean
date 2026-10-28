module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointControl
public import Theory.SpecificGroups.AlternatingSeven.BinaryThreeNormalizer

/-!
# Excluding the A₇ point row with the original quadratic actor

Work in the literal quotient J/O₂(J), where J = K₁T. The image D of K₁
is normal and isomorphic to A₇. The original L₁ image has quotient GL₃(2)
by its two-core; the order of D makes that core trivial. The normalizer
calculation therefore makes the image A of O₂(L₁T) centralize D.

The image of L₁T supplements D and normalizes A. Since the ambient
quotient has trivial two-core, A is trivial. But the original F.9.16
critical-pair proof supplies a nontrivial quadratic actor inside exactly A.
This contradiction excludes the abelian A₇ row before the plane-lattice
argument. Every image uses the original quotient map and original subgroups.
No overgroup recognition or module classification is assumed.

Source: Aschbacher--Smith F.9.16(3--4), pp.323--324, and the natural
branch of 12.9.5--7, pp.860--862, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
open Chapter13.Section08.SolvableExclusion.Three
open Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original abelian degree-four A₇ point row is impossible: its
placed nontrivial quadratic actor would centralize the component. -/
theorem four_seven_abelian_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7) : False := by
  let := h.chosen.elementary
  let J := C.K1 ⊔ (T : Subgroup G)
  let E₀ := F.Li L 1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H := sup_le C.point_le (F.invariant 1)
  have hLJ : F.Li L 1 ≤ J := C.contains.trans le_sup_left
  have hEJ : E₀ ≤ J := sup_le hLJ le_sup_right
  let N := C.K1.subgroupOf J
  have hN : N.IsCComponent := C.component.subgroupOf_of_le le_sup_left hJH
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal))
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := N.map q
  let : D.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  let e₀ : N ≃* C.K1 := subgroupOfEquivOfLe le_sup_left
  let eD : D ≃* alternatingGroup (Fin 7) :=
    (cComponentTwoCoreQuotientEquiv hN).symm.trans
      ((QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)).trans hm.some)
  let B₀ := (F.Li L 1).subgroupOf J
  let B := B₀.map q
  let E := (E₀.subgroupOf J).map q
  let A := ((F.Ri L 1).subgroupOf J).map q
  have hBD : B ≤ D := map_mono (comap_mono C.contains)
  have hBE : B ≤ E := map_mono (comap_mono le_sup_left)
  have hEB : E ≤ normalizer (B : Set (J ⧸ pCore 2 J)) := by
    have hn : E₀ ≤ normalizer (F.Li L 1 : Set G) :=
      sup_le (F.Li L 1).le_normalizer (sylow_normalizes_point_residual h earlier F)
    have hn' : E₀.subgroupOf J ≤ normalizer (B₀ : Set J) := by
      intro x hx y
      exact hn hx (y : G)
    exact (map_mono (f := q) hn').trans (B₀.le_normalizer_map q)
  obtain ⟨d,hd,_,⟨eLi⟩⟩ := Components.Li_core_linear F h.naturalMarking 1
    (Or.inr ⟨rfl,Or.inl rfl⟩)
  have hd3 : d = 3 := by norm_num at hd; exact hd
  subst d
  let f := q.subgroupMap B₀
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.subgroupMap B₀).ker
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    exact hq.comap_subtype
  let eL := subgroupOfEquivOfLe hLJ
  let eB : (B ⧸ pCore 2 B) ≃* LinearGroup 3 :=
    (f.pCoreQuotientEquiv (q.subgroupMap_surjective B₀) hk).symm.trans
      ((QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans eLi)
  have hp : IsPGroup 2 A := ((isPGroup_pCoreIn 2 E₀).comap_subtype).map q
  have hEA : E ≤ normalizer (A : Set (J ⧸ pCore 2 J)) := by
    have hn : E₀.subgroupOf J ≤ normalizer ((F.Ri L 1).subgroupOf J : Set J) := by
      intro x hx y
      exact le_normalizer_pCoreIn 2 E₀ hx (y : G)
    exact (map_mono (f := q) hn).trans (((F.Ri L 1).subgroupOf J).le_normalizer_map q)
  have hAE : A ≤ E := map_mono (comap_mono (pCoreIn_le 2 E₀))
  have hAc : A ≤ centralizer (D : Set (J ⧸ pCore 2 J)) :=
    (le_pCoreIn_of_normalizes hp hAE hEA).trans
      (AlternatingSeven.parabolic_core_centralizes D B E hBD hBE hEB eD eB)
  have hcover : C.K1 ⊔ E₀ = J :=
    le_antisymm (sup_le le_sup_left hEJ) (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have hgen : D ⊔ E = ⊤ := by
    change (C.K1.subgroupOf J).map q ⊔ (E₀.subgroupOf J).map q = ⊤
    rw [←Subgroup.map_sup,←subgroupOf_sup (show C.K1 ≤ J from le_sup_left) hEJ,
      hcover,subgroupOf_self,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hAz : A = ⊥ := by
    have hh := centralizer_inf_eq_bot_of_supplement D E A hgen hp hEA
      (pCore_quotient_pCore_eq_bot 2)
    rwa [inf_eq_left.mpr hAc] at hh
  obtain ⟨hU,a,_,B',hBR,hA,_,_⟩ := abelian_local_quadratic_actor h earlier F hab J
    (point_join_mem_Hz_of_abelian h (Or.inl rfl) earlier F hab C)
  exact hA.1 (bot_unique ((map_mono hBR).trans hAz.le))
end CFSG.Quasithin.Chapter12.Section09.NaturalSource
