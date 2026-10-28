module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Seven
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointGeometry
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Nonquasisimple
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Consumers

/-!
# Strict radical enlargement gives a generation-one escape

A containing C-component inside M = N_G(L) equals the original local
residual: its intersection with L is normal and nonsolvable, so is the whole
component, and perfectness puts it in N_L(Vᵢ)∞. A strict point component
therefore escapes M. In the nonquasisimple row the proved product
K₁ = Ξ₇(K₁)L₁ makes the actual solvable subgroup Ξ₇(K₁)T escape M.
It has nontrivial two-core, witnessed by the original V₁. Finite minimal
descent gives an actual H-star subgroup inside it; solvability and the
original involution give generation parameter exactly one.

The final application uses the existing source generation-one exclusion,
with point-core containment proved here from the nonquasisimple component.
It retains only Structural1222At and G₃,G₆ ≤ M. The structural input belongs
to qt-d-1222-source; the normalizer containments, quasisimple component
refinements and their strict escape remain with qt-d-1251-local. Final
exterior assembly belongs to qt-d-1251-source.

Source: Aschbacher--Smith, 12.5.11(2), printed p.821.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- A local containing component inside M cannot enlarge the original residual. -/
theorem local_component_eq_of_le_M
    (i : ℕ) (hi : LocalIndex i) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi i))
    (hLK : s.marking.Li i ≤ K) (hKM : K ≤ s.marking.M) :
    s.marking.Li i = K := by
  let H := s.marking.Gi i
  let C := K.subgroupOf H
  let e : C ≃* K := subgroupOfEquivOfLe hK.1
  let : Group.IsPerfect C := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let R := (L.subgroupOf H).subgroupOf C
  let : R.Normal := normal_subgroupOf_of_le_normalizer (by
    intro c hc l
    exact hKM hc (l : G))
  have hR : R = ⊤ := by
    by_contra hne
    let : Group.IsSolvable R := hK.2.isSolvable_of_subnormal_lt_top
      (inferInstance : R.Normal).isSubnormal hne
    let f : s.marking.Li i →* R :=
      { toFun := fun b => ⟨⟨⟨b,s.marking.Li_le_Gi i b.property⟩,hLK b.property⟩,
          s.marking.Li_le_L i b.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b he
      exact Subtype.ext (congrArg (fun x : R => (((x : C) : H) : G)) he)
    exact Chapter1.mem_L_not_isSolvable (s.Li_mem_local i hi)
      (Group.isSolvable_of_isSolvable_injective hf)
  have hKL : K ≤ L := by
    intro k hk
    have hr : (⟨⟨k,hK.1 hk⟩,hk⟩ : C) ∈ R := hR.symm ▸ mem_top _
    exact hr
  have hN : K ≤ L ⊓ s.marking.Gi i := le_inf hKL hK.1
  let a : K.subgroupOf (L ⊓ s.marking.Gi i) ≃* K := subgroupOfEquivOfLe hN
  let : Group.IsPerfect (K.subgroupOf (L ⊓ s.marking.Gi i)) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  have hres := le_solvableResidual_of_isPerfect (K.subgroupOf (L ⊓ s.marking.Gi i))
  exact le_antisymm hLK (by
    intro k hk
    exact mem_map_of_mem _ (hres (show (⟨k,hN hk⟩ : (L ⊓ s.marking.Gi i : Subgroup G)) ∈
      K.subgroupOf (L ⊓ s.marking.Gi i) from hk)))

/-- A strict point component supplies a genuine escaping solvable H-star in
the radical row, and its generation parameter is exactly one. -/
theorem exists_generation_one_of_strict_radical_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K) (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ Chapter1.XiP 7 K ⊔ (T : Subgroup G) ∧
      H ≤ K ⊔ (T : Subgroup G) ∧ ChapterE.generationParameter H = 1 := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 K
  let J := X ⊔ (T : Subgroup G)
  have hKN : s.marking.Gi 1 ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1).mp hN
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    Chapter1.XiP_invariant 7 (s.sylow_le_G₁.trans hKN)
  have hJM : ¬ J ≤ s.marking.M := by
    intro hj
    apply hne
    apply s.local_component_eq_of_le_M 1 (.inl rfl) hK hLK
    rw [s.local_component_nonquasisimple_product h 1 (.inl rfl) hK hLK hn]
    exact sup_le (le_sup_left.trans hj) ((s.marking.Li_le_L 1).trans L.le_normalizer)
  let : Group.IsSolvable X := Chapter1.RadicalNormalizers.XiP_solvable 7 (by decide) K
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : (X.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer hTX)
  let : Group.IsSolvable (X.subgroupOf J) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show X ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show X ≤ J from le_sup_left)).injective
  let : Group.IsSolvable ((T : Subgroup G).subgroupOf J) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ J from le_sup_right)).injective
  let : Group.IsSolvable J := Group.isSolvable_of_normal_sup_eq_top
    (X.subgroupOf J) ((T : Subgroup G).subgroupOf J) (by
      rw [←subgroupOf_sup le_sup_left le_sup_right]
      exact subgroupOf_self J)
  have hJ1 : J ≤ s.marking.Gi 1 := sup_le ((Chapter1.XiP_le 7 K).trans hK.1) s.sylow_le_G₁
  have hV1T : s.marking.Vi 1 ≤ (T : Subgroup G) := (s.marking.subspace_le _).trans D.le_sylow
  let := D.elementary
  have hcore : s.marking.Vi 1 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le (s.marking.subspace_le _))
    (hV1T.trans le_sup_right) hJ1
  have hJH : J ∈ Chapter1.HOver G (T : Set G) :=
    ⟨fun he => s.marking.Vi_ne_bot 1 (.inl rfl) (bot_unique (he ▸ hcore)),fun _ ht => (le_sup_right : (T : Subgroup G) ≤ J) ht⟩
  let P := fun H : Subgroup G => H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ s.marking.M
  obtain ⟨H,hHJ,hH,hmin⟩ := exists_minimal_le_of_wellFoundedLT P J (show P J from ⟨hJH,hJM⟩)
  have hstar : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M := ⟨hH,hmin⟩
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective (inclusion_injective hHJ)
  have heven : ¬ Odd (Nat.card H) := by
    have hdiv := card_dvd_of_le (hV1T.trans hH.1.2)
    rw [s.marking.card_V₁] at hdiv
    exact fun ho => ho.not_two_dvd_nat hdiv
  exact ⟨H,hstar,hHJ,hHJ.trans (sup_le_sup_right (Chapter1.XiP_le 7 K) _),
    ChapterE.generationParameter_eq_one_of_solvable heven⟩

/-- The genuine generation-one exclusion rules out strict radical enlargement. -/
theorem point_component_eq_of_nonquasisimple_of_generation_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) : s.marking.Li 1 = K := by
  by_contra hne
  obtain ⟨H,hH,_,_,hg⟩ := s.exists_generation_one_of_strict_radical_point_component h hK hLK hN hne hn
  exact hex H hH hg

/-- The radical row of 12.5.11(2), applying the genuine generation-one
exclusion with point-core containment already proved for this component. -/
theorem point_component_eq_of_nonquasisimple_of_source_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) : s.marking.Li 1 = K := by
  apply s.point_component_eq_of_nonquasisimple_of_generation_exclusion h hK hLK hN hn
  intro H hH
  exact generation_ne_one_of_source_parameters s h structural hG₃ hG₆
    (s.seed_le_point_core_of_nonquasisimple_component h hK hLK hN hn) hH

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
