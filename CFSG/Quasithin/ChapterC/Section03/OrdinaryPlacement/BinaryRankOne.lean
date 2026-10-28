module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SpanProjection
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.SpecificGroups.Suzuki.NormalSubgroups

/-!
# Binary rank-one ordinary components are excluded by the source module

The perfect coordinate projection supplied by genuine C.2.8 has noncentral
two-core. In characteristic-two SL₂, every perfect subgroup has trivial
two-core; the same follows for Suzuki groups from their normal-subgroup
partition. A central quotient marking therefore excludes these components.

This proves the binary Lie-type local obstruction used in C.3.3, printed
p.149, without first assuming the conclusion that M normalizes L.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

private theorem projected_core_central
    {J S : Type*} [Group J] [Group S] [Finite J]
    (K P : Subgroup J) (hPK : P ≤ K) (q : K →* S)
    (hker : q.ker ≤ center K)
    (hcore : pCore 2 P ≤ (q.comp (inclusion hPK)).ker) :
    ⁅P.pCoreIn 2,P⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u,hu,rfl⟩ y hy
  have hz : inclusion hPK u ∈ center K := hker (hcore hu)
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hPK hy⟩)

/-- Characteristic-two SL₂ cannot be the central quotient of an ordinary
component in the genuine C.2.8 configuration. -/
theorem no_ordinary_component_sl2_central_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* SL(2,F)) : False := by
  apply h.no_ordinary_component_of_perfect_subgroup_core_central K hK
  intro P hPK hP
  let := hP
  let q : K →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : q.ker ≤ center K := by
    intro k hk
    change e (QuotientGroup.mk k) = 1 at hk
    exact (QuotientGroup.eq_one_iff k).mp (e.injective (by simpa only [map_one] using hk))
  exact projected_core_central K P hPK q hker
    (Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker (q.comp (inclusion hPK)))

private theorem suzuki_perfect_core_le_ker
    {A : Type*} [Group A] [Group.IsPerfect A]
    {m : ℕ} (hm : 0 < m)
    (f : A →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : pCore 2 A ≤ f.ker := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hbot : pCore 2 f.range = ⊥ := by
    by_contra hne
    let : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
      intro he
      have : Subsingleton f.range := by rw [he]; infer_instance
      exact hne (Subsingleton.elim _ _))
    let : Group.IsNilpotent (pCore 2 f.range) := pCore_isNilpotent
    have hs := BenderSuzuki.MatrixGroups.suzukiSubgroup_isSolvable_of_solvable_normal
      hm f.range (pCore 2 f.range) hne
    exact Group.IsPerfect.not_isSolvable f.range hs
  have him : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f.rangeRestrict
      f.rangeRestrict_surjective, pCore_isPGroup.map f.rangeRestrict⟩
  rw [hbot] at him
  have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique him)
  intro a ha
  exact congrArg Subtype.val (hk ha)

/-- The genuine Suzuki central quotient likewise contradicts the noncentral
two-core of the actual perfect projection. -/
theorem no_ordinary_component_suzuki_central_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {m : ℕ} (hm : 0 < m)
    (e : K ⧸ center K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  apply h.no_ordinary_component_of_perfect_subgroup_core_central K hK
  intro P hPK hP
  let := hP
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : q.ker ≤ center K := by
    intro k hk
    change e (QuotientGroup.mk k) = 1 at hk
    exact (QuotientGroup.eq_one_iff k).mp (e.injective (by simpa only [map_one] using hk))
  exact projected_core_central K P hPK q hker
    (suzuki_perfect_core_le_ker hm (q.comp (inclusion hPK)))

end CFSG.Quasithin.ChapterC.HypothesisC28
