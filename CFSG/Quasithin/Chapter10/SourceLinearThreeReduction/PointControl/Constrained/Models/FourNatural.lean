module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.QuietRows
public import Theory.Representation.PSL3Two.FourNaturalNormalizer
public import Theory.GroupTheory.PCoreQuotientInnerJoin

/-!
# The original point quotient in the retained four-natural row

The four-copy marking implements every component-normalizer automorphism
on its literal quotient coordinates. The concrete normalizer theorem
excludes graph automorphisms, without discarding the original fixed kernel
or claiming that multiplicity operators are trivial.

In particular C_T(v) acts innerly on L/O₂(L). The inner-join theorem then
identifies (L C_T(v))/O₂(L C_T(v)) with the original SL₃(2), preserving the
specified quotient map on L. Orbit preparation and exclusion of this row
remain with qt-d-10-nona5-point-constrained; these results use neither
10.2.3's generation bound nor small-offender point control.

Source: Aschbacher--Smith 10.1.1(6) and10.2.9, pp.741,751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem four_natural_common_normalizer_inner
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (P : Subgroup G) (hPL : P ≤ normalizer (L : Set G))
    (hPW : P ≤ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (p : P) :
    (MulAut.congr e) (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion hPL p))) ∈
        MulAut.innerSubgroup BinaryLinearThree.Group := by
  let W := ⁅D.fullModule,L⁆
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hPZ : P ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf hPW (hPL.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨η,hη⟩ := s.exists_original_quotient_action hPW hPZ
  let a : P →* MulAut BinaryLinearThree.Group :=
    (MulAut.congr e).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hPL)))
  have ha (p : P) (l : L) : a p (q l) = q (L.normalizerMonoidHom (inclusion hPL p) l) := by
    change e (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion hPL p)) (e.symm (e (QuotientGroup.mk' _ l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  apply BinaryLinearThree.FourNatural.implemented_automorphism_inner _
    (LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom p))
  intro g x
  obtain ⟨l,rfl⟩ := hq g
  obtain ⟨w,rfl⟩ := s.onto (Multiplicative.ofAdd x)
  change η p (BinaryLinearThree.FourNatural.action (q l) (s.coordinates w).toAdd) =
    BinaryLinearThree.FourNatural.action (a p (q l)) (η p (s.coordinates w).toAdd)
  have hs (k : L) (z : W) :
      (s.coordinates ⟨k*z*(k:G)⁻¹,
        (mem_normalizer_iff.mp (s.normalized k.property) z).mp z.property⟩).toAdd =
      BinaryLinearThree.FourNatural.action (q k) (s.coordinates z).toAdd := s.equivariant k z
  rw [←hs,hη,ha,hη,←hs]
  apply congrArg (fun z : W => (s.coordinates z).toAdd)
  apply Subtype.ext
  change (p : G)*((l : G)*w*(l : G)⁻¹)*(p : G)⁻¹ =
    ((p : G)*l*(p : G)⁻¹)*((p : G)*w*(p : G)⁻¹)*((p : G)*l*(p : G)⁻¹)⁻¹
  group

/-- Every original component normalizer acts innerly in the four-natural row. -/
theorem Context.normalizer_inner_of_four_natural_cover (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (p : normalizer (L : Set G)) :
    quotientAut (pCore 2 L) (L.normalizerMonoidHom p) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  have h := four_natural_common_normalizer_inner e s _ le_rfl
    ((le_inf c.escaping.component_normalizer le_rfl).trans
      (source_moved_normalizer_local_containment D)) p
  rw [←MulAut.map_innerSubgroup_congr e] at h
  exact (mem_map_iff_mem (MulAut.congr e).injective).mp h

/-- The literal point action on the original quotient contains no graph actor. -/
theorem Context.pointQuotientAction_inner_of_four_natural_cover (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (p : pointSylow T v) :
    c.pointQuotientAction e p ∈ MulAut.innerSubgroup BinaryLinearThree.Group := by
  rw [←MulAut.map_innerSubgroup_congr e]
  exact mem_map_of_mem _ (c.normalizer_inner_of_four_natural_cover e s
    (inclusion c.escaping.sylow_normalizes p))

private theorem four_natural_join_inner (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (p : pointSylow T v) :
    pCoreJoinAction 2 c.escaping.sylow_normalizes (inclusion le_sup_right p) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) :=
  c.normalizer_inner_of_four_natural_cover e s (inclusion c.escaping.sylow_normalizes p)

omit [Finite G] in
private theorem binary_quotient_center (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro x hx
  have h := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center BinaryLinearThree.Group at h
  rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at h
  exact e.map_eq_one_iff.mp h

/-- Adjoining the original point Sylow preserves the exact binary-three quotient.
The multiplicity action is absorbed only into the two-core of this join. -/
def Context.fourNaturalPointQuotientEquiv (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ((L ⊔ pointSylow T v : Subgroup G) ⧸ pCore 2 (L ⊔ pointSylow T v : Subgroup G)) ≃*
      BinaryLinearThree.Group :=
  (pCoreJoinQuotientEquivOfInner L (pointSylow T v) c.escaping.sylow_normalizes
    (T.isPGroup'.to_le inf_le_left) (binary_quotient_center e)
    (four_natural_join_inner c e s)).trans e

/-- The point-join equivalence retains the original marking on every element of L. -/
theorem Context.fourNaturalPointQuotientEquiv_on_component (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) (l : L) :
    c.fourNaturalPointQuotientEquiv e s
      (QuotientGroup.mk' (pCore 2 (L ⊔ pointSylow T v : Subgroup G))
        (inclusion le_sup_left l)) = e (QuotientGroup.mk' (pCore 2 L) l) := by
  change e ((pCoreJoinQuotientEquivOfInner _ _ _ _ _ _) _) = _
  rw [pCoreJoinQuotientEquivOfInner_on_component]

end CFSG.Quasithin.Chapter10.PointControl.Constrained
