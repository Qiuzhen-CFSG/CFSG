module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.CoordinateModel
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.TorusSeparation
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation

/-!
# Reduction of actual centralizer connectedness to two torus cases

Conjugation gives an algebraic isomorphism between the literal closed
centralizers. Thus the permitted geometric torus-normal-form hypothesis
reduces connectedness for a nonidentity odd-order element to its torus
representative. The two explicit remaining cases distinguish whether one
of the six nonconstant octonion weights is one.

Neither case is proved here. In particular, the case with no such fixed weight
still includes repeated eigenvalues and the order-three centralizer; it must
not be replaced by a distinct-eigenvalue hypothesis.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 8.5 and 12.5. The
weights are those of the actual octonion torus, as defined in the licensed
ATLAS port `Theory.AtlasPort.LinearGroups.G2.Torus` (`LICENSES/ATLAS.txt`).
-/

public section

open Theory.AlgebraicGroup
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem centralizerClosedSubgroup_conjugate (g c : Model K) :
    centralizerClosedSubgroup (c * g * c⁻¹) =
      (centralizerClosedSubgroup g).conjugate (modelPointEquiv.symm c) := by
  apply SetLike.coe_injective
  ext x
  change x ∈ (centralizerClosedSubgroup (c * g * c⁻¹)).toSubgroup ↔
    x ∈ (centralizerClosedSubgroup g).conjugate (modelPointEquiv.symm c)
  rw [ClosedSubgroup.mem_conjugate_iff]
  change x ∈ Subgroup.centralizer {modelPointEquiv.symm (c * g * c⁻¹)} ↔
    (modelPointEquiv.symm c)⁻¹ * x * modelPointEquiv.symm c ∈
      Subgroup.centralizer {modelPointEquiv.symm g}
  simp only [Subgroup.mem_centralizer_singleton_iff, map_mul, map_inv]
  let a := modelPointEquiv.symm c
  let b := modelPointEquiv.symm g
  change x * (a * b * a⁻¹) = (a * b * a⁻¹) * x ↔
    a⁻¹ * x * a * b = b * (a⁻¹ * x * a)
  constructor
  · intro h
    calc
      _ = a⁻¹ * (x * (a * b * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * b * a⁻¹) * x) * a := by rw [h]
      _ = _ := by group
  · intro h
    calc
      _ = a * (a⁻¹ * x * a * b) * a⁻¹ := by group
      _ = a * (b * (a⁻¹ * x * a)) * a⁻¹ := by rw [h]
      _ = _ := by group

theorem centralizer_connected_conjugate (g c : Model K)
    (h : Variety.IsConnected (centralizerVariety g)) :
    Variety.IsConnected (centralizerVariety (c * g * c⁻¹)) := by
  change Variety.IsConnected (centralizerClosedSubgroup (c * g * c⁻¹)).carrierVariety
  rw [centralizerClosedSubgroup_conjugate]
  let := ((centralizerClosedSubgroup g).conjugate (modelPointEquiv.symm c)).carrierAlgebraicGroup
  let e := (centralizerClosedSubgroup g).conjugateIso (modelPointEquiv.symm c)
  exact connected_of_surjective_morphism e.hom h (fun y => ⟨e.inv.onPoints y, e.inv_hom_id y⟩)

theorem centralizer_connected_of_isConj {g h : Model K} (hc : IsConj g h)
    (hh : Variety.IsConnected (centralizerVariety h)) :
    Variety.IsConnected (centralizerVariety g) := by
  obtain ⟨c,hc⟩ := isConj_iff.mp hc.symm
  rw [← hc]
  exact centralizer_connected_conjugate h c hh

theorem centralizer_connected_of_torus_cases
    (hgeom : ∀ x : Model K, ¬ 2 ∣ orderOf x →
      ∃ l m : Kˣ, IsConj x (torus l m))
    (hnoFixedWeight : ∀ l m : Kˣ, l ≠ 1 → m ≠ 1 → l ≠ m →
      Variety.IsConnected (centralizerVariety (torus l m)))
    (hfixedWeight : ∀ l m : Kˣ, torus l m ≠ 1 →
      (l = 1 ∨ m = 1 ∨ l = m) →
      Variety.IsConnected (centralizerVariety (torus l m)))
    (g : Model K) (hg : ¬ 2 ∣ orderOf g) (hg1 : g ≠ 1) :
    Variety.IsConnected (centralizerVariety g) := by
  obtain ⟨l,m,hc⟩ := hgeom g hg
  apply centralizer_connected_of_isConj hc
  have ht : torus l m ≠ 1 := by
    intro he
    rw [he] at hc
    exact hg1 (isConj_one_right.mp hc.symm)
  by_cases hl : l = 1
  · exact hfixedWeight l m ht
      (Or.inl hl)
  by_cases hm : m = 1
  · exact hfixedWeight l m ht
      (Or.inr (Or.inl hm))
  by_cases he : l = m
  · exact hfixedWeight l m ht
      (Or.inr (Or.inr he))
  exact hnoFixedWeight l m hl hm he

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
