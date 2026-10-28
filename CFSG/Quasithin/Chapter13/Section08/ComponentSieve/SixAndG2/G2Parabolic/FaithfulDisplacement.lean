module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.Offenders
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# Displacement on a faithful binary section

The source actor is the long-root four-group in the literal component, while
the representation on `V_H/U_H` is not assumed to be the natural module.  If
its displacement had dimension at most two, duality would make the same
elementary actor an offender on the dual faithful module.  Binary G₂ offender
rank then gives the required contradiction.  This is the arbitrary faithful
module input in the final G₂ parabolic estimate.

Source: Aschbacher–Smith, 13.8.27, with B.1.5 and B.4.2.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic

variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A faithful binary action of a self-centralizing derived G₂ component moves
every elementary rank-two actor in at least three dimensions. -/
theorem faithful_displacement_ge_three
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D) [L.Normal]
    [IsQuasisimple L] (hρ : Function.Injective ρ)
    (hcentral : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    {A : Subgroup D} (hA : IsElementaryTwo A) (hrank : rank A = 2) :
    3 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  by_contra hsmall
  have hfixed : fixedCodim ρ.dual A ≤ rank A := by
    rw [Representation.BinaryOffender.fixedCodim_dual_eq_moved_finrank]
    omega
  have hoff : IsOffender ρ.dual A := ⟨hA, hfixed⟩
  have hrank :=
    G2Recognition.offender_rank_ge_three ρ.dual L
      (faithful_dual ρ hρ) hcentral e hoff
  omega


/-- A literal derived G₂ model and the fitting equality make the source
component quasisimple and self-centralizing. -/
theorem component_properties_of_fitting
    (L : Subgroup D) (hfit : generalizedFitting D = L)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasisimple L ∧ centralizer (L : Set D) = ⊥ := by
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsSimpleGroup L := e.isSimpleGroup
  let : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center L = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h))
  let : IsQuasisimple L :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hc : centralizer (L : Set D) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxL : x ∈ L := by
      rw [← hfit] at hx ⊢
      exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hx
    have hxc : (⟨x, hxL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      exact Subtype.ext (mem_centralizer_iff.mp hx l l.property)
    rw [hz, mem_bot] at hxc
    exact congrArg Subtype.val hxc
  exact ⟨inferInstance, hc⟩

/-- The source fitting equality discharges the component normality and
self-centralizer premises of the faithful displacement theorem. -/
theorem faithful_displacement_ge_three_of_fitting
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D)
    (hfit : generalizedFitting D = L) (hρ : Function.Injective ρ)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    {A : Subgroup D} (hA : IsElementaryTwo A) (hrank : rank A = 2) :
    3 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  let : L.Normal := hfit ▸ inferInstance
  obtain ⟨hq, hc⟩ := component_properties_of_fitting L hfit e
  let := hq
  exact faithful_displacement_ge_three ρ L hρ hc e hA hrank

/-- The same rank-two actor has fixed codimension at least three on every
faithful binary module, including the actual core-comparison section. -/
theorem faithful_fixedCodim_ge_three_of_fitting
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D)
    (hfit : generalizedFitting D = L) (hρ : Function.Injective ρ)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    {A : Subgroup D} (hA : IsElementaryTwo A) (hrank : rank A = 2) :
    3 ≤ fixedCodim ρ A := by
  let : L.Normal := hfit ▸ inferInstance
  obtain ⟨hq, hc⟩ := component_properties_of_fitting L hfit e
  let := hq
  by_contra hsmall
  have ho : IsOffender ρ A := ⟨hA, by omega⟩
  have hb := G2Recognition.offender_rank_ge_three ρ L hρ hc e ho
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
