module
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Mathlib.GroupTheory.Nilpotent
public import Theory.ElementaryAbelian.Basic

/-!
# A normal A₄ subgroup centralizes the third term of a two-group

A two-group of automorphisms of A₄ embeds in a Sylow two-subgroup of S₄,
hence in D₈. Its third lower-central term is trivial. Thus an A₄ subgroup
normalized by T centralizes the actual third lower-central term of T.
When this term is nontrivial, characteristic-normalizer control contains A₄.
This is the terminal characteristic-subgroup argument of C.1.29, p.134.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup

/-- A square moving an elementary normal subgroup detects a nontrivial
third lower-central term, without computing the full nilpotency class. -/
theorem third_ne_bot_of_square_movement
    {G : Type*} [Group G] (T V : Subgroup G)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : T ≤ normalizer (V : Set G))
    (t v : G) (ht : t ∈ T) (hv : v ∈ V)
    (hm : t ^ 2 * v * (t ^ 2)⁻¹ ≠ v) :
    (⊤ : Subgroup T).lowerCentralSeries 2 ≠ ⊥ := by
  intro hthird
  have hclass : _root_.commutator T ≤ center T :=
    commutator_top_right_eq_bot_iff_le_center.mp hthird
  let c : G := ⁅t,v⁆
  have hcV : c ∈ V := V.mul_mem ((hTV ht v).mp hv) (V.inv_mem hv)
  have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) c hcV
  have hct : t * c = c * t := by
    have hc := hclass (commutator_mem_commutator
      (mem_top (⟨t,ht⟩ : T)) (mem_top (⟨v,hVT hv⟩ : T)))
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨t,ht⟩)
  have he : t * v * t⁻¹ = c * v := by dsimp [c]; group
  apply hm
  calc
    t ^ 2 * v * (t ^ 2)⁻¹ = t * (t * v * t⁻¹) * t⁻¹ := by rw [pow_two]; group
    _ = t * (c * v) * t⁻¹ := by rw [he]
    _ = c * (t * v * t⁻¹) := by rw [← mul_assoc, hct]; group
    _ = c * (c * v) := by rw [he]
    _ = v := by rw [← mul_assoc, ← pow_two, hc2, one_mul]
end Subgroup

namespace alternatingGroup.FourThirdCentralizer

private theorem dihedral_third :
    (⊤ : Subgroup (DihedralGroup 4)).lowerCentralSeries 2 = ⊥ := by
  apply commutator_top_right_eq_bot_iff_le_center.mpr
  change _root_.commutator (DihedralGroup 4) ≤ center (DihedralGroup 4)
  rw [_root_.commutator_eq_closure, closure_le]
  rintro d ⟨x, y, rfl⟩
  apply mem_center_iff.mpr
  intro z
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    (show ⁅⁅x,y⁆,z⁆ = 1 by revert x y z; decide +kernel)).symm

/-- Every two-group action on A₄ kills the actual third lower-central term. -/
theorem third_le_action_kernel
    {T Y : Type*} [Group T] [Group Y] [Finite T]
    (hp : IsPGroup 2 T) (eY : Y ≃* alternatingGroup (Fin 4))
    (a : T →* MulAut Y) : (⊤ : Subgroup T).lowerCentralSeries 2 ≤ a.ker := by
  let eA : MulAut Y ≃* Equiv.Perm (Fin 4) :=
    (MulAut.congr eY).trans AlternatingFourPair.eA.symm
  let f : T →* Equiv.Perm (Fin 4) := eA.toMonoidHom.comp a
  have hf : IsPGroup 2 f.range := hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hf.exists_le_sylow
  obtain ⟨eP⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  let fP : T →* P := f.codRestrict P (fun x => hP ⟨x, rfl⟩)
  let F : T →* DihedralGroup 4 := eP.toMonoidHom.comp fP
  have hm : ((⊤ : Subgroup T).lowerCentralSeries 2).map F = ⊥ := by
    apply le_bot_iff.mp
    rw [map_lowerCentralSeries]
    exact (lowerCentralSeries_mono 2 le_top).trans dihedral_third.le
  intro x hx
  have hF : F x = 1 := ((Subgroup.map_eq_bot_iff _).mp hm) hx
  have hxP : fP x = 1 := eP.map_eq_one_iff.mp hF
  have hxf : f x = 1 := congrArg Subtype.val hxP
  exact eA.map_eq_one_iff.mp hxf

/-- The same statement for the literal conjugation action of a normalized
subgroup of an ambient group. -/
theorem third_centralizes
    {G : Type*} [Group G] [Finite G]
    (T Y : Subgroup G) (hp : IsPGroup 2 T)
    (hTY : T ≤ normalizer (Y : Set G))
    (eY : Y ≃* alternatingGroup (Fin 4)) :
    ((⊤ : Subgroup T).lowerCentralSeries 2).map T.subtype ≤ centralizer (Y : Set G) := by
  let a := Y.normalizerMonoidHom.comp (Subgroup.inclusion hTY)
  have hk := third_le_action_kernel hp eY a
  rintro x ⟨t, ht, rfl⟩
  have hh := hk ht
  change Subgroup.inclusion hTY t ∈ Y.normalizerMonoidHom.ker at hh
  rw [normalizerMonoidHom_ker] at hh
  exact hh

/-- A nontrivial characteristic third term supplies the exact C(G,T)
containment used in the ordinary A₇ exclusion. -/
theorem le_characteristicNormalizerClosure
    {G : Type*} [Group G] [Finite G]
    (T Y : Subgroup G) (hp : IsPGroup 2 T)
    (hTY : T ≤ normalizer (Y : Set G))
    (eY : Y ≃* alternatingGroup (Fin 4))
    (hne : (⊤ : Subgroup T).lowerCentralSeries 2 ≠ ⊥) :
    Y ≤ T.characteristicNormalizerClosure := by
  have hc := le_centralizer_iff.mp (third_centralizes T Y hp hTY eY)
  exact hc.trans ((centralizer_le_normalizer _).trans
    (normalizer_le_characteristicNormalizerClosure T _ hne))
end alternatingGroup.FourThirdCentralizer
