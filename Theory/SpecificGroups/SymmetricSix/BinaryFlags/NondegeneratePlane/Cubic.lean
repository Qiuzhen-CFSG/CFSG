module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Stabilizer
public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups
public import Theory.ElementaryAbelian.Basic

/-!
# The two cubic axes of the native plane stabilizer

The block embedding sends the two alternating groups of degree three to
commuting, disjoint normal cubic subgroups. Their join is elementary of order
nine and lies in A₆. Inside the actual plane stabilizer it consists exactly
of the elements whose cube is one, so it is characteristic. The explicit
cycles (012) and (345) retain the native action marking.

Source: Aschbacher--Smith, 13.5.6, printed p.917, the two cubic directions
used to construct the two A₃ blocks.
-/

@[expose] public section

open Subgroup BinaryPermutation Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
open NaturalGeometry NaturalPairing Representation.BinaryOffender
open SymmetricThreeProduct

def cubicLeft : Subgroup S := leftThree.map tripleProductHom
def cubicRight : Subgroup S := rightThree.map tripleProductHom
def nineCore : Subgroup S := (threeCore.prod threeCore).map tripleProductHom

theorem cubicLeft_card : Nat.card cubicLeft = 3 := by
  rw [cubicLeft, card_map_of_injective tripleProductHom_injective, card_leftThree]
theorem cubicRight_card : Nat.card cubicRight = 3 := by
  rw [cubicRight, card_map_of_injective tripleProductHom_injective, card_rightThree]
theorem nineCore_card : Nat.card nineCore = 9 := by
  rw [nineCore, card_map_of_injective tripleProductHom_injective, Nat.card_eq_fintype_card]
  decide

theorem cubic_sup : cubicLeft ⊔ cubicRight = nineCore := by
  rw [cubicLeft,cubicRight,nineCore, ← Subgroup.map_sup]
  congr 1
  ext x
  constructor
  · intro hx
    have hl : leftThree ≤ threeCore.prod threeCore := by
      intro y hy
      refine ⟨hy.1,?_⟩
      change y.2 ^ 3 = 1
      rw [mem_bot.mp hy.2,one_pow]
    have hr : rightThree ≤ threeCore.prod threeCore := by
      intro y hy
      refine ⟨?_,hy.2⟩
      change y.1 ^ 3 = 1
      rw [mem_bot.mp hy.1,one_pow]
    exact sup_le hl hr hx
  · intro hx
    have hl : (x.1,1) ∈ leftThree := ⟨hx.1,mem_bot.mpr rfl⟩
    have hr : (1,x.2) ∈ rightThree := ⟨mem_bot.mpr rfl,hx.2⟩
    simpa using (leftThree ⊔ rightThree).mul_mem (mem_sup_left hl) (mem_sup_right hr)

theorem cubic_disjoint : Disjoint cubicLeft cubicRight := by
  rw [disjoint_iff, cubicLeft,cubicRight, ← map_inf _ _ _ tripleProductHom_injective]
  have h : leftThree ⊓ rightThree = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact mem_bot.mpr (Prod.ext (mem_bot.mp hx.2.1) (mem_bot.mp hx.1.2))
  rw [h,Subgroup.map_bot]

theorem cubic_commute (x y : S) (hx : x ∈ cubicLeft) (hy : y ∈ cubicRight) :
    Commute x y := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  apply Commute.map
  have ha2 : a.2 = 1 := mem_bot.mp ha.2
  have hb1 : b.1 = 1 := mem_bot.mp hb.1
  change a * b = b * a
  apply Prod.ext <;> simp [ha2,hb1]

theorem nineCore_le : nineCore ≤ planeStabilizer := by
  rintro _ ⟨x,hx,rfl⟩
  exact tripleProduct_mem x

theorem mem_nineCore_iff (g : S) : g ∈ nineCore ↔ g ∈ planeStabilizer ∧ g ^ 3 = 1 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨tripleProduct_mem x,?_⟩
    have hp : x ^ 3 = 1 := Prod.ext hx.1 hx.2
    rw [← map_pow,hp,map_one]
  · rintro ⟨hg,hpow⟩
    have hg' : g ∈ tripleProductHom.range := tripleProduct_range.symm ▸ hg
    obtain ⟨x,rfl⟩ := hg'
    have hp : x ^ 3 = 1 := tripleProductHom_injective (by simpa only [map_pow,map_one] using hpow)
    exact ⟨x,⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩,rfl⟩

instance nineCore_characteristic : (nineCore.subgroupOf planeStabilizer).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  change (a x : S) ∈ nineCore
  apply (mem_nineCore_iff _).mpr
  refine ⟨(a x).property,?_⟩
  have hp : x ^ 3 = 1 := Subtype.ext ((mem_nineCore_iff x).mp hx).2
  exact congrArg Subtype.val (by rw [← map_pow,hp,map_one] : (a x)^3=1)

instance nineCore_elementary : IsElementaryAbelian 3 nineCore := by
  let : IsElementaryAbelian 3 (threeCore.prod threeCore) := {
    is_comm.comm := by
      intro x y
      apply Subtype.ext
      exact (show ∀ x y : SymmetricThreeProduct.G,
        x ∈ threeCore.prod threeCore → y ∈ threeCore.prod threeCore → x*y=y*x by decide) _ _ x.property y.property
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      exact Prod.ext x.property.1 x.property.2 }
  exact IsElementaryAbelian.map tripleProductHom

theorem nineCore_even : nineCore ≤ alternatingGroup Ω := by
  rintro _ ⟨x,hx,rfl⟩
  exact (show ∀ x : TriplePerm × TriplePerm, x ∈ threeCore.prod threeCore →
    (tripleProductHom x).sign=1 by decide) x hx


theorem stabilizer_normalizes_left : planeStabilizer ≤ normalizer (cubicLeft : Set S) := by
  let _ : leftThree.Normal := inferInstanceAs ((threeCore.prod (⊥ : Subgroup TriplePerm)).Normal)
  have h := Subgroup.le_normalizer_map (H := leftThree) tripleProductHom
  rw [Subgroup.normalizer_eq_top] at h
  simpa only [← MonoidHom.range_eq_map,tripleProduct_range,cubicLeft] using h

theorem stabilizer_normalizes_right : planeStabilizer ≤ normalizer (cubicRight : Set S) := by
  let _ : rightThree.Normal := inferInstanceAs (((⊥ : Subgroup TriplePerm).prod threeCore).Normal)
  have h := Subgroup.le_normalizer_map (H := rightThree) tripleProductHom
  rw [Subgroup.normalizer_eq_top] at h
  simpa only [← MonoidHom.range_eq_map,tripleProduct_range,cubicRight] using h

abbrev cycleLeft : S := swap 0 1 * swap 1 2
abbrev cycleRight : S := swap 3 4 * swap 4 5

theorem cycleLeft_mem : cycleLeft ∈ cubicLeft := by
  refine ⟨(swap 0 1 * swap 1 2,1),?_,?_⟩
  · change (swap (0 : Fin 3) 1 * swap 1 2)^3=1 ∧ (1 : TriplePerm)=1
    decide
  · decide

theorem cycleRight_mem : cycleRight ∈ cubicRight := by
  refine ⟨(1,swap 0 1 * swap 1 2),?_,?_⟩
  · change (1 : TriplePerm)=1 ∧ (swap (0 : Fin 3) 1 * swap 1 2)^3=1
    decide
  · decide

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
