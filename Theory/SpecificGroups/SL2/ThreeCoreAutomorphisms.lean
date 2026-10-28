module

public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.SpecificGroups.SL2.ThreeCharacteristicTwo
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.CentralDisplacementOddIndex
public import Theory.GroupTheory.PPerfectHom

/-!
# Automorphisms detected on the quaternion core of SL₂(3)

An automorphism fixing the two-core pointwise has displacement in its
centralizer. The quaternion core is self-centralizing, so this displacement
lies in its center. That center has order two and is normal, hence central
in SL₂(3). Two-perfection makes the central displacement homomorphism
trivial. Transport through an arbitrary model equivalence then shows that
an ambient element normalizing an SL₂(3) subgroup and centralizing its
embedded two-core centralizes the whole subgroup.

This is the residual-factor lifting step used in Aschbacher--Smith,
combined manuscript of 1 March 2004, printed p.546.
-/

public section
open Subgroup GLS3.Chapter5.SchurPresentation
namespace Matrix.SpecialLinearGroup

private theorem three_twoCore_center_central :
    (center (pCore 2 (SpecialLinearGroup (Fin 2) (ZMod 3)))).map
      (pCore 2 (SpecialLinearGroup (Fin 2) (ZMod 3))).subtype ≤
        center (SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  let Q := pCore 2 (SpecialLinearGroup (Fin 2) (ZMod 3))
  let Z := (center Q).map Q.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  apply central_of_normal_card_two Z
  rw [card_map_of_injective Q.subtype_injective]
  have hc := Nat.card_congr (centerCongr sl23_twoCoreEquiv).toEquiv
  change Nat.card (center Q) = Nat.card (center (QuaternionGroup 2)) at hc
  rw [hc, Nat.card_eq_fintype_card]
  decide

/-- Restriction to the actual two-core detects every automorphism of SL₂(3). -/
theorem three_aut_eq_one_of_fix_twoCore
    (a : MulAut (SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hfix : ∀ x ∈ pCore 2 (SpecialLinearGroup (Fin 2) (ZMod 3)), a x = x) :
    a = 1 := by
  let Q := pCore 2 (SpecialLinearGroup (Fin 2) (ZMod 3))
  let Z := (center Q).map Q.subtype
  have hd (g : SpecialLinearGroup (Fin 2) (ZMod 3)) : g⁻¹ * a g ∈ Z := by
    have hc : g⁻¹ * a g ∈ centralizer (Q : Set _) := by
      intro x hx
      have hxg : g * x * g⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem x hx g
      have he := hfix (g * x * g⁻¹) hxg
      rw [map_mul, map_mul, map_inv, hfix x hx] at he
      calc
        x * (g⁻¹ * a g) = g⁻¹ * (g * x * g⁻¹) * a g := by group
        _ = g⁻¹ * (a g * x * (a g)⁻¹) * a g := by rw [he]
        _ = (g⁻¹ * a g) * x := by group
    have hq : g⁻¹ * a g ∈ Q := three_twoCore_self_centralizing hc
    refine ⟨⟨g⁻¹ * a g, hq⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro q
    exact Subtype.ext (hc q q.property)
  let δ := MulAut.centralDisplacement Z three_twoCore_center_central a hd
  have hZ : IsPGroup 2 Z :=
    ((pCore_isPGroup (p := 2) (G := SpecialLinearGroup (Fin 2) (ZMod 3))).to_subgroup
      (center Q)).map Q.subtype
  have hδ := sl23_twoPerfect.hom_eq_one_of_isPGroup hZ δ
  apply MulEquiv.ext
  intro g
  have he := congrArg (fun k : SpecialLinearGroup (Fin 2) (ZMod 3) →* Z => (k g :
      SpecialLinearGroup (Fin 2) (ZMod 3))) hδ
  change g⁻¹ * a g = 1 at he
  exact (inv_mul_eq_one.mp he).symm

/-- The same detection statement under an arbitrary SL₂(3) marking. -/
theorem aut_eq_one_of_fix_twoCore_of_equiv_three
    {I : Type*} [Group I] (e : I ≃* SpecialLinearGroup (Fin 2) (ZMod 3))
    (a : MulAut I) (hfix : ∀ x ∈ pCore 2 I, a x = x) : a = 1 := by
  apply (MulAut.congr e).injective
  rw [map_one]
  apply three_aut_eq_one_of_fix_twoCore
  intro x hx
  have hx' : e.symm x ∈ pCore 2 I := by
    rw [← pCore_map_iso 2 e] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  change e (a (e.symm x)) = x
  rw [hfix _ hx', e.apply_symm_apply]

/-- Centralizing the embedded two-core detects centralization of the whole factor. -/
theorem centralizes_of_normalizes_of_centralizes_twoCore
    {G : Type*} [Group G] (I : Subgroup G)
    (e : I ≃* SpecialLinearGroup (Fin 2) (ZMod 3)) (y : G)
    (hynorm : y ∈ normalizer (I : Set G))
    (hycore : y ∈ centralizer ((pCore 2 I).map I.subtype : Set G)) :
    y ∈ centralizer (I : Set G) := by
  let n : normalizer (I : Set G) := ⟨y, hynorm⟩
  have ha : I.normalizerMonoidHom n = 1 := by
    apply aut_eq_one_of_fix_twoCore_of_equiv_three e
    intro x hx
    apply Subtype.ext
    change y * (x : G) * y⁻¹ = (x : G)
    have hc := hycore x (mem_map_of_mem I.subtype hx)
    rw [← hc, mul_inv_cancel_right]
  have hn : n ∈ I.normalizerMonoidHom.ker := ha
  rw [I.normalizerMonoidHom_ker] at hn
  exact hn

end Matrix.SpecialLinearGroup
