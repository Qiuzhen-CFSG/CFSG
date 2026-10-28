module
public import Theory.Representation.PSL3Two.ParabolicFixedFree
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.PGroupCore
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Stellmacher.OmegaOneCenterMap

/-!
# Doubled natural action excludes a central four-group

Suppose G=K O₂(G), and a normal elementary subgroup U≤O₂(G) is a direct
sum of two natural binary three-spaces for K. If O₂(G) centralizes U,
each summand is normal in G and has a nonidentity Sylow-central point.
These points span a central four-group. Any further central involution
centralizing K cannot belong to U, since the doubled natural module has
no fixed vectors. Hence Ω₁Z(S) cannot have order four.

The source application excludes the doubled whole reduced moved module
in 13.4.10(4), using its independently constructed natural omega-orbit and
central four-group. All normality here is relative to the displayed G.
Source: Aschbacher–Smith 13.4.10(4–5), printed pp.907–909.
-/

public noncomputable section
namespace Theory.GroupTheory
open Subgroup Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem elementary_normal_fixed_point (S : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≠ ⊥) (hAS : A ≤ S)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) :
    ∃ x ∈ A, x ≠ 1 ∧ x ∈ omegaOneCenterAmbient (S : Subgroup G) := by
  let Ai := A.subgroupOf (S : Subgroup G)
  let : Ai.Normal := normal_subgroupOf_of_le_normalizer hn
  have hAi : Ai ≠ ⊥ := by
    intro hh
    have hm := congrArg (map (S : Subgroup G).subtype) hh
    rw [map_subgroupOf_eq_of_le hAS,Subgroup.map_bot] at hm
    exact hA hm
  have hc := center_inf_ne_bot_of_normal S.isPGroup' Ai hAi
  obtain ⟨x,hx,hx1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp ((Subgroup.nontrivial_iff_ne_bot _).mpr hc)
  refine ⟨x.val,hx.2,fun hh => hx1 (Subtype.ext hh),?_⟩
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨x.property,elemPow_eq_one_of_isElementaryAbelian x.val hx.2,
      fun s hs => congrArg Subtype.val (mem_center_iff.mp hx.1 ⟨s,hs⟩)⟩

/-- A doubled natural module and an independent central involution force at
least three central involution generators when the component supplements O₂. -/
theorem doubled_natural_not_central_four
    (S : Sylow 2 G) (K U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hgen : K ⊔ pCore 2 G = ⊤)
    (hU : U ≤ pCore 2 G) (hc : pCore 2 G ≤ centralizer (U : Set G))
    (q : K →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : ∀ (k : K) (v : U), (e (MulAut.conjNormal k.val v)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (e v).toAdd)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (S : Subgroup G)) (hz1 : z ≠ 1)
    (hzK : z ∈ centralizer (K : Set G)) :
    Nat.card (omegaOneCenterAmbient (S : Subgroup G)) ≠ 4 := by
  let Z := omegaOneCenterAmbient (S : Subgroup G)
  let c (i : Fin 2) : Multiplicative BinaryLinearThree.Vector →*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector) :=
    { toFun := fun x => Multiplicative.ofAdd (if i = 0 then (0,x.toAdd) else (x.toAdd,0))
      map_one' := by split_ifs <;> rfl
      map_mul' := fun x y => by split_ifs <;> rfl }
  have ci (i : Fin 2) : Function.Injective (c i) := by
    intro x y hxy
    fin_cases i
    · exact congrArg (fun v => v.toAdd.2) hxy
    · exact congrArg (fun v => v.toAdd.1) hxy
  let f (i : Fin 2) : Multiplicative BinaryLinearThree.Vector →* G :=
    U.subtype.comp (e.symm.toMonoidHom.comp (c i))
  let A (i : Fin 2) := (f i).range
  have hAU (i : Fin 2) : A i ≤ U := by
    rintro _ ⟨v,rfl⟩
    exact (e.symm (c i v)).property
  have hAn (i : Fin 2) : (⊤ : Subgroup G) ≤ normalizer (A i : Set G) := by
    rw [←hgen]
    apply sup_le
    · apply le_normalizer_iff.mpr
      intro k hk x hx
      obtain ⟨v,rfl⟩ := hx
      have hx' : e (MulAut.conjNormal k (e.symm (c i v))) ∈
          (c i).range := by
        refine ⟨Multiplicative.ofAdd (BinaryLinearThree.W (q ⟨k,hk⟩) v.toAdd),?_⟩
        apply Multiplicative.toAdd.injective
        rw [he ⟨k,hk⟩,e.apply_symm_apply]
        fin_cases i <;> simp [c,Representation.prod,map_zero]
      obtain ⟨w,hw⟩ := hx'
      refine ⟨w,?_⟩
      exact congrArg Subtype.val (e.symm_apply_eq.mpr hw)
    · exact (hc.trans (centralizer_le (hAU i))).trans (Subgroup.centralizer_le_normalizer _)
  have hAe (i : Fin 2) : IsElementaryAbelian 2 (A i) := IsElementaryAbelian.of_le (hAU i)
  have hAc (i : Fin 2) : Nat.card (A i) = 8 := by
    have hi : Function.Injective (f i) := U.subtype_injective.comp
      (e.symm.injective.comp (ci i))
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    change Nat.card BinaryLinearThree.Vector = 8
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  have hex (i : Fin 2) : ∃ x ∈ A i, x ≠ 1 ∧ x ∈ Z := by
    let := hAe i
    exact elementary_normal_fixed_point S (A i)
      (fun hh => by have h := hAc i; rw [hh,Subgroup.card_bot] at h; omega)
      ((hAU i).trans (hU.trans (pCore_isPGroup.le_sylow_of_normal S)))
      (le_top.trans (hAn i))
  obtain ⟨x,hx,hx1,hxZ⟩ := hex 0
  obtain ⟨y,hy,hy1,hyZ⟩ := hex 1
  have hdis : Disjoint (A 0) (A 1) := by
    apply disjoint_iff_inf_le.mpr
    intro w hw
    obtain ⟨a,ha⟩ := hw.1
    obtain ⟨b,hb⟩ := hw.2
    have hh : c 0 a =
        c 1 b :=
      e.symm.injective (Subtype.ext (ha.trans hb.symm))
    have ha0 : a = 1 := congrArg (fun v => v.toAdd.2) hh
    rw [←ha,ha0,map_one]
    exact one_mem _
  let X := zpowers x
  let Y := zpowers y
  have hXY : Disjoint X Y := hdis.mono (zpowers_le.mpr hx) (zpowers_le.mpr hy)
  have hXZ : X ≤ Z := zpowers_le.mpr hxZ
  have hYZ : Y ≤ Z := zpowers_le.mpr hyZ
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hnorm : Y ≤ normalizer (X : Set G) :=
    ((hYZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
      (centralizer_le hXZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hcx : Nat.card X = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hxZ).2.1 hx1
  have hcy : Nat.card Y = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hyZ).2.1 hy1
  have hfour : Nat.card (X ⊔ Y : Subgroup G) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint X Y hnorm hXY,hcx,hcy]
  intro hZ
  have hEq : X ⊔ Y = Z := eq_of_le_of_card_ge (sup_le hXZ hYZ) (by rw [hfour,hZ])
  have hZU : Z ≤ U := hEq ▸ sup_le ((zpowers_le.mpr hx).trans (hAU 0))
    ((zpowers_le.mpr hy).trans (hAU 1))
  let v : U := ⟨z,hZU hz⟩
  have hfix (k : BinaryLinearThree.Group) :
      (BinaryLinearThree.W.prod BinaryLinearThree.W) k (e v).toAdd = (e v).toAdd := by
    obtain ⟨k,rfl⟩ := hq k
    rw [←he k v]
    congr 2
    apply Subtype.ext
    change k.val * z * k.val⁻¹ = z
    rw [hzK k.val k.property,mul_inv_cancel_right]
  have hv : (e v).toAdd = 0 := BinaryLinearThree.ParabolicFixedFree.doubled_fixed_eq_zero
    (e v).toAdd (fun k _ => hfix k)
  exact hz1 (congrArg Subtype.val (e.map_eq_one_iff.mp hv))
end Theory.GroupTheory
