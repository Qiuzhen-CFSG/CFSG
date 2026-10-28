module
public import Theory.GroupAction.SixteenOddComplements.Splitting
public import Theory.GroupAction.SixteenOddComplements.CubicTransvection
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
/-!
# Invariant binary planes for a symmetric-three product with a transvection

The two normal cubic axes of S₃×S₃ both have nonzero fixed groups in a
faithful action on binary16 containing a transvection. Their joint order-nine
actor fixes only the identity. The two fixed groups intersect trivially;
orbit counting makes each have at least four elements, so each is a plane
and together they exhaust the sixteen. Normality preserves both planes.

These are the intrinsic factors needed for Aschbacher--Smith F.5.7, p.303.
The statement uses the supplied actor homomorphism and actual fixed groups.
-/
open Subgroup
open scoped IsMulCommutative
namespace SixteenOddComplements
public theorem invariant_planes_of_normal_cubics
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (D K L : Subgroup (MulAut E))
    (hK : Nat.card K=3) (hL : Nat.card L=3) (hKL : Nat.card (K⊔L : Subgroup (MulAut E))=9)
    (hKD : K≤D) (hLD : L≤D)
    (hnK : D≤normalizer (K : Set (MulAut E)))
    (hnL : D≤normalizer (L : Set (MulAut E)))
    (t : MulAut E) (htD : t∈D) (ht : Nat.card t.fixedSubgroup=8) :
    ∃ U W : Subgroup E, Nat.card U=4 ∧ Nat.card W=4 ∧ Disjoint U W ∧
      (∀ d:D, ∀ x∈U, (d : MulAut E) x∈U) ∧
      (∀ d:D, ∀ x∈W, (d : MulAut E) x∈W) := by
  let U := FixedPoints.subgroup K E
  let W := FixedPoints.subgroup L E
  let : IsInvariant D E U := fixedPoints_isInvariant_of_normalizing_actor D K hnK
  let : IsInvariant D E W := fixedPoints_isInvariant_of_normalizing_actor D L hnL
  have hUb : U≠⊥ := cubic_fixed_ne_bot_of_transvection_normalizer hE K hK t ht (hnK htD)
  have hWb : W≠⊥ := cubic_fixed_ne_bot_of_transvection_normalizer hE L hL t ht (hnL htD)
  have hwhole := fixed_eq_bot_of_nine hE (K⊔L) hKL
  have hi : U⊓W=⊥ := by
    apply bot_unique
    intro x hx
    have hKst : K≤MulAction.stabilizer (MulAut E) x := fun a ha => hx.1 ⟨a,ha⟩
    have hLst : L≤MulAction.stabilizer (MulAut E) x := fun a ha => hx.2 ⟨a,ha⟩
    exact hwhole.le (show x∈FixedPoints.subgroup (K⊔L : Subgroup (MulAut E)) E from fun a => (sup_le hKst hLst) a.property)
  have lower (Y Z : Subgroup (MulAut E)) (hZ : Nat.card Z=3)
      (hn : Z≤normalizer (Y : Set (MulAut E)))
      (hi : FixedPoints.subgroup Y E ⊓ FixedPoints.subgroup Z E=⊥)
      (hb : FixedPoints.subgroup Y E≠⊥) : 4≤Nat.card (FixedPoints.subgroup Y E) := by
    let C := FixedPoints.subgroup Y E
    let : IsInvariant Z E C := fixedPoints_isInvariant_of_normalizing_actor Z Y hn
    have hf : FixedPoints.subgroup Z C=⊥ := by
      apply bot_unique
      intro x hx
      apply Subtype.ext
      exact hi.le ⟨x.property,fun z => congrArg Subtype.val (hx z)⟩
    have hm := (IsPGroup.of_card (n:=1) (by simpa using hZ)).card_modEq_card_fixedPoints C
    change Nat.ModEq 3 (Nat.card C) (Nat.card (FixedPoints.subgroup Z C)) at hm
    rw [hf,card_bot,Nat.ModEq] at hm
    have hne : Nat.card C≠1 := fun hh => hb (card_eq_one.mp hh)
    have hp : 0<Nat.card C := Nat.card_pos
    change 4≤Nat.card C
    omega
  have hU := lower K L hL (hLD.trans hnK) hi hUb
  have hW := lower L K hK (hKD.trans hnL) (by rwa [inf_comm]) hWb
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes U W
    (by rw [normalizer_eq_top];exact le_top)
  rw [hi,card_bot,one_mul] at hc
  have hb := card_le_card_group (U⊔W)
  rw [←hc,hE] at hb
  have hUc : Nat.card U=4 := by nlinarith
  have hWc : Nat.card W=4 := by nlinarith
  exact ⟨U,W,hUc,hWc,disjoint_iff.mpr hi,
    fun d x hx => (IsInvariant.invariant (A:=D) d x).mp hx,
    fun d x hx => (IsInvariant.invariant (A:=D) d x).mp hx⟩
end SixteenOddComplements

namespace SixteenOddComplements
public theorem invariant_planes_of_symmetric_three_pair
    {E D : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E] [Group D]
    (hE : Nat.card E=16) (e : D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (f : D →* MulAut E) (hf : Function.Injective f)
    (t : D) (ht : Nat.card (f t).fixedSubgroup=8) :
    ∃ U W : Subgroup E, Nat.card U=4 ∧ Nat.card W=4 ∧ Disjoint U W ∧
      (∀ d:D, ∀ x∈U, f d x∈U) ∧ (∀ d:D, ∀ x∈W, f d x∈W) := by
  let S := Equiv.Perm (Fin 3)
  let K0 : Subgroup (S×S) := (alternatingGroup (Fin 3)).prod ⊥
  let L0 : Subgroup (S×S) := (⊥ : Subgroup S).prod (alternatingGroup (Fin 3))
  let φ := f.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := hf.comp e.symm.injective
  let K := K0.map φ
  let L := L0.map φ
  have hthree : Nat.card (alternatingGroup (Fin 3))=3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hK0 : Nat.card K0=3 := by
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,hthree,mul_one]
  have hL0 : Nat.card L0=3 := by
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,hthree,one_mul]
  have hd0 : Disjoint K0 L0 := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact Prod.ext hx.2.1 hx.1.2
  have hKL0 : Nat.card (K0⊔L0 : Subgroup (S×S))=9 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint K0 L0
      (by rw [normalizer_eq_top];exact le_top) hd0,hK0,hL0]
  have hK : Nat.card K=3 := (card_map_of_injective hφ).trans hK0
  have hL : Nat.card L=3 := (card_map_of_injective hφ).trans hL0
  have hKL : Nat.card (K⊔L : Subgroup (MulAut E))=9 := by
    change Nat.card (K0.map φ ⊔ L0.map φ : Subgroup (MulAut E))=9
    rw [←Subgroup.map_sup,card_map_of_injective hφ,hKL0]
  have hKn : φ.range≤normalizer (K : Set (MulAut E)) := by
    have hh := K0.le_normalizer_map φ
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map] using hh
  have hLn : φ.range≤normalizer (L : Set (MulAut E)) := by
    have hh := L0.le_normalizer_map φ
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map] using hh
  obtain ⟨U,W,hU,hW,hd,hu,hw⟩ := invariant_planes_of_normal_cubics hE φ.range K L hK hL hKL
    (map_le_range _ _) (map_le_range _ _) hKn hLn (f t)
    ⟨e t,by simp [φ]⟩ ht
  refine ⟨U,W,hU,hW,hd,?_,?_⟩
  · intro d x hx
    exact hu ⟨f d,⟨e d,by simp [φ]⟩⟩ x hx
  · intro d x hx
    exact hw ⟨f d,⟨e d,by simp [φ]⟩⟩ x hx
end SixteenOddComplements
