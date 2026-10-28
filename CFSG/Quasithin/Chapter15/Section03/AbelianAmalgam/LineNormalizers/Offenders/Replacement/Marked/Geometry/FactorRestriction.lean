module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.OriginalData
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.PairingData
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Restricting the original marked factors to the temporary group

The original marked product and `OriginalData.inherited` give
`H = ⟨Y_E,τ⟩ C_H(E)`. Restrict the original quotient coordinates to H.
Their kernel is the restriction of the original two-core, hence a normal
two-subgroup of H contained in its intrinsic two-core. In the other direction,
the intrinsic two-core of H is killed by the first coordinate, which is a
surjection onto S₃. These are containments between distinct cores, not an
identification of the original and temporary cores.

In the temporary core quotient the marked subgroup consequently maps
isomorphically onto S₃, commutes with the actual centralizer image, and together
with that image generates the quotient. Multiplication of these two factors
constructs the equivalence. Its inverse preserves centralizer elements
pointwise and retains the original first coordinate on every element of H.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171, following 15.3.66 on p.1152.
-/

@[expose] public section
open Subgroup
private theorem exists_product_equiv {K S : Type*} [Group K] [Group S]
    (B C : Subgroup K) (f : K →* S)
    (hf : Function.Bijective (f.comp B.subtype))
    (hC : ∀ c : C, f c = 1)
    (hcomm : ∀ b : B, ∀ c : C, Commute (b : K) (c : K))
    (hprod : ∀ x : K, ∃ b : B, ∃ c : C, (b : K) * c = x) :
    ∃ e : K ≃* S × C,
      (∀ x, (e x).1 = f x) ∧
      (∀ b : B, e b = (f b, 1)) ∧
      (∀ c : C, e c = (1, c)) := by
  let m : B × C →* K := B.subtype.noncommCoprod C.subtype hcomm
  have hm : Function.Bijective m := by
    constructor
    · intro x y hxy
      have hfirst : x.1 = y.1 := hf.1 (by
        change f (x.1 : K) = f (y.1 : K)
        have hh := congrArg f hxy
        change f ((x.1 : K) * x.2) = f ((y.1 : K) * y.2) at hh
        simpa only [map_mul, hC, mul_one] using hh)
      apply Prod.ext hfirst
      apply Subtype.ext
      change (x.1 : K) * x.2 = (y.1 : K) * y.2 at hxy
      rw [hfirst] at hxy
      exact mul_left_cancel hxy
    · intro x
      obtain ⟨b, c, h⟩ := hprod x
      exact ⟨(b, c), h⟩
  let em : B × C ≃* K := MulEquiv.ofBijective m hm
  let eb : B ≃* S := MulEquiv.ofBijective (f.comp B.subtype) hf
  let e := em.symm.trans (eb.prodCongr (MulEquiv.refl C))
  have hfst (x : K) : (e x).1 = f x := by
    change f ((em.symm x).1 : K) = f x
    have hh := congrArg f (em.apply_symm_apply x)
    change f (((em.symm x).1 : K) * (em.symm x).2) = f x at hh
    simpa only [map_mul, hC, mul_one] using hh
  refine ⟨e, hfst, ?_, ?_⟩
  · intro b
    have hb : em.symm (b : K) = (b, 1) := em.symm_apply_eq.mpr (by
      change (b : K) = (b : K) * 1
      simp)
    change (eb (em.symm b).1, (em.symm b).2) = _
    rw [hb]
    rfl
  · intro c
    have hc : em.symm (c : K) = (1, c) := em.symm_apply_eq.mpr (by
      change (c : K) = 1 * (c : K)
      simp)
    change (eb (em.symm c).1, (em.symm c).2) = _
    rw [hc]
    simp

open scoped commutatorElement
private theorem exists_quotient_factors {K S D : Type*} [Group K] [Group S] [Group D]
    (A C Q : Subgroup K) [Q.Normal] (f : K →* S × D)
    (hA : A.map f = (⊤ : Subgroup S).prod ⊥)
    (hC : ∀ c ∈ C, (f c).1 = 1)
    (hprod : ∀ x : K, ∃ a ∈ A, ∃ c ∈ C, a * c = x)
    (hK : f.ker ≤ Q)
    (hQ : Q ≤ ((MonoidHom.fst S D).comp f).ker) :
    ∃ e : (K ⧸ Q) ≃* S × (C.map (QuotientGroup.mk' Q)),
      A.map (e.toMonoidHom.comp (QuotientGroup.mk' Q)) = (⊤ : Subgroup S).prod ⊥ ∧
      (∀ c : C, e (QuotientGroup.mk' Q c) =
        (1, ⟨QuotientGroup.mk' Q c, mem_map_of_mem _ c.property⟩)) ∧
      (∀ x, (e (QuotientGroup.mk' Q x)).1 = (f x).1) := by
  let q := QuotientGroup.mk' Q
  let B := A.map q
  let F := C.map q
  let φ := QuotientGroup.lift Q ((MonoidHom.fst S D).comp f) hQ
  have hφ (x : K) : φ (q x) = (f x).1 := rfl
  have hAsnd (a : K) (ha : a ∈ A) : (f a).2 = 1 := by
    have hh := mem_map_of_mem f ha
    rw [hA] at hh
    exact hh.2
  have hbij : Function.Bijective (φ.comp B.subtype) := by
    constructor
    · apply (injective_iff_map_eq_one _).mpr
      rintro ⟨b, hb⟩ hh
      obtain ⟨a, ha, rfl⟩ := hb
      have ha1 : (f a).1 = 1 := hh
      have haQ : a ∈ Q := hK (show f a = 1 from Prod.ext ha1 (hAsnd a ha))
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff a).mpr haQ
    · intro s
      have hs : (s, (1 : D)) ∈ A.map f := by rw [hA]; exact ⟨mem_top _, rfl⟩
      obtain ⟨a, ha, he⟩ := hs
      exact ⟨⟨q a, mem_map_of_mem q ha⟩, congrArg Prod.fst he⟩
  have hF (c : F) : φ c = 1 := by
    obtain ⟨c, hc, he⟩ := c.property
    rw [← he, hφ]
    exact hC c hc
  have hcomm (b : B) (c : F) : Commute (b : K ⧸ Q) (c : K ⧸ Q) := by
    obtain ⟨a, ha, he⟩ := b.property
    obtain ⟨c, hc, he'⟩ := c.property
    rw [← he, ← he']
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply hK
    change f ⁅a, c⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    apply Prod.ext
    · change (f a).1 * (f c).1 = (f c).1 * (f a).1
      rw [hC c hc, mul_one, one_mul]
    · change (f a).2 * (f c).2 = (f c).2 * (f a).2
      rw [hAsnd a ha, one_mul, mul_one]
  have hprod' (x : K ⧸ Q) : ∃ b : B, ∃ c : F, (b : K ⧸ Q) * c = x := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q x
    obtain ⟨a, ha, c, hc, rfl⟩ := hprod x
    exact ⟨⟨q a, mem_map_of_mem q ha⟩, ⟨q c, mem_map_of_mem q hc⟩, (map_mul q a c).symm⟩
  obtain ⟨e, hef, heB, heF⟩ := exists_product_equiv B F φ hbij hF hcomm hprod'
  refine ⟨e, ?_, ?_, fun x => (hef _).trans (hφ x)⟩
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have hh := heB ⟨q a, mem_map_of_mem q ha⟩
      change e (q a) ∈ _
      rw [hh]
      exact ⟨mem_top _, rfl⟩
    · rintro ⟨s, c⟩ ⟨_, hc⟩
      have hc' : c = 1 := hc
      subst c
      obtain ⟨b, hb⟩ := hbij.2 s
      obtain ⟨a, ha, he⟩ := b.property
      refine ⟨a, ha, ?_⟩
      change e (q a) = (s, 1)
      rw [he, heB]
      exact Prod.ext hb rfl
  · intro c
    exact heF ⟨q c, mem_map_of_mem q c.property⟩

open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry
open Descent.QuotientIdentification
namespace OriginalData
variable {G : Type*} [Group G] [Finite G] {Y T V M E Pc : Subgroup G}
variable [IsMulCommutative V]
attribute [local instance] temporaryCore_normal

/-- Restriction retains the original first coordinate and the actual centralizer image. -/
theorem exists_markedQuotientFactors (d : OriginalData Y T V M E Pc) :
    ∃ factors : MarkedQuotientFactors
      ((lineY Y E ⊔ zpowers d.marked.tau).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)),
      ∀ h : temporaryLineNormalizer T V E,
        (factors.equiv (QuotientGroup.mk' _ h)).1 =
          (d.marked.equiv (quotientMap E (inclusion inf_le_left h))).1 := by
  let H := temporaryLineNormalizer T V E
  let A := (lineY Y E ⊔ zpowers d.marked.tau).subgroupOf H
  let C := (temporaryCentralizer T V E).subgroupOf H
  let Q := (temporaryCore T V E).subgroupOf H
  let i : H →* lineNormalizer E := inclusion inf_le_left
  let f : H →* Equiv.Perm (Fin 3) × centralizerImage E :=
    d.marked.equiv.toMonoidHom.comp ((quotientMap E).comp i)
  have hAH : lineY Y E ⊔ zpowers d.marked.tau ≤ H :=
    sup_le d.inherited.2.1 (zpowers_le.mpr d.inherited.1)
  have hA : A.map f = (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rw [← d.marked.first_factor]
      exact mem_map_of_mem _ (show i a ∈
        (lineY Y E ⊔ zpowers d.marked.tau).subgroupOf (lineNormalizer E) from ha)
    · intro z hz
      rw [← d.marked.first_factor] at hz
      obtain ⟨a, ha, he⟩ := hz
      exact ⟨⟨a, hAH ha⟩, ha, he⟩
  have hC (c : H) (hc : c ∈ C) : (f c).1 = 1 := by
    have hh := congrArg Prod.fst (d.marked.centralizer_factor ⟨c, hc.2⟩)
    exact hh
  have hprod (x : H) : ∃ a ∈ A, ∃ c ∈ C, a * c = x := by
    have hx : (x : G) ∈ ((lineY Y E ⊔ zpowers d.marked.tau : Subgroup G) : Set G) *
        (temporaryCentralizer T V E : Set G) := by
      rw [← d.inherited.2.2.1]
      exact x.property
    obtain ⟨a, ha, c, hc, he⟩ := hx
    exact ⟨⟨a, hAH ha⟩, ha, ⟨c, hc.1⟩, hc, Subtype.ext he⟩
  have hQcore : Q = pCore 2 H := by
    change ((pCore 2 H).map H.subtype).comap H.subtype = pCore 2 H
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hker : f.ker = (pCore 2 (lineNormalizer E)).comap i := by
    ext x
    change d.marked.equiv (quotientMap E (i x)) = 1 ↔ i x ∈ pCore 2 (lineNormalizer E)
    rw [d.marked.equiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hK : f.ker ≤ Q := by
    rw [hQcore]
    exact le_sSup ⟨inferInstance, hker ▸
      (pCore_isPGroup.comap_of_injective i (inclusion_injective inf_le_left))⟩
  let φ : H →* Equiv.Perm (Fin 3) := (MonoidHom.fst _ _).comp f
  have hφ : Function.Surjective φ := by
    intro s
    have hs : (s, (1 : centralizerImage E)) ∈ A.map f := by
      rw [hA]
      exact ⟨mem_top _, rfl⟩
    obtain ⟨a, _, he⟩ := hs
    exact ⟨a, congrArg Prod.fst he⟩
  have hS : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa using hh.symm
  have hQ : Q ≤ φ.ker := by
    rw [hQcore]
    have hn : ((pCore 2 H).map φ).Normal := Normal.map inferInstance φ hφ
    have hp : (pCore 2 H).map φ ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
      le_sSup ⟨hn, pCore_isPGroup.map φ⟩
    rw [hS] at hp
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hp)
  obtain ⟨e, heA, heC, hef⟩ := exists_quotient_factors A C Q f hA hC hprod hK hQ
  exact ⟨⟨e, heA, heC⟩, hef⟩

/-- The inherited marked factors in the temporary core quotient. -/
noncomputable def markedQuotientFactors (d : OriginalData Y T V M E Pc) :
    MarkedQuotientFactors
      ((lineY Y E ⊔ zpowers d.marked.tau).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)) :=
  d.exists_markedQuotientFactors.choose

/-- The constructor preserves the original first coordinate at every element of H. -/
theorem markedQuotientFactors_fst (d : OriginalData Y T V M E Pc)
    (h : temporaryLineNormalizer T V E) :
    (d.markedQuotientFactors.equiv (QuotientGroup.mk' _ h)).1 =
      (d.marked.equiv (quotientMap E (inclusion inf_le_left h))).1 :=
  d.exists_markedQuotientFactors.choose_spec h

end OriginalData
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry
