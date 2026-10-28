module

public import Theory.GroupTheory.DihedralRotationQuotient
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Splitting along a Sylow three-normalizer

Let Y = X R, with X a Sylow three-subgroup and R a two-group. If U
normalizes both Y and R and contains R, Frattini gives U = N_U(X) R.
Since N_R(X) = C_R(X), a trivial centralizer makes restriction of any
quotient map with kernel R an isomorphism on N_U(X). For a dihedral
quotient its inverse constructs a section with image exactly N_U(X).

All normality assumptions are relative to the local overgroups. The last
lemmas reduce the centralizer calculation to a fixed-vector bound and
lift inversion modulo R to actual inversion of X.

Source: Aschbacher--Smith, proof of 15.3.38, combined manuscript
(1 March 2004), printed p.1136. This module proves the Frattini and
splitting argument; it does not identify any matrix automorphism cosets.
-/

public section

open Subgroup

namespace SylowThreeNormalizer
variable {H Q : Type*} [Group H] [Group Q] [Finite H]

omit [Finite H] in
theorem normalizer_inf_eq_centralizer_inf
    (R P : Subgroup H) (hPR : P ≤ normalizer (R : Set H)) (hRP : Disjoint R P) :
    R ⊓ normalizer (P : Set H) = R ⊓ centralizer (P : Set H) := by
  apply le_antisymm
  · apply le_inf inf_le_left
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hRP.eq_bot]
    refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp inf_le_right)
    exact (commutator_mono inf_le_left le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hPR)
  · exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)

theorem sylow_supplement
    (Y R : Subgroup H) [(R.subgroupOf Y).Normal] (hRY : R ≤ Y)
    (hq : IsPGroup 3 (Y ⧸ R.subgroupOf Y)) (X : Sylow 3 Y) :
    (X : Subgroup Y).map Y.subtype ⊔ R = Y := by
  have h := congrArg (Subgroup.map Y.subtype)
    (X.sup_eq_top_of_quotient_isPGroup (R.subgroupOf Y) hq)
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hRY,
    ← MonoidHom.range_eq_map, range_subtype] using h

theorem normalizer_factorization
    (Y R U : Subgroup H) (X : Sylow 3 Y)
    (hgen : (X : Subgroup Y).map Y.subtype ⊔ R = Y)
    (hRU : R ≤ U) (hYR : Y ≤ normalizer (R : Set H))
    (hUR : U ≤ normalizer (R : Set H)) (hUY : U ≤ normalizer (Y : Set H))
    (u : U) :
    ∃ n ∈ U ⊓ normalizer (((X : Subgroup Y).map Y.subtype) : Set H),
      ∃ r ∈ R, n * r = u := by
  let W := Y ⊔ U
  let Y' := Y.subgroupOf W
  let R' := R.subgroupOf W
  have hRY : R ≤ Y := by rw [← hgen]; exact le_sup_right
  let : Y'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer hUY)
  let : R'.Normal := normal_subgroupOf_of_le_normalizer (sup_le hYR hUR)
  let e : Y ≃* Y' := (subgroupOfEquivOfLe (show Y ≤ W from le_sup_left)).symm
  let X' := X.mapSurjective (f := e.toMonoidHom) e.surjective
  let P' := (X' : Subgroup Y').map Y'.subtype
  have hP : P'.map W.subtype = (X : Subgroup Y).map Y.subtype := by
    change (((X : Subgroup Y).map e.toMonoidHom).map Y'.subtype).map W.subtype = _
    rw [map_map, map_map]
    rfl
  have hR : R'.map W.subtype = R :=
    map_subgroupOf_eq_of_le (hRY.trans le_sup_left)
  have hY : Y'.map W.subtype = Y := map_subgroupOf_eq_of_le le_sup_left
  have hgen' : P' ⊔ R' = Y' := by
    apply map_injective W.subtype_injective
    rw [Subgroup.map_sup, hP, hR, hY, hgen]
  have hFr : normalizer (P' : Set W) ⊔ R' = ⊤ := by
    calc
      _ = normalizer (P' : Set W) ⊔ (P' ⊔ R') := by
        rw [← sup_assoc, sup_eq_left.mpr P'.le_normalizer]
      _ = normalizer (P' : Set W) ⊔ Y' := by rw [hgen']
      _ = ⊤ := X'.normalizer_sup_eq_top
  let u' : W := ⟨u, mem_sup_right u.property⟩
  obtain ⟨n, hn, r, hr, hnr⟩ := mem_sup_of_normal_right.mp
    (show u' ∈ normalizer (P' : Set W) ⊔ R' by rw [hFr]; exact mem_top _)
  have hnH : (n : H) ∈ normalizer (((X : Subgroup Y).map Y.subtype) : Set H) := by
    rw [← hP]
    exact P'.le_normalizer_map W.subtype ⟨n, hn, rfl⟩
  have hnrH : (n : H) * (r : H) = (u : H) := congrArg Subtype.val hnr
  have hnU : (n : H) ∈ U :=
    (U.mul_mem_cancel_right (hRU hr)).mp (hnrH.symm ▸ u.property)
  exact ⟨n, ⟨hnU, hnH⟩, r, hr, hnrH⟩

theorem normalizer_restriction_bijective
    (Y R : Subgroup H) (X : Sylow 3 Y)
    (hgen : (X : Subgroup Y).map Y.subtype ⊔ R = Y)
    (hYR : Y ≤ normalizer (R : Set H)) (hR : IsPGroup 2 R)
    (hC : R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set H) = ⊥)
    (U : Subgroup H) (hRU : R ≤ U)
    (hUR : U ≤ normalizer (R : Set H)) (hUY : U ≤ normalizer (Y : Set H))
    (f : U →* Q) (hf : Function.Surjective f) (hk : f.ker = R.subgroupOf U) :
    Function.Bijective (f.domRestrict
      ((normalizer (((X : Subgroup Y).map Y.subtype) : Set H)).subgroupOf U)) := by
  let P : Subgroup H := (X : Subgroup Y).map Y.subtype
  let N := normalizer (P : Set H)
  have hd : Disjoint R P :=
    IsPGroup.disjoint_of_ne 2 3 (by decide) R P hR (X.isPGroup'.map Y.subtype)
  have hRN : R ⊓ N = ⊥ :=
    (normalizer_inf_eq_centralizer_inf R P ((map_subtype_le _).trans hYR) hd).trans hC
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    ext x
    change f (x : U) = 1 ↔ x = 1
    constructor
    · intro hx
      have hxR : ((x : U) : H) ∈ R := show (x : U) ∈ R.subgroupOf U from hk ▸ hx
      exact Subtype.ext (Subtype.ext (show ((x : U) : H) = 1 from hRN.le ⟨hxR, x.property⟩))
    · rintro rfl
      exact f.map_one
  · intro q
    obtain ⟨u, rfl⟩ := hf q
    obtain ⟨n, hn, r, hr, hnr⟩ := normalizer_factorization Y R U X hgen hRU hYR hUR hUY u
    let nU : U := ⟨n, hn.1⟩
    let rU : U := ⟨r, hRU hr⟩
    have hmul : nU * rU = u := Subtype.ext hnr
    refine ⟨⟨nU, hn.2⟩, ?_⟩
    change f nU = f u
    have hr1 : f rU = 1 := show rU ∈ f.ker from hk.symm ▸ hr
    rw [← hmul, map_mul, hr1, mul_one]

@[expose] noncomputable def normalizerEquiv
    (Y R : Subgroup H) (X : Sylow 3 Y)
    (hgen : (X : Subgroup Y).map Y.subtype ⊔ R = Y)
    (hYR : Y ≤ normalizer (R : Set H)) (hR : IsPGroup 2 R)
    (hC : R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set H) = ⊥)
    (U : Subgroup H) (hRU : R ≤ U)
    (hUR : U ≤ normalizer (R : Set H)) (hUY : U ≤ normalizer (Y : Set H))
    (f : U →* Q) (hf : Function.Surjective f) (hk : f.ker = R.subgroupOf U) :
    ((normalizer (((X : Subgroup Y).map Y.subtype) : Set H)).subgroupOf U) ≃* Q :=
  MulEquiv.ofBijective _
    (normalizer_restriction_bijective Y R X hgen hYR hR hC U hRU hUR hUY f hf hk)

@[expose] noncomputable def dihedralSection
    (Y R : Subgroup H) (X : Sylow 3 Y)
    (hgen : (X : Subgroup Y).map Y.subtype ⊔ R = Y)
    (hYR : Y ≤ normalizer (R : Set H)) (hR : IsPGroup 2 R)
    (hC : R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set H) = ⊥)
    (U : Subgroup H) (hRU : R ≤ U)
    (hUR : U ≤ normalizer (R : Set H)) (hUY : U ≤ normalizer (Y : Set H))
    (f : U →* DihedralGroup 4) (hf : Function.Surjective f)
    (hk : f.ker = R.subgroupOf U) : DihedralGroup.SplitSection (R.subgroupOf U) :=
  let N := (normalizer (((X : Subgroup Y).map Y.subtype) : Set H)).subgroupOf U
  let e := normalizerEquiv Y R X hgen hYR hR hC U hRU hUR hUY f hf hk
  { projection := f
    sectionMap := N.subtype.comp e.symm.toMonoidHom
    rightInverse := e.apply_symm_apply
    kernel := hk }

theorem dihedralSection_range
    (Y R : Subgroup H) (X : Sylow 3 Y)
    (hgen : (X : Subgroup Y).map Y.subtype ⊔ R = Y)
    (hYR : Y ≤ normalizer (R : Set H)) (hR : IsPGroup 2 R)
    (hC : R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set H) = ⊥)
    (U : Subgroup H) (hRU : R ≤ U)
    (hUR : U ≤ normalizer (R : Set H)) (hUY : U ≤ normalizer (Y : Set H))
    (f : U →* DihedralGroup 4) (hf : Function.Surjective f)
    (hk : f.ker = R.subgroupOf U) :
    (dihedralSection Y R X hgen hYR hR hC U hRU hUR hUY f hf hk).sectionMap.range.map U.subtype =
      U ⊓ normalizer (((X : Subgroup Y).map Y.subtype) : Set H) := by
  let e := normalizerEquiv Y R X hgen hYR hR hC U hRU hUR hUY f hf hk
  ext x
  constructor
  · rintro ⟨t, ⟨a, rfl⟩, rfl⟩
    exact ⟨(e.symm a).val.property, (e.symm a).property⟩
  · rintro ⟨ht, hn⟩
    let n : (normalizer (((X : Subgroup Y).map Y.subtype) : Set H)).subgroupOf U :=
      ⟨⟨x, ht⟩, hn⟩
    refine ⟨⟨x, ht⟩, ⟨e n, ?_⟩, rfl⟩
    exact congrArg Subtype.val (e.symm_apply_apply n)

omit [Finite H] in
theorem sylow_centralizer_eq_bot_of_bound
    (Y R V : Subgroup H) (X : Sylow 3 Y)
    (hgen : (X : Subgroup Y).map Y.subtype ⊔ R = Y)
    (hRV : R ≤ centralizer (V : Set H))
    (hVY : V ⊓ centralizer (Y : Set H) = ⊥)
    (hbound : R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set H) ≤ V) :
    R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set H) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  apply hVY.le
  refine ⟨hbound hx, ?_⟩
  have hP : (X : Subgroup Y).map Y.subtype ≤ centralizer ({x} : Set H) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hx.2 a ha)
  have hR : R ≤ centralizer ({x} : Set H) := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (hRV hr x (hbound hx)).symm
  intro y hy
  have hyC := (sup_le hP hR) (hgen.symm ▸ hy)
  exact mem_centralizer_singleton_iff.mp hyC

omit [Finite H] in
theorem normalizer_inverts_of_modulo
    (R P : Subgroup H) (hd : Disjoint R P) (t : H)
    (ht : t ∈ normalizer (P : Set H))
    (hinv : ∀ x ∈ P, t * x * t⁻¹ * x ∈ R) :
    ∀ x ∈ P, (MulAut.conj t) x = x⁻¹ := by
  intro x hx
  have hm : t * x * t⁻¹ * x ∈ P :=
    P.mul_mem ((mem_normalizer_iff.mp ht x).mp hx) hx
  have he := disjoint_def.mp hd (hinv x hx) hm
  exact eq_inv_of_mul_eq_one_left he

end SylowThreeNormalizer
