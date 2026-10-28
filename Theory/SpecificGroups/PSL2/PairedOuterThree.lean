module
public import Theory.SpecificGroups.PSL2.PairedOuterThree.Cubic

/-!
# Three-prime outer quotients of a pair of binary PSL2 factors

Let A lie in Aut(S)×Aut(S), containing the full inner product, where
S is the actual projective matrix group over a finite field of
characteristic two. The split field projection sends A to field pairs,
and full inner containment puts their pure field sections back in A.
A cubic field pair centralizes the independent prime-field inner cubics
in both coordinates, producing an elementary subgroup of order 27.
Thus three-rank at most two forces the outer image to have three-prime
order. The two first-isomorphism consumers retain the literal inner
product and its preimage under an arbitrary original action.

The argument includes F2 and requires neither simplicity nor a field
degree bound. Source: Aschbacher--Smith 1.2.2(a), printed p.504,
combined manuscript of 1 March 2004. The ambient component and action
construction remain with the original source assembly.
-/

@[expose] public section
open Subgroup
namespace Theory.PSL2.PairedOuterThree
variable (F : Type*) [Field F] [CharP F 2] [Finite F]

noncomputable def projection :
    MulAut (Group F) × MulAut (Group F) →* (F ≃+* F) × (F ≃+* F) :=
  (fieldProjection F).prodMap (fieldProjection F)

noncomputable def sectionMap :
    (F ≃+* F) × (F ≃+* F) →* MulAut (Group F) × MulAut (Group F) :=
  fieldAutHom.prodMap fieldAutHom

theorem projection_section (σ : (F ≃+* F) × (F ≃+* F)) :
    projection F (sectionMap F σ) = σ :=
  Prod.ext (fieldProjection_fieldAut F σ.1) (fieldProjection_fieldAut F σ.2)

theorem section_injective : Function.Injective (sectionMap F) := by
  intro σ τ he
  have hh := congrArg (projection F) he
  simpa only [projection_section] using hh

theorem projection_ker : (projection F).ker = (inner F).prod (inner F) := by
  ext a
  change (fieldProjection F a.1,fieldProjection F a.2) = (1,1) ↔ _
  rw [Prod.mk.injEq]
  change a.1 ∈ (fieldProjection F).ker ∧ a.2 ∈ (fieldProjection F).ker ↔ _
  rw [fieldProjection_ker]
  rfl

theorem section_mem_of_full_inner
    (A : Subgroup (MulAut (Group F) × MulAut (Group F)))
    (hI : (inner F).prod (inner F) ≤ A)
    (σ : (F ≃+* F) × (F ≃+* F)) (hσ : σ ∈ A.map (projection F)) :
    sectionMap F σ ∈ A := by
  have hk : (projection F).ker ≤ A := (projection_ker F).trans_le hI
  have hm : sectionMap F σ ∈ (A.map (projection F)).comap (projection F) :=
    by
    change projection F (sectionMap F σ) ∈ A.map (projection F)
    rwa [projection_section]
  rwa [comap_map_eq_self hk] at hm

/-- A cubic field-pair would centralize the actual elementary-nine subgroup
of inner cubics, contradicting the given three-rank. -/
theorem image_coprime_three
    (A : Subgroup (MulAut (Group F) × MulAut (Group F)))
    (hI : (inner F).prod (inner F) ≤ A) (hr : primeRank 3 A ≤ 2) :
    Nat.Coprime 3 (Nat.card (A.map (projection F))) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  obtain ⟨σ,hσ⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let x : A := ⟨sectionMap F σ,section_mem_of_full_inner F A hI σ σ.property⟩
  have hx : orderOf x = 3 := by
    rw [←orderOf_injective A.subtype A.subtype_injective x]
    change orderOf (sectionMap F σ.val) = 3
    rw [orderOf_injective _ (section_injective F)]
    exact (orderOf_injective (A.map (projection F)).subtype Subtype.val_injective σ).trans hσ
  have hEA : cubicPlane F ≤ A := (cubicPlane_le_inner F).trans hI
  let E := (cubicPlane F).subgroupOf A
  let : IsElementaryAbelian 3 (cubicPlane F) := cubicPlane_elementary F
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.subgroupOf hEA
  have hc : Nat.card E = 3^2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv).trans (cubicPlane_card F)
  have hxE : x ∉ E := by
    intro he
    have hi : sectionMap F σ.val ∈ (projection F).ker :=
      (projection_ker F).symm ▸ cubicPlane_le_inner F he
    have hs : σ.val = 1 := (projection_section F σ).symm.trans hi
    have hs' : σ = 1 := Subtype.ext hs
    rw [hs',orderOf_one] at hσ
    norm_num at hσ
  have hfix : E ≤ centralizer ({x} : Set A) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact fieldPair_centralizes_plane F σ a.val ha
  have hl := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hx hxE hfix hc
  omega

/-- The literal quotient by the full inner product has three-prime order. -/
theorem quotient_coprime_three
    (A : Subgroup (MulAut (Group F) × MulAut (Group F)))
    (hI : (inner F).prod (inner F) ≤ A) (hr : primeRank 3 A ≤ 2) :
    Nat.Coprime 3 (Nat.card (A ⧸ ((inner F).prod (inner F)).subgroupOf A)) := by
  let f := (projection F).comp A.subtype
  have hk : f.ker = ((inner F).prod (inner F)).subgroupOf A := by
    change ((projection F).comp A.subtype).ker = _
    rw [←MonoidHom.comap_ker,projection_ker]
    rfl
  have him : f.range = A.map (projection F) := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem (projection F) x.property
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  rw [Nat.card_congr e.toEquiv,him]
  exact image_coprime_three F A hI hr

/-- The same obstruction on an original action, retaining the literal
preimage of the inner product. This is the outer-action step in 1.2.2(a). -/
theorem quotient_by_inner_preimage_coprime_three
    {D : Type*} [_root_.Group D] [Finite D]
    (a : D →* MulAut (Group F) × MulAut (Group F))
    (hI : (inner F).prod (inner F) ≤ a.range) (hr : primeRank 3 a.range ≤ 2) :
    Nat.Coprime 3 (Nat.card (D ⧸ ((inner F).prod (inner F)).comap a)) := by
  let f := (projection F).comp a
  have hk : f.ker = ((inner F).prod (inner F)).comap a := by
    change ((projection F).comp a).ker = _
    rw [←MonoidHom.comap_ker,projection_ker]
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  rw [Nat.card_congr e.toEquiv,MonoidHom.range_comp]
  exact image_coprime_three F a.range hI hr
end Theory.PSL2.PairedOuterThree
