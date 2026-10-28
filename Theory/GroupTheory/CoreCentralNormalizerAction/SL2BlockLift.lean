module

public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.SpecificGroups.SL2.CentralPreimageBlock
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# An SL₂ block lifted to the original group

First take the derived subgroup of its full inverse image in K/O₂(K).
The central SL₂ lifting theorem removes the entire central kernel there.
Then take the full inverse image in K, retaining all of the original O₂(K).
Its intrinsic two-core quotient is the marked PSL₂, and its original
core-central image is exactly the specified block.

Source: Aschbacher--Smith 6.1.4, replacement of K₁ by K₂, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The canonical derived central preimage, then full two-core preimage,
produces an actual subgroup of the original K with a PSL₂ core quotient. -/
theorem coreCentral_sl2_block_lift
    {F : Type*} [Field F] [Finite F] [Fact (3 < Nat.card F)]
    (K : Subgroup G) (B : Subgroup (coreCentralQuotient K))
    (e : B ≃* SL(2,F)) (ho : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9) :
    let q := QuotientGroup.mk' (pCore 2 K)
    let z := QuotientGroup.mk' (center (K ⧸ pCore 2 K))
    let R := (commutator (B.comap z)).map (B.comap z).subtype
    let J := (R.comap q).map K.subtype
    J ≤ K ∧ K.pCoreIn 2 ≤ J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* PSL(2,F)) ∧
      coreCentralIntersectionImage K J = B := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let z := QuotientGroup.mk' (center (K ⧸ pCore 2 K))
  let R := (commutator (B.comap z)).map (B.comap z).subtype
  let A := R.comap q
  let J := A.map K.subtype
  obtain ⟨hRp,⟨eR⟩,hR,_⟩ := Theory.SpecificGroups.SL2.central_preimage_block
    z (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) B e ho h9
  let f : A →* R := q.subgroupComap R
  have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective R
    (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 K).comap A.subtype := by
      ext x
      change f x = 1 ↔ (x : K) ∈ pCore 2 K
      rw [←QuotientGroup.eq_one_iff]
      exact Subtype.ext_iff
    rw [he]
    exact pCore_isPGroup.comap_of_injective A.subtype A.subtype_injective
  let r := eR.toMonoidHom.comp f
  have hr : Function.Surjective r := eR.surjective.comp hf
  have hrk : IsPGroup 2 r.ker := by
    have he : r.ker = f.ker := by
      ext x
      change eR (f x) = 1 ↔ f x = 1
      exact eR.map_eq_one_iff
    exact he.symm ▸ hk
  let : IsQuasisimple SL(2,F) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv Fact.out (MulEquiv.refl _)
  have hZ : IsPGroup 2 (center SL(2,F)) :=
    (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup F ho).of_equiv
      (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker F))
  have hcore : pCore 2 SL(2,F) = center SL(2,F) :=
    le_antisymm (IsQuasisimple.pCore_le_center 2) (le_sSup ⟨inferInstance,hZ⟩)
  let eA : (A ⧸ pCore 2 A) ≃* PSL(2,F) :=
    (r.quotientPCoreEquivOfSurjective hr hrk).trans
      (QuotientGroup.quotientMulEquivOfEq hcore)
  let eJ : A ≃* J := A.equivMapOfInjective K.subtype K.subtype_injective
  have hJA : J.subgroupOf K = A := comap_map_eq_self_of_injective K.subtype_injective A
  refine ⟨map_subtype_le A,map_mono ?_,⟨(QuotientGroup.congr _ _ eJ
    (pCore_map_iso 2 eJ)).symm.trans eA⟩,?_⟩
  · intro k hk
    change q k ∈ R
    rw [show q k = 1 from (QuotientGroup.eq_one_iff k).mpr hk]
    exact R.one_mem
  · change (J.subgroupOf K).map (z.comp q) = B
    rw [hJA,←map_map,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    exact hR

private theorem preimage_map_eq {E C : Type*} [Group E] [Finite E] [Group C]
    (f : E →* C) (B : Subgroup C) (a : MulAut E) (b : MulAut C)
    (hc : f.comp a.toMonoidHom = b.toMonoidHom.comp f)
    (hB : B.map b.toMonoidHom = B) : (B.comap f).map a.toMonoidHom = B.comap f := by
  apply eq_of_le_of_card_ge
  · rintro x ⟨y,hy,rfl⟩
    change f (a y) ∈ B
    have he : f (a y) = b (f y) := DFunLike.congr_fun hc y
    rw [he]
    exact hB ▸ mem_map_of_mem b.toMonoidHom hy
  · exact (Nat.card_congr (a.subgroupMap (B.comap f)).toEquiv).le

private theorem derived_preimage_map_eq {E C : Type*} [Group E] [Finite E] [Group C]
    (f : E →* C) (B : Subgroup C) (a : MulAut E) (b : MulAut C)
    (hc : f.comp a.toMonoidHom = b.toMonoidHom.comp f)
    (hB : B.map b.toMonoidHom = B) :
    ((commutator (B.comap f)).map (B.comap f).subtype).map a.toMonoidHom =
      (commutator (B.comap f)).map (B.comap f).subtype := by
  let A := B.comap f
  have hA := preimage_map_eq f B a b hc hB
  let eA : A ≃* A := (a.subgroupMap A).trans (MulEquiv.subgroupCongr hA)
  have he : a.toMonoidHom.comp A.subtype = A.subtype.comp eA.toMonoidHom := rfl
  rw [map_map,he,←map_map,map_commutator_eq,
    MonoidHom.range_eq_top.mpr eA.surjective]
  rfl

/-- Every original actor preserving the marked block preserves its canonical
lift. This uses the literal quotient actions and the full original two-core. -/
theorem coreCentral_derived_block_lift_normalized
    (K A : Subgroup G) (B : Subgroup (coreCentralQuotient K))
    (hB : coreCentralActorImage K A ≤
      MulAction.stabilizer (MulAut (coreCentralQuotient K)) B) :
    let q := QuotientGroup.mk' (pCore 2 K)
    let z := QuotientGroup.mk' (center (K ⧸ pCore 2 K))
    let R := (commutator (B.comap z)).map (B.comap z).subtype
    let J := (R.comap q).map K.subtype
    A ⊓ normalizer (K : Set G) ≤ normalizer (J : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let z := QuotientGroup.mk' (center (K ⧸ pCore 2 K))
  let R := (commutator (B.comap z)).map (B.comap z).subtype
  let P := R.comap q
  change A ⊓ normalizer (K : Set G) ≤ normalizer (P.map K.subtype : Set G)
  rintro x ⟨hx,hxK⟩
  let u : normalizer (K : Set G) := ⟨x,hxK⟩
  let a := K.normalizerMonoidHom u
  let b := quotientAut (pCore 2 K) a
  let c := quotientAut (center (K ⧸ pCore 2 K)) b
  have hBc : B.map c.toMonoidHom = B :=
    hB (mem_map_of_mem (normalizerCoreCentralAction K)
      (show u ∈ A.subgroupOf (normalizer (K : Set G)) from hx))
  have hzc : z.comp b.toMonoidHom = c.toMonoidHom.comp z := by
    ext y
    exact (quotientAut_apply_mk _ _ _).symm
  have hR : R.map b.toMonoidHom = R := derived_preimage_map_eq z B b c hzc hBc
  have hqb : q.comp a.toMonoidHom = b.toMonoidHom.comp q := by
    ext y
    exact (quotientAut_apply_mk _ _ _).symm
  have hP : P.map a.toMonoidHom = P := preimage_map_eq q R a b hqb hR
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : (MulAut.conj x).toMonoidHom.comp K.subtype =
      K.subtype.comp a.toMonoidHom := rfl
  change (P.map K.subtype).map (MulAut.conj x).toMonoidHom = P.map K.subtype
  rw [map_map,he,←map_map,hP]

end Theory.GroupTheory
