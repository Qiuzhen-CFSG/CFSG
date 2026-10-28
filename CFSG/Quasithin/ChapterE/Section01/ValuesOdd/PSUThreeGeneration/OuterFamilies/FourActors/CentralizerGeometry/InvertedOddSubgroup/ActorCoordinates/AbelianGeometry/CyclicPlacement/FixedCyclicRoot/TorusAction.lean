module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.FixedCyclicRoot.Setup

/-!
# From fixed torus conjugacy to literal root action

The diagonal torus with fixed-field parameter c scales the root parameter
by c⁻¹; entrywise conjugation fixes it. Scalar actors form a subgroup, so
these formulas control the whole join of the cyclic inner image with the
entrywise actor. A conjugator fixed by that actor commutes with its action.

Root injectivity also proves injectivity of the restricted projective
torus. The order-two element of any cyclic subgroup placed in it therefore
has parameter -1, giving the required marking in the same coordinates.
These results do not construct a torus conjugator.
Source: Aschbacher--Smith E.1.14(7), printed p.214; Aschbacher (1982),
Lemma 4.11. The explicit matrix formulas are those of Huppert II.10.12.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement.FixedCyclicRoot
variable {F : Type} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (h2 : (2 : F) ≠ 0)

/-- A fixed-field torus parameter acts on the literal root line by its inverse. -/
theorem fixedTorus_action (c : (FixedBy.subfield F J.conj)ˣ)
    (t : FixedBy.subfield F J.conj) :
    MulAut.conj (fixedTorus J hJ c) (fixedRoot J hJ h2 (Multiplicative.ofAdd t)) =
      fixedRoot J hJ h2 (Multiplicative.ofAdd ((c⁻¹ : (FixedBy.subfield F J.conj)ˣ) * t)) := by
  let k : Fˣ := Units.map (FixedBy.subfield F J.conj).subtype.toMonoidHom c
  have hk : J.conj (k : F) = k := (c : FixedBy.subfield F J.conj).property
  have he : hermitianTorusAction J k (fixedRootCoord J h2 (Multiplicative.ofAdd t)) =
      fixedRootCoord J h2 (Multiplicative.ofAdd ((c⁻¹ : (FixedBy.subfield F J.conj)ˣ) * t)) := by
    apply Subtype.ext
    apply Prod.ext
    · simp only [hermitianTorusAction_fst, fixedRootCoord, MonoidHom.coe_mk,
        OneHom.coe_mk, Units.val_inv_eq_inv_val]
      change (t : F) * (k : F) * (J.conj (k : F))⁻¹ ^ 2 = (k : F)⁻¹ * (t : F)
      rw [hk]
      field_simp
    · simp only [hermitianTorusAction_snd, fixedRootCoord, MonoidHom.coe_mk,
        OneHom.coe_mk, Units.val_inv_eq_inv_val]
      change (-(t : F) ^ 2 / 2) * (J.conj (k : F))⁻¹ * (k : F)⁻¹ =
        -((k : F)⁻¹ * (t : F)) ^ 2 / 2
      rw [hk]
      ring
  change hermitianTorusPSU J hJ k *
    hermitianUnipotentPSU J hJ (fixedRootCoord J h2 (Multiplicative.ofAdd t)) *
      (hermitianTorusPSU J hJ k)⁻¹ = _
  rw [hermitianTorusPSU_mul_unipotent, he, mul_inv_cancel_right]
  rfl

include h2 in
/-- The restricted torus survives projectivization injectively. -/
theorem fixedTorus_injective : Function.Injective (fixedTorus J hJ) := by
  intro c d h
  have he := congrArg (fun x => MulAut.conj x (fixedRoot J hJ h2 (Multiplicative.ofAdd 1))) h
  rw [fixedTorus_action, fixedTorus_action] at he
  have hf := fixedRoot_injective J hJ h2 he
  have hv : (↑c⁻¹ : FixedBy.subfield F J.conj) = ↑d⁻¹ := by
    simpa using congrArg Multiplicative.toAdd hf
  exact inv_injective (Units.ext hv)

/-- Entrywise conjugation fixes every point of the original fixed root line. -/
theorem entrywise_fixedRoot (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγ : J.IsEntrywiseConjugation γ) (t : FixedBy.subfield F J.conj) :
    γ (fixedRoot J hJ h2 (Multiplicative.ofAdd t)) =
      fixedRoot J hJ h2 (Multiplicative.ofAdd t) := by
  let z := hermitianUnipotentSU J hJ (fixedRootCoord J h2 (Multiplicative.ofAdd t))
  have hroot : fixedRoot J hJ h2 (Multiplicative.ofAdd t) = J.specialToProjective z := by
    apply Subtype.ext
    rw [J.specialToProjective_apply_val]
    rfl
  rw [hroot]
  obtain ⟨y, hy, he⟩ := hγ z
  have ht : J.conj (t : F) = t := t.property
  have hz : y = z := by
    apply Subtype.ext
    apply Units.ext
    rw [hy]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [z, hermitianUnipotentSU, hermitianUnipotentGL, hermitianUnipotentMatrix,
        fixedRootCoord, ht, map_ofNat]
  rw [he, hz]

private def scalarActors : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) where
  carrier := {a | ∃ c : (FixedBy.subfield F J.conj)ˣ,
    ∀ t : FixedBy.subfield F J.conj,
      a (fixedRoot J hJ h2 (Multiplicative.ofAdd t)) =
        fixedRoot J hJ h2 (Multiplicative.ofAdd ((c : FixedBy.subfield F J.conj) * t))}
  one_mem' := ⟨1, by intro t; simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    intro t
    change a (b _) = _
    rw [hd, hc]
    simp only [Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro a ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    intro t
    apply a.injective
    change a (a.symm _) = a _
    rw [a.apply_symm_apply, hc]
    simp

private theorem congr_inner {K : Type*} [Group K] (e : K ≃* K) (x : K) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext z
  change e (x * e.symm z * x⁻¹) = e x * z * (e x)⁻¹
  simp

private theorem congr_entrywise {K : Type*} [Group K] (γ : MulAut K) (y : K) (hy : γ y = y) :
    MulAut.congr (MulAut.conj y) γ = γ := by
  ext z
  change y * γ (y⁻¹ * z * y) * y⁻¹ = γ z
  simp [hy, mul_assoc]

include h2 in
/-- Torus placement of the generator also marks every involution in its cyclic group. -/
theorem marked_of_torus (e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (x w : ProjectiveSpecialUnitaryMatrixGroup J)
    (c : (FixedBy.subfield F J.conj)ˣ) (hx : e x = fixedTorus J hJ c)
    (hw : orderOf w = 2) (hwx : w ∈ zpowers x) :
    e w = hermitianTorusPSU J hJ (-1) := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hwx
  have hew : e (x ^ n) = fixedTorus J hJ (c ^ n) := by
    rw [map_zpow, hx, map_zpow]
  have hw2 : (x ^ n) ^ 2 = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one _
  have hd2 : (c ^ n) ^ 2 = 1 := by
    apply fixedTorus_injective J hJ h2
    rw [map_pow, ← hew, ← map_pow, hw2, map_one, map_one]
  have hd : c ^ n = -1 := by
    have hval : ((c ^ n : (FixedBy.subfield F J.conj)ˣ) : FixedBy.subfield F J.conj) ^ 2 = 1 :=
      congrArg Units.val hd2
    rcases sq_eq_one_iff.mp hval with h | h
    · have hc1 : c ^ n = 1 := Units.ext h
      have he1 : e (x ^ n) = 1 := by rw [hew, hc1, map_one]
      have hx1 : x ^ n = 1 := e.injective (he1.trans e.map_one.symm)
      rw [hx1, orderOf_one] at hw
      contradiction
    · exact Units.ext h
  rw [hew, hd]
  change hermitianTorusPSU J hJ _ = hermitianTorusPSU J hJ _
  congr 1

include h2 in
/-- A fixed torus conjugator gives root coordinates for the entire generated actor. -/
theorem rootActionCoordinates_of_fixed_conjugator
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hγ : J.IsEntrywiseConjugation γ)
    (x w y : ProjectiveSpecialUnitaryMatrixGroup J) (hy : γ y = y)
    (c : (FixedBy.subfield F J.conj)ˣ) (hx : MulAut.conj y x = fixedTorus J hJ c)
    (hw : orderOf w = 2) (hwx : w ∈ zpowers x) :
    AbelianGeometry.RootActionCoordinates J ((zpowers x).map MulAut.conj ⊔ zpowers γ) w := by
  let e := MulAut.conj y
  have hle : (zpowers x).map MulAut.conj ⊔ zpowers γ ≤
      (scalarActors J hJ h2).comap (MulAut.congr e).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    apply sup_le
    · apply zpowers_le.mpr
      change MulAut.congr e (MulAut.conj x) ∈ scalarActors J hJ h2
      rw [congr_inner, hx]
      exact ⟨c⁻¹, fixedTorus_action J hJ h2 c⟩
    · apply zpowers_le.mpr
      change MulAut.congr (MulAut.conj y) γ ∈ scalarActors J hJ h2
      rw [congr_entrywise γ y hy]
      refine ⟨1, ?_⟩
      intro t
      simpa only [Units.val_one, one_mul] using entrywise_fixedRoot J hJ h2 γ hγ t
  refine ⟨J, rfl, hJ, h2, e, marked_of_torus J hJ h2 e x w c hx hw hwx, ?_⟩
  intro a ha
  exact hle ha


end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry.CyclicPlacement.FixedCyclicRoot
