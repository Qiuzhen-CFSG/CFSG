module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import BenderSuzuki.SE.Lemma312

/-!
# Transport of the literal residual generators to a quotient model

For a subgroup `B` and elements `z,t`, `borelPairGenerated B z t` adjoins the
displacements `a(t)t⁻¹` for automorphisms preserving `B` and `Bᵗ`.
If the actual two-point stabilizer `D` normalizes `L`, conjugation by each
of its elements induces such an automorphism on every model of `L/O₂'(L)`.
In particular the image of `[O₂'(D),t]` belongs to this generated subgroup.
Together with the images of `z,t` this generates the whole quotient.

This is the group-theoretic connection needed for the unitary exclusion in
GLS4, Chapter 2, Lemma 12.2(a), using Chapter 4, Lemma 3.2(h). The concrete
unitary assertion that this generated subgroup is proper is not assumed or
proved here. No automorphism of the quotient is assumed inner, and no
splitting of the central extension is used.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped commutatorElement
universe u v

/-- The source generators in a group with two distinguished point stabilizers. -/
@[expose] public def borelPairGenerated {Q : Type*} [Group Q] (B : Subgroup Q) (z t : Q) : Subgroup Q :=
  zpowers z ⊔ zpowers t ⊔ closure
    {x | ∃ a : MulAut Q, B.map a.toMonoidHom = B ∧
      (rightConjugate B t).map a.toMonoidHom = rightConjugate B t ∧ x = a t * t⁻¹}

private theorem rightConjugate_comap_subtype {G : Type*} [Group G]
    (H L : Subgroup G) (t : L) :
    rightConjugate (H.comap L.subtype) t = (rightConjugate H (t : G)).comap L.subtype := by
  ext x
  simp only [rightConjugate, Subgroup.conjBy, mem_map, mem_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨(y : G), hy, congrArg Subtype.val he⟩
  · rintro ⟨y, hy, he⟩
    have hyt : y = (t : G) * x * (t : G)⁻¹ := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] at he
      change (t : G)⁻¹ * y * (t : G) = (x : G) at he
      rw [← he]
      group
    have hyL : y ∈ L := by rw [hyt]; exact L.mul_mem (L.mul_mem t.property x.property) (L.inv_mem t.property)
    exact ⟨⟨y, hyL⟩, hy, Subtype.ext he⟩

private theorem normalizer_preserves_intersection {G : Type*} [Group G]
    (H L : Subgroup G) (a : normalizer (L : Set G)) (ha : (a : G) ∈ H) :
    (H.comap L.subtype).map (L.normalizerMonoidHom a).toMonoidHom = H.comap L.subtype := by
  let α := L.normalizerMonoidHom a
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem ha hy) (H.inv_mem ha)
  · intro x hx
    refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
    change (α.symm x : G) ∈ H
    have he : (α.symm x : G) = (a : G)⁻¹ * x * (a : G) := by
      have hh := congrArg Subtype.val (α.apply_symm_apply x)
      change (a : G) * (α.symm x : G) * (a : G)⁻¹ = (x : G) at hh
      rw [← hh]
      group
    rw [he]
    exact H.mul_mem (H.mul_mem (H.inv_mem ha) hx) ha

private theorem quotient_normalizer_preserves_intersection
    {G : Type*} [Group G] {Q : Type*} [Group Q]
    (H L : Subgroup G) (N : Subgroup L) [N.Characteristic]
    (e : (L ⧸ N) ≃* Q) (a : normalizer (L : Set G)) (ha : (a : G) ∈ H) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
    let α := MulAut.congr e (quotientAut N (L.normalizerMonoidHom a))
    ((H.comap L.subtype).map f).map α.toMonoidHom = (H.comap L.subtype).map f := by
  dsimp only
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  let β := L.normalizerMonoidHom a
  let α := MulAut.congr e (quotientAut N β)
  have he : α.toMonoidHom.comp f = f.comp β.toMonoidHom := by
    ext x
    change e (quotientAut N β (e.symm (e (QuotientGroup.mk' N x)))) = _
    rw [e.symm_apply_apply, quotientAut_apply_mk]
    rfl
  change ((H.comap L.subtype).map f).map α.toMonoidHom = _
  rw [map_map, he, ← map_map, normalizer_preserves_intersection H L a ha]

/-- The literal generators of `L` fill the quotient model. Each conjugate
of `t` by an element of the odd core of `D` is accounted for by the induced
automorphism preserving the two local Borel images. -/
public theorem borelPairGenerated_eq_top_of_residualGenerated
    {G : Type u} [Group G] [Finite G] {Q : Type v} [Group Q]
    (M : Subgroup G) (z t : G)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (e : (residualGenerated M z t ⧸ twoPrimeCore (residualGenerated M z t)) ≃* Q) :
    let L := residualGenerated M z t
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (twoPrimeCore L))
    let zL : L := ⟨z, (le_sup_left.trans le_sup_left : zpowers z ≤ L) (mem_zpowers z)⟩
    let tL : L := ⟨t, (le_sup_right.trans le_sup_left : zpowers t ≤ L) (mem_zpowers t)⟩
    borelPairGenerated ((M.comap L.subtype).map f) (f zL) (f tL) = ⊤ := by
  dsimp only
  let L := residualGenerated M z t
  let N := twoPrimeCore L
  let : N.Characteristic := pPrimeCore_characteristic (p := 2) (G := L)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  let zL : L := ⟨z, (le_sup_left.trans le_sup_left : zpowers z ≤ L) (mem_zpowers z)⟩
  let tL : L := ⟨t, (le_sup_right.trans le_sup_left : zpowers t ≤ L) (mem_zpowers t)⟩
  let B := (M.comap L.subtype).map f
  let R := borelPairGenerated B (f zL) (f tL)
  let P := (R.comap f).map L.subtype
  have hzR : f zL ∈ R := (le_sup_left.trans le_sup_left : zpowers (f zL) ≤ R) (mem_zpowers _)
  have htR : f tL ∈ R := (le_sup_right.trans le_sup_left : zpowers (f tL) ≤ R) (mem_zpowers _)
  have hzP : z ∈ P := ⟨zL, hzR, rfl⟩
  have htP : t ∈ P := ⟨tL, htR, rfl⟩
  have hconj : ∀ a ∈ residualPairStabilizer M t, MulAut.conj a t ∈ P := by
    intro a ha
    let an : normalizer (L : Set G) := ⟨a, hDN ha⟩
    let β := L.normalizerMonoidHom an
    let α := MulAut.congr e (quotientAut N β)
    have he (x : L) : α (f x) = f (β x) := by
      change e (quotientAut N β (e.symm (e _))) = _
      rw [e.symm_apply_apply, quotientAut_apply_mk]
      rfl
    have hB : B.map α.toMonoidHom = B :=
      quotient_normalizer_preserves_intersection M L N e an ha.1
    have hBt : (rightConjugate B (f tL)).map α.toMonoidHom = rightConjugate B (f tL) := by
      have hright : rightConjugate B (f tL) = ((rightConjugate M t).comap L.subtype).map f := by
        rw [← rightConjugate_comap_subtype M L tL]
        exact (rightConjugate_map (M.comap L.subtype) f tL).symm
      rw [hright]
      exact quotient_normalizer_preserves_intersection (rightConjugate M t) L N e an ha.2
    have hd : α (f tL) * (f tL)⁻¹ ∈ R :=
      (show Subgroup.closure _ ≤ R from le_sup_right) (subset_closure ⟨α, hB, hBt, rfl⟩)
    have hβ : f (β tL) ∈ R := by
      rw [← he]
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using R.mul_mem hd htR
    exact ⟨β tL, hβ, rfl⟩
  have hLP : L ≤ P := by
    apply sup_le (sup_le (zpowers_le.mpr hzP) (zpowers_le.mpr htP))
    apply commutator_le.mpr
    intro a ha b hb
    have haD : a ∈ residualPairStabilizer M t := by
      obtain ⟨a, _, rfl⟩ := ha
      exact a.property
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    have hp : MulAut.conj a (t ^ n) ∈ P := by
      simpa only [map_zpow] using P.zpow_mem (hconj a haD) n
    exact P.mul_mem hp (P.inv_mem (P.zpow_mem htP n))
  have hsurj : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨w, hw, he⟩ := hLP y.property
  have hwy : w = y := Subtype.ext he
  exact hwy ▸ hw
end BenderSuzuki.ZD
