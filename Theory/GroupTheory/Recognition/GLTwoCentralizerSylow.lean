module
public import Theory.SpecificGroups.GL2.CentralQuotientOddKernel
public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Theory.GroupTheory.CentralizerSylowPromotion

/-!
# Semidihedral Sylow entry from an actual GL₂ centralizer

For a finite group with an involution whose centralizer is an actual central
quotient of GL₂ over a finite field of cardinality three modulo four, the
central kernel is odd and the ambient group has an explicit semidihedral
Sylow two-subgroup contained in that centralizer. Its rotation half-power
is the specified involution, not merely a conjugate involution.

The centralizer involution first detects oddness of the scalar kernel.
The concrete full-GL₂ Sylow subgroup then maps isomorphically to a Sylow
subgroup of the centralizer, since a two-group meets an odd kernel trivially.
Transport its actual generators into the ambient image. The given involution
lies in this image because its central cyclic two-subgroup lies in every
centralizer Sylow. The explicit semidihedral center calculation identifies
it with the rotation half-power. Finally, the centralizer-to-ambient Sylow
promotion preserves the underlying image and hence the same generators.

Source: Brauer, On finite Desarguesian planes II, pp125–126 and (4A), p129.
This is the Sylow entry for the principal two-block application, independent
of the later no-normal-index-two hypothesis and of any recognition theorem.
-/

namespace Theory.GroupTheory

open Subgroup Matrix.GeneralLinearGroup

public theorem exists_gl2Centralizer_semidihedralSylow
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (J : G) (hJ : orderOf J = 2) (hF : Nat.card F % 4 = 3)
    (Z : Subgroup (GL (Fin 2) F)) [Z.Normal]
    (hZ : Z ≤ Subgroup.center (GL (Fin 2) F))
    (centralizerEquiv : centralizer {J} ≃* (GL (Fin 2) F ⧸ Z)) :
    Odd (Nat.card Z) ∧ ∃ (S : Sylow 2 G) (n : ℕ),
      4 ≤ n ∧ Nat.card S = 2 ^ n ∧ J ∈ S ∧
      (S : Subgroup G) ≤ centralizer {J} ∧
      ∃ a b : S, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
        closure ({a, b} : Set S) = ⊤ ∧
        ((a ^ (2 ^ (n - 2)) : S) : G) = J := by
  classical
  let C := centralizer ({J} : Set G)
  let distinguished : C := ⟨J, mem_centralizer_singleton_iff.mpr rfl⟩
  have hdistinguished : distinguished ∈ center C := by
    apply mem_center_iff.mpr
    intro element
    exact Subtype.ext (mem_centralizer_singleton_iff.mp element.property)
  have hdistinguishedOrder : orderOf distinguished = 2 := by
    exact (orderOf_injective C.subtype C.subtype_injective distinguished).symm.trans hJ
  have hquotientCenter : centralizerEquiv distinguished ∈ center (GL (Fin 2) F ⧸ Z) := by
    apply mem_center_iff.mpr
    intro element
    obtain ⟨preimage, rfl⟩ := centralizerEquiv.surjective element
    simpa only [map_mul] using congrArg centralizerEquiv
      (mem_center_iff.mp hdistinguished preimage)
  have hquotientOrder : orderOf (centralizerEquiv distinguished) = 2 := by
    calc
      orderOf (centralizerEquiv distinguished) = orderOf distinguished :=
        orderOf_injective centralizerEquiv.toMonoidHom centralizerEquiv.injective distinguished
      _ = 2 := hdistinguishedOrder
  have hodd : Odd (Nat.card Z) := odd_card_of_central_quotient_involution hF Z hZ
    (centralizerEquiv distinguished) hquotientCenter hquotientOrder
  obtain ⟨P, n, hn, hPcard, rotation, reflection, hrotation, hreflection,
    hconjugate, hgenerate, _hcenter, _hscalar⟩ := exists_semidihedral_sylow F hF
  let projection : GL (Fin 2) F →* C :=
    centralizerEquiv.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hsurjective : Function.Surjective projection :=
    centralizerEquiv.symm.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hkernel : projection.ker = Z := by
    ext element
    simp [projection]
  have hcoprime : Nat.Coprime (Nat.card P) (Nat.card Z) := by
    rw [hPcard]
    exact hodd.coprime_two_left.pow_left n
  have hdisjoint : (P : Subgroup (GL (Fin 2) F)) ⊓ Z = ⊥ :=
    (disjoint_of_coprime_natCard hcoprime).eq_bot
  have hinjective : Function.Injective (projection.subgroupMap (P : Subgroup _)) := by
    apply (injective_iff_map_eq_one _).mpr
    intro element helement
    have hker : (element : GL (Fin 2) F) ∈ Z := by
      rw [← hkernel]
      exact congrArg Subtype.val helement
    have hbot : (element : GL (Fin 2) F) ∈ (⊥ : Subgroup _) := by
      rw [← hdisjoint]
      exact ⟨element.property, hker⟩
    exact Subtype.ext (mem_bot.mp hbot)
  let localSylow : Sylow 2 C := P.mapSurjective hsurjective
  let localEquiv : P ≃* localSylow := MulEquiv.ofBijective
    (projection.subgroupMap (P : Subgroup _))
    ⟨hinjective, projection.subgroupMap_surjective _⟩
  let image := (localSylow : Subgroup C).map C.subtype
  let imageEquiv : P ≃* image := localEquiv.trans
    ((localSylow : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective)
  let rotationImage := imageEquiv rotation
  let reflectionImage := imageEquiv reflection
  have hrotationImage : orderOf rotationImage = 2 ^ (n - 1) :=
    (orderOf_injective imageEquiv.toMonoidHom imageEquiv.injective rotation).trans hrotation
  have hreflectionImage : orderOf reflectionImage = 2 :=
    (orderOf_injective imageEquiv.toMonoidHom imageEquiv.injective reflection).trans hreflection
  have hconjugateImage : reflectionImage * rotationImage * reflectionImage⁻¹ =
      rotationImage ^ (2 ^ (n - 2) - 1) := by
    simpa only [map_mul, map_inv, map_pow] using congrArg imageEquiv hconjugate
  have hgenerateImage : closure ({rotationImage, reflectionImage} : Set image) = ⊤ := by
    change closure ({imageEquiv.toMonoidHom rotation, imageEquiv.toMonoidHom reflection} : Set image) = ⊤
    have hmap := congrArg (Subgroup.map imageEquiv.toMonoidHom) hgenerate
    have htop : Subgroup.map imageEquiv.toMonoidHom (⊤ : Subgroup P) = ⊤ :=
      map_top_of_surjective imageEquiv.toMonoidHom imageEquiv.surjective
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      htop] using hmap
  have hcenterImage : center image = zpowers (rotationImage ^ (2 ^ (n - 2))) :=
    Semidihedral.center_eq hn rotationImage reflectionImage hrotationImage
      hreflectionImage hconjugateImage hgenerateImage
  have hcyclicCentral : zpowers distinguished ≤ center C := zpowers_le.mpr hdistinguished
  let _ : (zpowers distinguished).Normal := ⟨by
    intro element helement actor
    have hcomm := mem_center_iff.mp (hcyclicCentral helement) actor
    simpa only [hcomm, mul_assoc, mul_inv_cancel, mul_one] using helement⟩
  have hcyclicTwo : IsPGroup 2 (zpowers distinguished) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hdistinguishedOrder, pow_one]
  have hlocal : distinguished ∈ localSylow :=
    hcyclicTwo.le_sylow_of_normal localSylow (mem_zpowers distinguished)
  have hJimage : J ∈ image := ⟨distinguished, hlocal, rfl⟩
  let imageInvolution : image := ⟨J, hJimage⟩
  have hJcenter : imageInvolution ∈ center image := by
    apply mem_center_iff.mpr
    intro element
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (map_subtype_le (localSylow : Subgroup C) element.property))
  have hhalfOrder : orderOf (rotationImage ^ (2 ^ (n - 2))) = 2 := by
    have hexponent : n - 1 = (n - 2) + 1 := by omega
    have hdiv : 2 ^ (n - 2) ∣ orderOf rotationImage := by
      rw [hrotationImage, hexponent, pow_succ]
      exact dvd_mul_right _ _
    rw [orderOf_pow_of_dvd (by positivity) hdiv, hrotationImage, hexponent, pow_succ]
    exact Nat.mul_div_cancel_left _ (by positivity)
  have hhalf : rotationImage ^ (2 ^ (n - 2)) = imageInvolution := by
    rw [hcenterImage, mem_zpowers_iff_mem_range_orderOf, hhalfOrder] at hJcenter
    obtain ⟨exponent, hexponent, heq⟩ := Finset.mem_image.mp hJcenter
    have hbound := Finset.mem_range.mp hexponent
    interval_cases exponent
    · have hone : J = 1 := congrArg Subtype.val (by simpa using heq.symm)
      simp [hone] at hJ
    · simpa using heq
  have hcenterAmbient : (center image).map image.subtype = zpowers J := by
    rw [hcenterImage, MonoidHom.map_zpowers, hhalf]
    rfl
  obtain ⟨S, hS⟩ := exists_ambient_sylow_of_centralizer_center J hJ localSylow hcenterAmbient
  refine ⟨hodd, S, n, hn, ?_, ?_, ?_, ?_⟩
  · rw [hS]
    exact (Nat.card_congr imageEquiv.toEquiv).symm.trans hPcard
  · change J ∈ (S : Subgroup G)
    rw [hS]
    exact hJimage
  · rw [hS]
    exact map_subtype_le _
  · change ∃ a b : (S : Subgroup G), orderOf a = _ ∧ orderOf b = _ ∧
      b * a * b⁻¹ = a ^ _ ∧ closure ({a, b} : Set (S : Subgroup G)) = ⊤ ∧
      (((a ^ (2 ^ (n - 2))) : (S : Subgroup G)) : G) = J
    rw [hS]
    exact ⟨rotationImage, reflectionImage, hrotationImage, hreflectionImage,
      hconjugateImage, hgenerateImage, congrArg Subtype.val hhalf⟩

end Theory.GroupTheory
