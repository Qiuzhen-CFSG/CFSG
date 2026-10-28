module

public import Theory.Representation.BinaryPermutation.InvolutionFixedSpace
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.AugmentationModel

/-!
# Four-groups on the eleven-point M₁₁ module

The standard involution has four transpositions, so restriction to seven
coordinates embeds its full fixed space in a seven-dimensional space. The
checked involution conjugacy theorem gives codimension at least four for every
involution. If a four-group had codimension at most four, its distinct
involutions would have equal fixed spaces. Indicator functions of their point
orbits distinguish them, giving a contradiction.

Odd-degree augmentation preserves fixed codimensions. The actual zero-extension
and quotient equivalence then gives the bound on the marked point representation.

Source application: Aschbacher--Smith, K.4, printed p.457 (PDF p.468),
with the binary permutation conventions of B.3. This is the point-module
geometry used in the M₁₁ exclusion; it assumes no cubic-ratio bound.
-/

public section
open Representation.BinaryOffender BinaryPermutation Subgroup Sporadic.Mathieu

namespace Representation.MathieuSmall.M11PointGeometry
private noncomputable abbrev fullRepresentation := (representation (Fin 11)).comp M11.subtype

private theorem generator_fixed_finrank_le :
    Module.finrank (ZMod 2) (fixedSpace fullRepresentation (zpowers m11GeneratorAInM11)) ≤ 7 := by
  let f : fixedSpace fullRepresentation (zpowers m11GeneratorAInM11) →ₗ[ZMod 2]
      (Fin 7 → ZMod 2) :=
    { toFun := fun v i => v.val (![0, 1, 2, 3, 5, 6, 8] i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    change v = 0
    have hz (i : Fin 7) : v.val (![0, 1, 2, 3, 5, 6, 8] i) = 0 :=
      congrFun hv i
    have hfix := (mem_fixedSpace_zpowers_iff fullRepresentation _ v.val).mp v.property
    have hfix' (i : Fin 11) : v.val (m11GeneratorA.symm i) = v.val i :=
      congrFun hfix i
    have h0 := hz 0
    have h1 := hz 1
    have h2 := hz 2
    have h3 := hz 3
    have h5 := hz 4
    have h6 := hz 5
    have h8 := hz 6
    have h4 := hfix' 0
    have h7 := hfix' 5
    have h9 := hfix' 8
    have h10 := hfix' 2
    change v.val 4 = v.val 0 at h4
    change v.val 7 = v.val 5 at h7
    change v.val 9 = v.val 8 at h9
    change v.val 10 = v.val 2 at h10
    apply Subtype.ext
    ext i
    fin_cases i <;> simp_all
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa using hd

private theorem involution_codim (a : M11) (ha : orderOf a = 2) :
    4 ≤ fixedCodim fullRepresentation (zpowers a) := by
  have hgen : 4 ≤ fixedCodim fullRepresentation (zpowers m11GeneratorAInM11) := by
    have h := fixedCodim_add_finrank fullRepresentation (zpowers m11GeneratorAInM11)
    have hd := generator_fixed_finrank_le
    rw [finrank_full] at h
    change _ + _ = 11 at h
    omega
  obtain ⟨g, hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA a ha)
  rw [← hg, fixedCodim_zpowers_conj] at hgen
  exact hgen

private theorem full_rankTwo_fixedCodim_ge_five (A : Subgroup M11)
    (hA : IsElementaryTwo A) (hr : rank A = 2) :
    5 ≤ fixedCodim fullRepresentation A := by
  classical
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hcard : Nat.card A = 4 := by rw [hA.card_eq_two_pow_rank, hr]; rfl
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra! hn
    have hle : A ≤ zpowers a := by
      intro b hb
      by_cases hb1 : b = 1
      · simp [hb1]
      · rw [hn b hb hb1]
        exact mem_zpowers a
    have hc := card_le_of_le hle
    rw [hcard, Nat.card_zpowers, ha2] at hc
    omega
  have hb2 : orderOf b = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hb1
  by_contra hn
  have hc : fixedCodim fullRepresentation A ≤ 4 := by omega
  have he (t : M11) (ht : t ∈ A) (ht2 : orderOf t = 2) :
      fixedSpace fullRepresentation A = fixedSpace fullRepresentation (zpowers t) := by
    have hle : fixedSpace fullRepresentation A ≤
        fixedSpace fullRepresentation (zpowers t) := by
      intro v hv
      rw [mem_fixedSpace_zpowers_iff]
      exact hv ⟨t, ht⟩
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hmono := Submodule.finrank_mono hle
    have hlo := involution_codim t ht2
    have hdA := fixedCodim_add_finrank fullRepresentation A
    have hdt := fixedCodim_add_finrank fullRepresentation (zpowers t)
    omega
  have hab := (he a ha ha2).symm.trans (he b hb hb2)
  change fixedSpace ((representation (Fin 11)).comp M11.subtype) (zpowers a) =
    fixedSpace ((representation (Fin 11)).comp M11.subtype) (zpowers b) at hab
  rw [fixedSpace_comp_map, fixedSpace_comp_map, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers] at hab
  have hp (t : M11) (ht : orderOf t = 2) : t.val ^ 2 = 1 := by
    have ht' : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    exact congrArg Subtype.val ht'
  exact hba (Subtype.ext (involution_eq_of_fixedSpace_eq a.val b.val
    (hp a ha2) (hp b hb2) hab).symm)

open Representation.MathieuSmall.M12Recognition
open Representation.MathieuSmall.M12Recognition.PointClassification

/-- A rank-two elementary subgroup displaces at least five dimensions on the
eleven-point augmentation module. -/
theorem augmentation_rankTwo_fixedCodim_ge_five (A : Subgroup M11)
    (hA : IsElementaryTwo A) (hr : rank A = 2) :
    5 ≤ fixedCodim augmentationRepresentation A := by
  have he : fixedCodim augmentationRepresentation A = fixedCodim fullRepresentation A := by
    change fixedCodim ((coreRepresentation (Fin 11)).comp M11.subtype) A =
      fixedCodim ((representation (Fin 11)).comp M11.subtype) A
    unfold fixedCodim
    rw [fixedSpace_comp_map, fixedSpace_comp_map]
    exact fixedCodim_core_eq_full_odd (Fin 11) (by decide) (A.map M11.subtype)
  rw [he]
  exact full_rankTwo_fixedCodim_ge_five A hA hr

/-- The same bound on the literal restricted M₁₂ point heart, with its M₁₁ marking. -/
theorem point_rankTwo_fixedCodim_ge_five (A : Subgroup M11)
    (hA : IsElementaryTwo A) (hr : rank A = 2) :
    5 ≤ fixedCodim pointRepresentation A := by
  have he := OddTransport.fixedCodim_eq_of_equivariant
    augmentationRepresentation pointRepresentation augmentationEquivPoint.toLinearEquiv
    (fun g v => LinearMap.congr_fun (augmentationEquivPoint.isIntertwining' g) v) A
  rw [← he]
  exact augmentation_rankTwo_fixedCodim_ge_five A hA hr
end Representation.MathieuSmall.M11PointGeometry

