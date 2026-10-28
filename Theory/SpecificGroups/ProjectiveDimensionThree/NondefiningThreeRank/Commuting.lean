module

public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank.Lifts
public import Theory.Representation.AbelianAllWeights
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Commuting lifts in projective dimension three

Over an algebraically closed field, a finite abelian matrix group of coprime
order has at most three occurring character weights. Divide each weight by
one fixed weight. If the projective image has exponent three, these ratios
are cube roots of unity; the nonconstant ratios separate projective classes.
There are at most two such ratios, so the projective image has order at most
nine. The kernel and field-extension results in `Lifts` apply this argument
to the full preimage of an elementary subgroup of the actual finite PGL₃.

This proves only the commuting-lift branch. Elementary projective groups
can have noncommuting matrix lifts, and that branch remains separate.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17 and Remark A.2.14, printed pp.37–39.
-/

public section

open Matrix
open scoped MatrixGroups IsMulCommutative

namespace Matrix.ProjectiveDimensionThree
open Representation
variable {F : Type*} [Field F]

private lemma natural_scalar (u : Fˣ) (v : Fin 3 → F) :
    generalLinearNatural 3 (GeneralLinearGroup.scalar (Fin 3) u) v = (u : F) • v := by
  change Matrix.mulVecLin (Matrix.scalar (Fin 3) (u : F)) v = _
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal, Pi.algebraMap_apply]

private lemma weight_on_scalar (H : Subgroup (GL (Fin 3) F))
    (chi : CharacterWeight ((generalLinearNatural (F := F) 3).comp H.subtype))
    (g : H) (u : Fˣ) (hg : g.val = GeneralLinearGroup.scalar (Fin 3) u) :
    chi.val g = u := by
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot chi.property
  simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv
  have h := hv g
  change generalLinearNatural 3 g.val v = (chi.val g : F) • v at h
  rw [hg, natural_scalar] at h
  apply Units.ext
  exact (smul_left_injective F hne) h.symm

private lemma scalar_of_weight_values [IsAlgClosed F]
    (H : Subgroup (GL (Fin 3) F)) [IsMulCommutative H]
    (horder : (Nat.card H : F) ≠ 0) (g : H) (u : Fˣ)
    (hg : ∀ chi : CharacterWeight ((generalLinearNatural (F := F) 3).comp H.subtype),
      chi.val g = u) : g.val = GeneralLinearGroup.scalar (Fin 3) u := by
  let sigma : Representation F H (Fin 3 → F) := (generalLinearNatural (F := F) 3).comp H.subtype
  apply generalLinearNatural_injective 3
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← sigma.iSup_characterWeightSpace_eq_top horder]
  refine iSup_le fun chi v hv => ?_
  simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv
  have h := hv g
  change generalLinearNatural 3 g.val v = generalLinearNatural 3 _ v
  rw [natural_scalar]
  change generalLinearNatural 3 g.val v = (chi.val g : F) • v at h
  rwa [hg chi] at h

/-- For commuting lifts, the ratios of at most three occurring characters
embed an elementary projective image into two groups of cube roots of unity. -/
theorem card_projective_image_le_nine_of_commuting [IsAlgClosed F]
    (H : Subgroup (GL (Fin 3) F)) [Finite H] [IsMulCommutative H]
    (horder : (Nat.card H : F) ≠ 0)
    [IsElementaryAbelian 3 (H.map ProjGenLinGroup.mk)] :
    Nat.card (H.map ProjGenLinGroup.mk) ≤ 3 ^ 2 := by
  classical
  let A := H.map ProjGenLinGroup.mk
  let q : H →* A := {
    toFun := fun h => ⟨ProjGenLinGroup.mk h.val, ⟨h.val, h.property, rfl⟩⟩
    map_one' := by apply Subtype.ext; exact map_one _
    map_mul' := by intro a b; apply Subtype.ext; exact map_mul _ _ _ }
  have hq : Function.Surjective q := by
    rintro ⟨a, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  let s : A → H := fun a => (hq a).choose
  have hs (a : A) : q (s a) = a := (hq a).choose_spec
  let sigma : Representation F H (Fin 3 → F) := (generalLinearNatural (F := F) 3).comp H.subtype
  obtain ⟨hfinite, hweights⟩ := sigma.characterWeight_card_le horder
  let := hfinite
  let := Fintype.ofFinite sigma.CharacterWeight
  have hweights3 : Nat.card sigma.CharacterWeight ≤ 3 := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using hweights
  have hnonempty : Nonempty sigma.CharacterWeight := by
    by_contra hn
    let : IsEmpty sigma.CharacterWeight := not_nonempty_iff.mp hn
    have htop := sigma.iSup_characterWeightSpace_eq_top horder
    simp only [iSup_of_empty] at htop
    exact bot_ne_top htop
  let chi0 : sigma.CharacterWeight := hnonempty.some
  let D := {chi : sigma.CharacterWeight // chi ≠ chi0}
  have hD : Nat.card D ≤ 2 := by
    change Nat.card {chi : sigma.CharacterWeight // chi ≠ chi0} ≤ 2
    have hlt := Fintype.card_subtype_lt (p := fun chi : sigma.CharacterWeight => chi ≠ chi0)
      (x := chi0) (by simp)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hlt
    omega
  have hratio (g : H) (chi : sigma.CharacterWeight) :
      (chi.val g / chi0.val g) ^ 3 = 1 := by
    have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 A) (q g)
    have hscalar : g.val ^ 3 ∈ Subgroup.center (GL (Fin 3) F) := by
      apply ProjGenLinGroup.mk_eq_one.mp
      have hh := congrArg Subtype.val hpow
      change ProjGenLinGroup.mk g.val ^ 3 = 1 at hh
      rwa [map_pow]
    rw [GeneralLinearGroup.center_eq_range_scalar] at hscalar
    obtain ⟨u, hu⟩ := hscalar
    have hx : chi.val g ^ 3 = u := by
      rw [← map_pow]
      exact weight_on_scalar H chi (g ^ 3) u hu.symm
    have hy : chi0.val g ^ 3 = u := by
      rw [← map_pow]
      exact weight_on_scalar H chi0 (g ^ 3) u hu.symm
    rw [div_pow, hx, hy, div_self']
  let evaluate : A → (D → rootsOfUnity 3 F) := fun a chi =>
    ⟨chi.val.val (s a) / chi0.val (s a), by rw [mem_rootsOfUnity]; exact hratio (s a) chi.val⟩
  have hevaluate : Function.Injective evaluate := by
    intro a b hab
    let u : Fˣ := chi0.val (s a) / chi0.val (s b)
    have hvals : ∀ chi : sigma.CharacterWeight, chi.val (s a * (s b)⁻¹) = u := by
      intro chi
      simp only [map_mul, map_inv]
      change chi.val (s a) / chi.val (s b) = u
      by_cases hchi : chi = chi0
      · subst chi
        rfl
      · have he := congrArg Subtype.val (congrFun hab (⟨chi, hchi⟩ : D))
        change chi.val (s a) / chi0.val (s a) = chi.val (s b) / chi0.val (s b) at he
        exact div_eq_div_iff_div_eq_div.mp he
    have hscalar := scalar_of_weight_values H horder (s a * (s b)⁻¹) u hvals
    have hqone : q (s a * (s b)⁻¹) = 1 := by
      apply Subtype.ext
      change ProjGenLinGroup.mk (s a * (s b)⁻¹).val = 1
      rw [hscalar, ProjGenLinGroup.mk_scalar]
    rw [map_mul, map_inv, hs, hs, mul_inv_eq_one] at hqone
    exact hqone
  calc
    Nat.card A ≤ Nat.card (D → rootsOfUnity 3 F) :=
      Nat.card_le_card_of_injective evaluate hevaluate
    _ = Nat.card (rootsOfUnity 3 F) ^ Nat.card D := Nat.card_fun
    _ ≤ 3 ^ Nat.card D := Nat.pow_le_pow_left (card_rootsOfUnity F 3) _
    _ ≤ 3 ^ 2 := pow_le_pow_right' (by decide) hD
end Matrix.ProjectiveDimensionThree

namespace Matrix.ProjectiveDimensionThree
variable {F : Type*} [Field F] [Finite F]

/-- The commuting-lift branch for the actual projective quotient over a finite field. -/
theorem elementary_card_le_nine_of_commuting_lift (h3 : (3 : F) ≠ 0)
    (A : Subgroup PGL(3,F)) [IsElementaryAbelian 3 A]
    [IsMulCommutative (matrixLift A)] : Nat.card A ≤ 3 ^ 2 := by
  classical
  let E := AlgebraicClosure F
  let f : GL (Fin 3) F →* GL (Fin 3) E := GeneralLinearGroup.map (algebraMap F E)
  let j : PGL(3,F) →* PGL(3,E) := ProjGenLinGroup.map (algebraMap F E)
  let H := (matrixLift A).map f
  have hf : Function.Injective f := matrix_map_injective _
  have hj : Function.Injective j := projective_map_injective _
  let : Finite H := Finite.of_equiv (matrixLift A)
    (Subgroup.equivMapOfInjective (matrixLift A) f hf).toEquiv
  let : IsMulCommutative H := Subgroup.map_isMulCommutative (matrixLift A) f
  have hH : H.map ProjGenLinGroup.mk = A.map j := by
    change ((matrixLift A).map f).map ProjGenLinGroup.mk = A.map j
    rw [Subgroup.map_map]
    change (matrixLift A).map (j.comp ProjGenLinGroup.mk) = A.map j
    rw [← Subgroup.map_map]
    congr 1
    exact Subgroup.map_comap_eq_self_of_surjective ProjGenLinGroup.mk_surjective A
  let : IsElementaryAbelian 3 (H.map ProjGenLinGroup.mk) :=
    hH.symm ▸ IsElementaryAbelian.map j
  have horder : (Nat.card H : E) ≠ 0 := by
    have hcard : Nat.card H = Nat.card (matrixLift A) :=
      Subgroup.card_map_of_injective hf
    rw [hcard]
    intro hz
    apply lift_card_ne_zero h3 A
    apply (algebraMap F E).injective
    simpa using hz
  have hb := card_projective_image_le_nine_of_commuting H horder
  rw [hH, Subgroup.card_map_of_injective hj] at hb
  exact hb
end Matrix.ProjectiveDimensionThree
