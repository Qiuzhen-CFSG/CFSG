module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.ProductSylow
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCriterion
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic

/-!
# Conjugacy of the Rudvalis centralizer's derived eight-group

An actual involution centralizer identified with E₄ × Sz(8) supplies an
order-256 Sylow whose involutions are all central. In any ambient Sylow
containing it, Sylow maximality identifies it with the intersection with
the full involution centralizer. Conjugation to the checked `localP` moves
the involution and the derived eight-group together.

The proved `localCentralizerDerivedNormal` and the existing elementary
catalogue identify the transported derived subgroup with `elementary 2`.
The final theorem discharges the finite local criterion in the preceding
conditional reduction, using the literal embedding of `NormalizerGeometry`.
Only the earlier-source identification of the actual involution centralizer
as E₄ × Sz(8) remains an input; no component-normalizer cubic extension is used.

Source: GLS3 Table 5.3r and pp.291–292; Aschbacher–Smith I.2.2(7), pp.412–413.
The intrinsic product calculations are those already proved in `ProductSylow`.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry
open Subgroup BenderSuzuki.MatrixGroups
open SylowOvergroups.RadicalCoverage.LocalCover
open scoped IsMulCommutative

variable {E : Type} [Group E]

/-- The centrality of every involution in the Suzuki product Sylow, retained
on its literal ambient image. This is stronger than a cardinality condition. -/
public theorem sylowImage_square_one_central [IsElementaryAbelian 2 E]
    (f : E × SuzukiMatrixGroup 1 →* Model) (hf : Function.Injective f)
    (x : Model) (hx : x ∈ sylowImage f) (hsq : x ^ 2 = 1) :
    x ∈ centralizer (sylowImage f : Set Model) := by
  obtain ⟨x, hx, rfl⟩ := hx
  have hs : x ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using hsq)
  have hs2 : x.2 ^ 2 = 1 := congrArg Prod.snd hs
  have hc : (⟨x.2, hx.2⟩ : SuzukiRootSubgroup 1) ∈ center (SuzukiRootSubgroup 1) :=
    (suzukiRootSubgroup_square_iff_center 1 (by decide) _).mp (Subtype.ext hs2)
  apply mem_centralizer_iff.mpr
  rintro y ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg f
  exact Prod.ext (mul_comm _ _) (congrArg Subtype.val (mem_center_iff.mp hc ⟨y.2, hy.2⟩))

/-- The root-center image is elementary abelian, even before identifying it
with a conjugate of the marked eight-group. -/
public theorem derivedImage_elementary
    (f : E × SuzukiMatrixGroup 1 →* Model) : IsElementaryAbelian 2 (derivedImage f) := by
  let : IsMulCommutative (derivedImage f) := le_centralizer_iff_isMulCommutative.mp
    ((derivedImage_le f).trans (sylowImage_centralizes_derived f))
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  rintro ⟨_, x, hx, rfl⟩
  apply Subtype.ext
  change (f x) ^ 2 = 1
  rw [← map_pow]
  have hs : x ^ 2 = 1 := by
    obtain ⟨hx1, z, hz, hz2⟩ := hx
    apply Prod.ext
    · change x.1 ^ 2 = 1
      rw [show x.1 = 1 from hx1, one_pow]
    · change x.2 ^ 2 = 1
      rw [← hz2]
      exact congrArg Subtype.val
        ((suzukiRootSubgroup_square_iff_center 1 (by decide) z).mpr hz)
  rw [hs, map_one]

/-- An ambient Sylow containing this actual centralizer Sylow cannot contain
any additional elements of the centralizer. -/
public theorem centralizerSylow_eq_intersection
    (C : Subgroup Model) (e : C ≃* E × SuzukiMatrixGroup 1) (hE : Nat.card E = 4)
    (S : Sylow 2 Model) (hTS : sylowImage (centralizerEmbedding C e) ≤ S) :
    sylowImage (centralizerEmbedding C e) = (S : Subgroup Model) ⊓ C := by
  let R := centralizerSylow C e hE
  have hR : (R : Subgroup C) ≤ (S : Subgroup Model).subgroupOf C := by
    intro x hx
    apply hTS
    rw [← centralizerSylow_image C e hE]
    exact mem_map_of_mem C.subtype hx
  have he := R.is_maximal' S.isPGroup'.comap_subtype hR
  rw [← centralizerSylow_image C e hE, ← he]
  exact subgroupOf_map_subtype _ _

private theorem central_involution_mem_sylow {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (x : G) (hx : x ∈ center G) (hsq : x ^ 2 = 1) : x ∈ P := by
  let H := zpowers x
  have hH : H ≤ center G := zpowers_le.mpr hx
  let : H.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hH hn) g, mul_inv_cancel_right]
    exact hn⟩
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.zpowers_of_pow_eq_one hsq
  exact (IsElementaryAbelian.isPGroup 2 H).le_sylow_of_normal P (mem_zpowers x)

/-- The central involution lies in the same Sylow chosen by the product
identification; no independent Sylow or marking is prescribed. -/
public theorem involution_mem_centralizerSylow_image (i : Model) (hi : i ^ 2 = 1)
    (e : centralizer ({i} : Set Model) ≃* E × SuzukiMatrixGroup 1) (hE : Nat.card E = 4) :
    i ∈ sylowImage (centralizerEmbedding (centralizer ({i} : Set Model)) e) := by
  let C := centralizer ({i} : Set Model)
  let x : C := ⟨i, mem_centralizer_singleton_iff.mpr rfl⟩
  have hx : x ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp y.property)
  rw [← centralizerSylow_image C e hE]
  exact mem_map_of_mem C.subtype
    (central_involution_mem_sylow (centralizerSylow C e hE) x hx (Subtype.ext hi))

private theorem map_centralizer_singleton (a : MulAut Model) (i : Model) :
    (centralizer ({i} : Set Model)).map a.toMonoidHom =
      centralizer ({a i} : Set Model) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change a y * a i = a i * a y
    simpa only [map_mul] using congrArg a (mem_centralizer_singleton_iff.mp hy)
  · intro hx
    refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply a.injective
    simpa only [map_mul, a.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

/-- Application of the finite local criterion to the actual involution
centralizer. Its output is precisely the `hmark` input of
`NormalizerGeometry.sylowImage_le_conjugate_core` and
`NormalizerGeometry.exists_compatible_normalizer_sylow`.

This is a conditional reduction: the local criterion must still be proved
before it establishes the requested source conjugacy. -/
public theorem derivedImage_conjugate_of_localCentralizerDerivedNormal
    [IsElementaryAbelian 2 E] (hlocal : LocalCentralizerDerivedNormal)
    (i : Model) (hi : i ^ 2 = 1)
    (e : centralizer ({i} : Set Model) ≃* E × SuzukiMatrixGroup 1)
    (hE : Nat.card E = 4) :
    ∃ g : Model, derivedImage (centralizerEmbedding (centralizer ({i} : Set Model)) e) =
      (elementary 2).map (MulAut.conj g).toMonoidHom := by
  let C := centralizer ({i} : Set Model)
  let f := centralizerEmbedding C e
  have hf := centralizerEmbedding_injective C e
  obtain ⟨S, hTS⟩ := (sylowImage_isPGroup hE f hf).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S SylowInvariantPair.sylow
  let a := MulAut.conj g
  let f' := a.toMonoidHom.comp f
  have hf' : Function.Injective f' := a.injective.comp hf
  have hP : (S : Subgroup Model).map a.toMonoidHom = localP :=
    congrArg (fun R : Sylow 2 Model => (R : Subgroup Model)) hg
  have hT : sylowImage f' = localP ⊓ centralizer ({a i} : Set Model) := by
    change (rootProduct E).map (a.toMonoidHom.comp f) = _
    rw [← map_map]
    change (sylowImage f).map a.toMonoidHom = _
    rw [centralizerSylow_eq_intersection C e hE S hTS,
      map_inf _ _ _ a.injective, hP, map_centralizer_singleton]
  have hiT := involution_mem_centralizerSylow_image i hi e hE
  have hiP : a i ∈ localP := by
    rw [← hP]
    exact mem_map_of_mem _ (hTS hiT)
  have hi' : (a i) ^ 2 = 1 := by rw [← map_pow, hi, map_one]
  have hn := hlocal (a i) hiP hi'
  dsimp only at hn
  rw [← hT] at hn
  have hnD : localP ≤ normalizer (derivedImage f' : Set Model) := by
    rw [← sylowImage_derived]
    exact hn (sylowImage_card hE f' hf') (sylowImage_square_one_central f' hf')
  have hD : derivedImage f' = elementary 2 :=
    RankOneEightCharacteristic.eq_elementary_two_of_normal_eight _
      ((derivedImage_le f').trans (hT ▸ inf_le_left)) hnD
      (derivedImage_elementary f') (derivedImage_card f' hf')
  refine ⟨g⁻¹, ?_⟩
  have he := congrArg (fun H : Subgroup Model => H.map a.symm.toMonoidHom) hD
  change ((rootDerived E).map (a.toMonoidHom.comp f)).map a.symm.toMonoidHom = _ at he
  rw [map_map] at he
  have hcomp : a.symm.toMonoidHom.comp (a.toMonoidHom.comp f) = f := by
    ext x
    exact a.symm_apply_apply (f x)
  rw [hcomp] at he
  exact he

/-- The derived eight-group of the Sylow supplied by an actual E₄ × Sz(8)
involution-centralizer identification is conjugate to the fixed max4 mark.
This discharges the `hmark` premise of the parent normalizer-incidence theorem.
The finite local normalization criterion is proved, not an additional premise.
The earlier-source centralizer identification remains with its source owner. -/
public theorem derivedImage_conjugate [IsElementaryAbelian 2 E]
    (i : Model) (hi : i ^ 2 = 1)
    (e : centralizer ({i} : Set Model) ≃* E × SuzukiMatrixGroup 1)
    (hE : Nat.card E = 4) :
    ∃ g : Model, derivedImage (centralizerEmbedding (centralizer ({i} : Set Model)) e) =
      (elementary 2).map (MulAut.conj g).toMonoidHom :=
  derivedImage_conjugate_of_localCentralizerDerivedNormal
    localCentralizerDerivedNormal i hi e hE

end Rudvalis.CoveringIncidence.NormalizerGeometry
