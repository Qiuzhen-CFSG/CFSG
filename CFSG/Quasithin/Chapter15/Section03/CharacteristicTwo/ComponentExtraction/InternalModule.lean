module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import GorensteinWalter.Section2.Bender1970_18
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.GroupTheory.NormalClosureSylowActionCore
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The internal module for the characteristic-two branches

For an outside overgroup `I`, the source's Sylow conclusion puts `S` in
`Syl₂(I)`. The central involutions of `T` centralize `S`, hence `O₂(I)`.
Self-centralization of `F*(I) = O₂(I)` puts them in `O₂(I)`. Their `I`-span
therefore lies in the elementary omega-center of that core. We retain the
actual subgroup of `I` and its centralizer quotient in the resulting binary
representation. Nontrivial Thompson image then supplies an FF-offender.

The generalized-Fitting comparison follows the checked argument in
`ChapterE/Section02/TwoConjugate/CentralAction.lean`, comparing the two actual
Fitting and component definitions rather than assuming they agree.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.14,
15.3.11(1),(11), and the opening proofs of 15.3.15 and 15.3.26,
printed pp.78, 1123–1125, 1130.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The genuine generalized-Fitting equality implies the centralizer form
of characteristic two. -/
theorem centralizer_twoCore_le [Finite G] {I : Subgroup G}
    (hf : HasCharacteristicTwo I) :
    centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
  have hbridge : GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup I) ≤
      Theory.GroupTheory.generalizedFitting I := by
    apply sup_le
    · apply le_trans _ (Theory.GroupTheory.fitting_le_generalizedFitting I)
      exact le_sSup ⟨fittingSubgroupOf_normal _ inferInstance,
        GorensteinWalter.fittingSubgroupOf_isNilpotent _⟩
    · apply sSup_le
      intro E hE
      have hsub : E.IsSubnormal := by
        have hh := hE.2.1.map (show Function.Surjective (⊤ : Subgroup I).subtype from
          fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
        simpa only [map_subgroupOf_eq_of_le (show E ≤ ⊤ from le_top)] using hh
      exact Theory.GroupTheory.component_le_generalizedFitting I E
        ⟨hsub, (Theory.GroupTheory.isQuasisimple_def E).mpr hE.2.2.2⟩
  rw [show Theory.GroupTheory.generalizedFitting I = pCore 2 I from hf] at hbridge
  exact (centralizer_le hbridge).trans
    (GorensteinWalter.fstar_self_centralizing.trans hbridge)

namespace LocalData
variable (d : LocalData G)

/-- The involutions of the fixed Sylow center centralize its plane stabilizer. -/
theorem Z_le_centralizer_S : d.Z ≤ centralizer (d.S : Set G) := by
  intro z hz s hs
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff (d.T : Subgroup G) z).mp hz).2.2
    s hs.1

/-- The earlier containment `V ≤ T` places the central involutions in `S`. -/
theorem Z_le_S (hVT : d.V ≤ (d.T : Subgroup G)) : d.Z ≤ d.S := by
  intro z hz
  have hzm := (Stellmacher.mem_omegaOneCenterAmbient_iff (d.T : Subgroup G) z).mp hz
  refine ⟨hzm.1, ?_⟩
  apply Subgroup.centralizer_le_normalizer
  intro v hv
  have hvT : v ∈ (d.T : Subgroup G) := hVT (map_subtype_le _ hv)
  exact hzm.2.2 v hvT

/-- `U_I` is contained in its defining local overgroup. -/
theorem UI_le {I : Subgroup G} (hZI : d.Z ≤ I) : d.UI I ≤ I :=
  conjugateSpanBy_le_self hZI

/-- The normality of the span is inside `I`. -/
instance UI_subgroupOf_normal (I : Subgroup G) : ((d.UI I).subgroupOf I).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy d.Z I)

/-- The source ambient span is precisely the internal normal closure. -/
theorem UI_subgroupOf_eq_normalClosure {I : Subgroup G} (hZI : d.Z ≤ I) :
    (d.UI I).subgroupOf I = normalClosure (d.Z.subgroupOf I : Set I) := by
  apply le_antisymm
  · let N := normalClosure (d.Z.subgroupOf I : Set I)
    have hle : d.UI I ≤ N.map I.subtype := by
      apply conjugateSpanBy_le
      · intro z hz
        exact ⟨⟨z, hZI hz⟩, le_normalClosure hz, rfl⟩
      · exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le N)).mp (by
          rw [show (N.map I.subtype).subgroupOf I = N from
            comap_map_eq_self_of_injective I.subtype_injective N]
          infer_instance)
    intro x hx
    obtain ⟨y, hy, he⟩ := hle hx
    exact (Subtype.ext he : y = x) ▸ hy
  · exact normalClosure_le_normal (comap_mono (le_conjugateSpanBy d.Z I))

/-- The action denominator is the internal centralizer of the actual `U_I`. -/
theorem starMap_ker {I : Subgroup G} (hZI : d.Z ≤ I) :
    (d.starMap I).ker = centralizer ((d.UI I).subgroupOf I : Set I) := by
  rw [show (d.starMap I).ker = localActionKernel d.Z I from QuotientGroup.ker_mk' _]
  ext x
  constructor
  · intro hx u hu
    exact Subtype.ext (hx u hu)
  · intro hx u hu
    exact congrArg Subtype.val (hx ⟨u, d.UI_le hZI hu⟩ hu)

/-- In characteristic two the span lies in the omega-center of the
intrinsic two-core, without assuming it is elementary abelian. -/
theorem UI_subgroupOf_le_coreOmega [Finite G] {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hf : HasCharacteristicTwo I) :
    (d.UI I).subgroupOf I ≤ Stellmacher.omegaOneCenterAmbient (pCore 2 I) := by
  obtain ⟨P, hP⟩ := hS
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have hQI : pCore 2 I ≤ (P : Subgroup I) := pCore_isPGroup.le_sylow_of_normal P
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQnorm : (Stellmacher.omegaOneCenterAmbient (pCore 2 I)).Normal := by
    let Q := pCore 2 I
    let C := center Q
    let W := omega₁ C (p := 2)
    let E := W.map C.subtype
    let _ : W.Characteristic := omega₁_characteristic C
    let _ : E.Characteristic := characteristic_of_characteristic_of_characteristic
    exact ConjAct.normal_of_characteristic_of_normal
  let _ := hQnorm
  rw [d.UI_subgroupOf_eq_normalClosure (hZS.trans hSI)]
  apply normalClosure_le_normal
  intro z hz
  have hzc : z ∈ centralizer (pCore 2 I : Set I) := by
    intro q hq
    apply Subtype.ext
    exact d.Z_le_centralizer_S hz q (hP ▸ mem_map_of_mem I.subtype (hQI hq))
  apply (Stellmacher.mem_omegaOneCenterAmbient_iff (pCore 2 I) z).mpr
  refine ⟨centralizer_twoCore_le hf hzc, ?_, hzc⟩
  apply Subtype.ext
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff (d.T : Subgroup G) (z : G)).mp hz).2.1

/-- The elementary abelian internal module required before applying B.2.7. -/
theorem UI_subgroupOf_elementary [Finite G] {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hf : HasCharacteristicTwo I) : IsElementaryAbelian 2 ((d.UI I).subgroupOf I) := by
  let _ := Stellmacher.omegaOneCenterAmbient_elementaryAbelian (pCore 2 I)
  have hle := d.UI_subgroupOf_le_coreOmega hS hZS hf
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    exact congrArg (fun w : Stellmacher.omegaOneCenterAmbient (pCore 2 I) => (w : I))
      (mul_comm (⟨x, hle x.property⟩ : Stellmacher.omegaOneCenterAmbient (pCore 2 I))
        ⟨y, hle y.property⟩)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : I) (hle x.property))

/-- The same elementary abelian module, represented in the ambient group. -/
theorem UI_elementary [Finite G] {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hf : HasCharacteristicTwo I) : IsElementaryAbelian 2 (d.UI I) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := d.UI_subgroupOf_elementary hS hZS hf
  have hZI : d.Z ≤ I := hZS.trans (Chapter1.isSylowIn_iff.mp hS).2.1
  have hm := IsElementaryAbelian.map (p := 2) (A := (d.UI I).subgroupOf I) I.subtype
  rwa [map_subgroupOf_eq_of_le (d.UI_le hZI)] at hm

/-- The faithful action quotient is two-reduced. This uses only the source
Sylow conclusion and central generation, so does not require characteristic two. -/
theorem star_twoCore_eq_bot [Finite G] {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    pCore 2 (d.Star I) = ⊥ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS
  have hZI : d.Z ≤ I := hZS.trans (hP ▸ map_subtype_le (P : Subgroup I))
  let U := (d.UI I).subgroupOf I
  let f : I →* MulAut U := MulAut.conjNormal
  have hZP : d.Z.subgroupOf I ≤ centralizer (P : Set I) := by
    intro z hz p hp
    apply Subtype.ext
    exact d.Z_le_centralizer_S hz p (hP ▸ mem_map_of_mem I.subtype hp)
  have hr : pCore 2 f.range = ⊥ :=
    pCore_conjNormal_range_eq_bot_of_normalClosure P (d.Z.subgroupOf I) U
      (d.UI_subgroupOf_eq_normalClosure hZI) hZP
  have hk : localActionKernel d.Z I = f.ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact (QuotientGroup.ker_mk' _).symm.trans (d.starMap_ker hZI)
  let e : d.Star I ≃* f.range :=
    (QuotientGroup.congr _ _ (MulEquiv.refl I) (by simpa using hk)).trans
      (QuotientGroup.quotientKerEquivRange f)
  exact (map_eq_bot_iff_of_injective (pCore 2 (d.Star I)) e.injective).mp
    ((pCore_map_iso 2 e).trans hr)

/-- The binary representation is the actual conjugation action on `U_I`,
descended to the exact star quotient. -/
noncomputable def UIAction (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)] :
    Representation (ZMod 2) (d.Star I) (Additive ((d.UI I).subgroupOf I)) :=
  Representation.NormalElementaryQuotient.representation
    ((d.UI I).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (d.starMap_ker hZI)

/-- Faithfulness uses the centralizer denominator, rather than an arbitrary
abstract group identification. -/
theorem UIAction_faithful (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)] :
    Function.Injective (d.UIAction I hZI) :=
  Representation.NormalElementaryQuotient.representation_injective
    ((d.UI I).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (d.starMap_ker hZI)

/-- Compatibility with the original ambient conjugation. -/
theorem UIAction_apply (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]
    (i : I) (u : Additive ((d.UI I).subgroupOf I)) :
    (((d.UIAction I hZI (d.starMap I i) u).toMul : I) : G) =
      (i : G) * ((u.toMul : I) : G) * (i : G)⁻¹ :=
  congrArg I.subtype (Representation.NormalElementaryQuotient.representation_apply
    ((d.UI I).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (d.starMap_ker hZI) i u)

/-- The intrinsic and ambient realizations of `J(I)` agree. -/
theorem thompson_subgroupOf (I : Subgroup G) :
    (Stellmacher.elementaryAbelianMaxJ I).subgroupOf I =
      Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup I) := by
  have he := Stellmacher.elementaryAbelianMaxJ_map_injective I.subtype
    I.subtype_injective (⊤ : Subgroup I)
  rw [← MonoidHom.range_eq_map, range_subtype] at he
  rw [he]
  exact comap_map_eq_self_of_injective I.subtype_injective _

/-- The precise FF input from 15.3.11(11). -/
theorem UIAction_isFFModule [Finite G] (I : Subgroup G) (hZI : d.Z ≤ I)
    [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]
    (hJ : ¬ d.starImage I (Stellmacher.elementaryAbelianMaxJ I) ≤ d.starImage I d.M) :
    Representation.BinaryOffender.IsFFModule (d.UIAction I hZI) := by
  apply Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    ((d.UI I).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (d.starMap_ker hZI) (⊤ : Subgroup I) le_top
  intro hle
  apply hJ
  have hb : d.starImage I (Stellmacher.elementaryAbelianMaxJ I) = ⊥ := by
    change ((Stellmacher.elementaryAbelianMaxJ I).subgroupOf I).map (d.starMap I) = ⊥
    rw [thompson_subgroupOf]
    exact (Subgroup.map_eq_bot_iff _).mpr hle
  rw [hb]
  exact bot_le

end LocalData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
