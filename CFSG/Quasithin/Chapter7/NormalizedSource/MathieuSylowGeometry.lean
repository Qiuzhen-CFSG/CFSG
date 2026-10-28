module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM24Equality
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrioNormalizers
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# Sylow placement and local geometry of Mathieu offender fixed spaces

A generator attaining the weak-closure minimum has the same corank as its
full relative normalizer, hence the full normalizer lies in the chosen Sylow
group. Native M24 has exactly two E64 subgroups in its common Sylow marking;
both are intrinsic cores and normal there. Transport through the actual
induced automizer therefore makes the offender fixed space Sylow invariant.

The full linear action on the marked three-space extends to its whole
normalizer with exactly the centralizer kernel. It also factors the normalizer
as the centralizer joined with the given full actor. Finally, a nonzero fixed
subgroup for the two-core generates the whole space under the previously
constructed residual action, forcing that two-core to centralize the space.
NonFFSourceMathieuM24Local supplies the original chosen-module applications.

Source: Aschbacher--Smith E.3.23--28, H.14.1(1), 8.2.5--6 and the M24 cocode
normalizer argument in 8.2.8, printed pp.236--237,396,716--719,
refs/quasithin.pdf. The canonical two-conjugate pair and component recognition
are separate source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSylow
open ChapterE

/-- A finite weak-closure minimum is attained by a full relative normalizer
inside the original Sylow subgroup. Corank additivity makes the minimizing
generator equal to its full normalizer. -/
theorem exists_offender_le_sylow {G : Type*} [Group G] [Finite G]
    {W : Subgroup G} [IsElementaryAbelian 2 W] {T : Sylow 2 G}
    (hT : HypothesisE322 W T) (hw : globalW W T ≠ ⊤) :
    ∃ g : G, IsWOffenderAt W T g ∧ offenderNormalizer W g ≤ T := by
  have he : globalW W T = (globalW W T).toNat := (ENat.natCast_toNat hw).symm
  obtain ⟨A, ⟨⟨g,hAW,hi⟩,hAT⟩,hAC⟩ := globalW_generator he
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let B := offenderNormalizer W g
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := offender_elementary_of_le (show B ≤ Wg from inf_le_left)
  have hAB : A ≤ B := le_inf hAW (hAT.trans hT.normalizes)
  have hBC : ¬ B ≤ centralizer (W : Set G) := fun hh => hAC (hAB.trans hh)
  have hcorA : subgroupCorank Wg A = (globalW W T).toNat := by
    change Nat.log 2 (A.relIndex Wg) = _
    rw [hi,Nat.log_pow Nat.one_lt_two]
  have hadd := offender_corank_add hAB (show B ≤ Wg from inf_le_left)
  have hbound := globalW_le_corank_of_noncentralizing_normalizes hT g
    (show B ≤ offenderNormalizer W g from le_rfl) hBC
  rw [he] at hbound
  have hbound' : (globalW W T).toNat ≤ subgroupCorank Wg B := by exact_mod_cast hbound
  have hzero : subgroupCorank B A = 0 := by omega
  have hBA : B = A := (subgroup_eq_of_corank_zero hAB hzero).symm
  refine ⟨g,⟨?_,?_⟩,hBA.le.trans hAT⟩
  · intro hc
    exact hAC (hAW.trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)))
  · rw [he]
    exact_mod_cast (show (globalW W T).toNat = subgroupCorank Wg B by omega)

/-- Every native E64 is normal in any two-subgroup containing it: conjugate
the two-subgroup into the common Sylow marking and use its two intrinsic cores. -/
theorem rank_six_normalized (P A : Subgroup M24) (hP : IsPGroup 2 P)
    (hAP : A ≤ P) (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 64) :
    P ≤ normalizer (A : Set M24) := by
  obtain ⟨S,hPS⟩ := hP.exists_le_sylow
  obtain ⟨c,hcS⟩ := MulAction.exists_smul_eq M24 S ElementaryFusion.standardSylow
  have hS : (S : Subgroup M24).map (MulAut.conj c).toMonoidHom =
      (ElementaryFusion.standardSylow : Subgroup M24) := congrArg Sylow.toSubgroup hcS
  have hP' : P.map (MulAut.conj c).toMonoidHom ≤
      (ElementaryFusion.standardSylow : Subgroup M24) := hS ▸ map_mono hPS
  let A' := A.map (MulAut.conj c).toMonoidHom
  have hAc : Nat.card A' = 64 := (card_map_of_injective (MulAut.conj c).injective).trans hc
  have hAs := (map_mono (f := (MulAut.conj c).toMonoidHom) hAP).trans hP'
  have hAn : (ElementaryFusion.standardSylow : Subgroup M24) ≤ normalizer (A' : Set M24) := by
    rcases (ElementaryFusion.elementary_card64_iff_eq_core A').mp
      ⟨IsElementaryAbelian.map _,hAc,hAs⟩ with ha | ha
    · rw [ha]
      exact ElementaryFusion.standardSylow_le_sextet.trans
        ((sextetStabilizer standardSextet).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 (sextetStabilizer standardSextet))))
    · rw [ha]
      exact ElementaryFusion.standardSylow_le_trio.trans
        ((PairOvergroups.trioStabilizer PairOvergroups.standardTrio).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _
            (pCore 2 (PairOvergroups.trioStabilizer PairOvergroups.standardTrio))))
  have hh := hP'.trans hAn
  rw [show A' = A.map (MulAut.conj c).toMonoidHom from rfl,
    ←map_equiv_normalizer_eq] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj c).injective).mp hh

/-- The E64 normality statement transfers through the literal induced
automizer and makes its fixed subgroup invariant under the original two-group. -/
theorem fixed_normalized {G : Type*} [Group G] [Finite G]
    (W A T : Subgroup G) [IsElementaryAbelian 2 W]
    (hT : IsPGroup 2 T) (hTW : T ≤ normalizer (W : Set G))
    (hAT : A ≤ T) (hA : IsElementaryAbelian 2 A)
    (a : Automizer W ≃* M24) (hr : rank (inducedAutomizer W A) = 6) :
    T ≤ normalizer ((W ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  let I := inducedAutomizer W A
  let P := inducedAutomizer W T
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary W A (hAT.trans hTW)
  have hIP : I ≤ P := map_mono (comap_mono hAT)
  have hP : IsPGroup 2 P := hT.comap_subtype.map _
  have hc : Nat.card I = 64 := by
    change rank I = 6 at hr
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
    have hn6 : n = 6 := by simpa only [rank,hn,Nat.log_pow Nat.one_lt_two] using hr
    rw [hn,hn6]
    rfl
  have hn := rank_six_normalized (P.map a.toMonoidHom) (I.map a.toMonoidHom)
    (hP.map _) (map_mono hIP) (IsElementaryAbelian.map _)
    ((card_map_of_injective a.injective).trans hc)
  rw [←map_equiv_normalizer_eq] at hn
  have hn' : P ≤ normalizer (I : Set (Automizer W)) :=
    (map_le_map_iff_of_injective a.injective).mp hn
  have hs := fixedSpace_stable_of_normalizes (automizerRepresentation W) hn'
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  have hp : W.normalizerMonoidHom.rangeRestrict ⟨t,hTW ht⟩ ∈ P :=
    mem_map_of_mem _ ht
  constructor
  · intro hx
    have hv := (mem_fixedSpace_inducedAutomizer W A (hAT.trans hTW)
      (Additive.ofMul ⟨x,hx.1⟩)).mpr hx.2
    have hh := (hs hp (Additive.ofMul ⟨x,hx.1⟩)).mpr hv
    exact ⟨(mem_normalizer_iff.mp (hTW ht) x).mp hx.1,
      (mem_fixedSpace_inducedAutomizer W A (hAT.trans hTW) _).mp hh⟩
  · intro hx
    have hxW := (mem_normalizer_iff.mp (hTW ht) x).mpr hx.1
    have hv := (mem_fixedSpace_inducedAutomizer W A (hAT.trans hTW)
      (automizerRepresentation W (W.normalizerMonoidHom.rangeRestrict ⟨t,hTW ht⟩)
        (Additive.ofMul ⟨x,hxW⟩))).mpr hx.2
    have hh := (hs hp (Additive.ofMul ⟨x,hxW⟩)).mp hv
    exact ⟨hxW,(mem_fixedSpace_inducedAutomizer W A (hAT.trans hTW) _).mp hh⟩

open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

/-- A full action on the three-space determines the whole normalizer modulo
its literal centralizer, with the original coordinates and projection. -/
theorem full_normalizer_action {G : Type*} [Group G]
    (U H : Subgroup G) [IsElementaryAbelian 2 U]
    (hHN : H ≤ normalizer (U : Set G))
    (e : U ≃* Multiplicative Vector) (π : H →* BinaryLinear.GL Vector)
    (hπ : Function.Surjective π)
    (hact : ∀ (l : H) (u : U),
      (e (U.normalizerMonoidHom ⟨l,hHN l.property⟩ u)).toAdd = π l (e u).toAdd) :
    ∃ qN : normalizer (U : Set G) →* BinaryLinear.GL Vector,
      Function.Surjective qN ∧ qN.comp (inclusion hHN) = π ∧
      qN.ker = (centralizer (U : Set G)).subgroupOf (normalizer (U : Set G)) ∧
      (∀ (n : normalizer (U : Set G)) (u : U),
        (e (U.normalizerMonoidHom n u)).toAdd = qN n (e u).toAdd) ∧
      normalizer (U : Set G) = centralizer (U : Set G) ⊔ H := by
  let fE : Additive U →+ Vector :=
    { toFun := fun u => (e u.toMul).toAdd
      map_zero' := e.map_one
      map_add' := fun x y => e.map_mul x.toMul y.toMul }
  let E : Additive U ≃ₗ[ZMod 2] Vector :=
    LinearEquiv.ofBijective (fE.toZModLinearMap 2) e.bijective
  let ρ : Representation (ZMod 2) (normalizer (U : Set G)) (Additive U) :=
    (automizerRepresentation U).comp U.normalizerMonoidHom.rangeRestrict
  let qN : normalizer (U : Set G) →* BinaryLinear.GL Vector :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector).toMonoidHom.comp
      ((Units.mapEquiv E.conjRingEquiv.toMulEquiv).toMonoidHom.comp ρ.asGroupHom)
  have hqN (n : normalizer (U : Set G)) (u : U) :
      qN n (e u).toAdd = (e (U.normalizerMonoidHom n u)).toAdd := by
    change E (ρ n (E.symm (E (Additive.ofMul u)))) = _
    rw [E.symm_apply_apply]
    rfl
  have hrestrict : qN.comp (inclusion hHN) = π := by
    apply MonoidHom.ext
    intro l
    apply LinearEquiv.ext
    intro v
    obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have huv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←huv]
    exact (hqN _ u).trans (hact l u)
  have hsur : Function.Surjective qN := by
    intro f
    obtain ⟨l,hl⟩ := hπ f
    exact ⟨inclusion hHN l, (congrArg (fun q : H →* BinaryLinear.GL Vector => q l) hrestrict).trans hl⟩
  have hker : qN.ker = (centralizer (U : Set G)).subgroupOf (normalizer (U : Set G)) := by
    ext n
    change qN n = 1 ↔ (n : G) ∈ centralizer (U : Set G)
    constructor
    · intro hn
      rw [mem_centralizer_iff]
      intro u hu
      have hh := hqN n ⟨u,hu⟩
      rw [hn] at hh
      have heq : (n : G) * u * (n : G)⁻¹ = u :=
        congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh.symm))
      exact ((mul_inv_eq_iff_eq_mul).mp heq).symm
    · intro hn
      apply LinearEquiv.ext
      intro v
      obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
      have huv : (e u).toAdd = v := congrArg Multiplicative.toAdd hu
      rw [←huv,hqN]
      change (e (U.normalizerMonoidHom n u)).toAdd = (e u).toAdd
      apply congrArg Multiplicative.toAdd
      apply congrArg e
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_iff.mp hn u u.property).symm
  refine ⟨qN,hsur,hrestrict,hker,fun n u => (hqN n u).symm,le_antisymm ?_ ?_⟩
  · intro n hn
    obtain ⟨l,hl⟩ := hπ (qN ⟨n,hn⟩)
    let lN := inclusion hHN l
    have heq : qN lN = qN ⟨n,hn⟩ :=
      (congrArg (fun q : H →* BinaryLinear.GL Vector => q l) hrestrict).trans hl
    have hk : (⟨n,hn⟩ : normalizer (U : Set G)) * lN⁻¹ ∈ qN.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,heq,mul_inv_cancel]
    rw [hker] at hk
    have hc : n * (l : G)⁻¹ ∈ centralizer (U : Set G) := hk
    simpa only [inv_mul_cancel_right] using
      (centralizer (U : Set G) ⊔ H).mul_mem (mem_sup_left hc) (mem_sup_right l.property)
  · exact sup_le (Subgroup.centralizer_le_normalizer _) hHN

/-- A nonzero two-space generated by every seed under an actor in its
normalizer is centralized by the full normalizer's two-core. -/
theorem core_centralizes_of_seed_generation {G : Type*} [Group G] [Finite G]
    (U R : Subgroup G) (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (hRN : R ≤ normalizer (U : Set G))
    (hspan : ∀ B : Subgroup G, B ≤ U → B ≠ ⊥ → conjugateSpanBy B R = U) :
    U ≤ (normalizer (U : Set G)).pCoreIn 2 ∧
      (normalizer (U : Set G)).pCoreIn 2 ≤ centralizer (U : Set G) := by
  let N := normalizer (U : Set G)
  let P := N.pCoreIn 2
  have hPN : P ≤ N := map_subtype_le _
  have hNP : N ≤ normalizer (P : Set G) :=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  let B := U ⊓ centralizer (P : Set G)
  have hBne : B ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups P U
    (isPGroup_pCoreIn 2 N) hU hPN hne
  have hNB : N ≤ normalizer (B : Set G) :=
    (le_inf le_rfl (hNP.trans (normalizer_le_normalizer_centralizer P))).trans
      inf_normalizer_le_normalizer_inf
  have hUB : U ≤ B := by
    rw [←hspan B inf_le_left hBne]
    exact conjugateSpanBy_le le_rfl (hRN.trans hNB)
  exact ⟨le_pCoreIn_of_normalizes hU U.le_normalizer le_rfl,
    le_centralizer_iff.mpr (hUB.trans inf_le_right)⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSylow
