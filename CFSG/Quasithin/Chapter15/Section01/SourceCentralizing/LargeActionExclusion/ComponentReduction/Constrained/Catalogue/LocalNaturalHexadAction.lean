module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadFullCore
public import Theory.Mathieu.M22.CentralCover.ElementaryHexadAction

/-!
# The six-letter action on the original full covered-hexad core

The original natural escape has an elementary full hexad core. The native
A₆ complement lifts through the same central two-cover, and the marked
augmentation-cover theorem then constructs a surjection from the even
six-letter module onto that entire core. The action equation retains the
lifted complement; the projection equation retains the original quotient
L → L/Z(L) → M₂₂ and its native natural coordinates.

The five-dimensional domain bounds the full core by 32. Its known order
16 |Z(L)| therefore bounds the original covering center by two. This is a
consequence, not a restriction imposed on the original source hypotheses.
The original-marker consumer retains the same G₁, M_Z, S, Q₁ and K.

The remaining plane-stabilizer transvection argument, covered-hexad
exclusion and general natural Borel containment remain open. Original
15.1.14 and whole-core A₆ reconstruction retain their existing producers.

Source: Aschbacher--Smith B.3.3 and I.2.2(6), printed pp.84 and 412;
the original 15.1.16--20 and 15.1.22 setup, printed pp.1092--1100.
-/

public section
open Subgroup Representation Representation.OneCohomology Sporadic.Mathieu
open scoped IsMulCommutative Pointwise

open Sporadic.Mathieu.M22CentralCover
open Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD.UniqueFactor ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem native_hexad_core {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22SetAction B).ker = pCore 2 (MulAction.stabilizer M22 B) := by
  let e := M22HexadCoordinates.stabilizerEquiv hB
  ext x
  rw [M22HexadCoordinates.kernel_iff hB,←pCore_map_iso 2 e]
  exact mem_map_iff_mem e.injective

/-- The full covered core has marked augmentation coordinates and its
original covering center has order at most two. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad_augmentation
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    V ≤ d.Q1 ∧ Nat.card (center d.L) ≤ 2 ∧
    ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B, ∃ hB : B ∈ m22Blocks,
      let J := preimage e (MulAction.stabilizer M22 B)
      let H := J.map d.L.subtype
      let f := localProjection e (MulAction.stabilizer M22 B)
      let R := ((m22SetAction B).ker).comap f
      d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
      (R.map J.subtype).map d.L.subtype = H.pCoreIn 2 ∧
      conjugateSpanBy (V ⊓ d.L) H = H.pCoreIn 2 ∧
      IsElementaryAbelian 2 (V ⊔ H.pCoreIn 2 : Subgroup G) ∧
      ∃ t : alternatingGroup (Fin 6) →* J,
        f.comp t = m22HexadSection hB ∧
        ∃ b : Multiplicative (BinaryPermutation.core (Fin 6)) →* R,
          Function.Surjective b ∧
          (∀ a v, b (Multiplicative.ofAdd
            (BinaryPermutation.coreRepresentation (Fin 6) a.val v.toAdd)) =
              (MulAut.conjNormal.comp t) a (b v)) ∧
          ∀ v, (m22HexadNaturalCoordinates hB
            (f.subgroupComap (m22SetAction B).ker (b v))).toAdd =
              BinaryPermutation.coreToNatural (Fin 6) v.toAdd := by
  obtain ⟨hVQ,e,B,hB,hMLH,hMZN,hgen,hAeq,hHQ,hE,hspan,hcentral⟩ :=
    s.localFamily_linearTwo_m22_hexad_full_core (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let J := preimage e (MulAction.stabilizer M22 B)
  let H := J.map d.L.subtype
  let f := localProjection e (MulAction.stabilizer M22 B)
  let R := ((m22SetAction B).ker).comap f
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  have hZ := (s.ordinary hL).center_two
  have hR : R = pCore 2 J := by
    change ((m22SetAction B).ker).comap (localProjection e (MulAction.stabilizer M22 B)) = _
    rw [native_hexad_core hB,localProjection_comap_twoCore e hZ]
  have hm : (R.map J.subtype).map d.L.subtype = H.pCoreIn 2 := by
    rw [hR]
    exact map_pCoreIn_of_injective 2 J d.L.subtype d.L.subtype_injective
  let i : R →* (V ⊔ H.pCoreIn 2 : Subgroup G) :=
    (d.L.subtype.comp (J.subtype.comp R.subtype)).codRestrict _
      (fun r => (show H.pCoreIn 2 ≤ V ⊔ H.pCoreIn 2 from le_sup_right)
        (hm ▸ mem_map_of_mem d.L.subtype (mem_map_of_mem J.subtype r.property)))
  let : IsElementaryAbelian 2 (V ⊔ H.pCoreIn 2 : Subgroup G) := hE
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_injective i (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (V ⊔ H.pCoreIn 2 : Subgroup G) => (z : G)) he)
  let : Group.IsPerfect J := hexadPreimage_isPerfect e hZ hB
  obtain ⟨t0,ht0⟩ := M22UniversalMultiplier.exists_hexadSection_lift
    (projection e) (projection_surjective e) (by rw [projection_ker])
    (by rw [projection_ker]; exact hZ) hB
  let t : alternatingGroup (Fin 6) →* J := t0.codRestrict J (fun a => by
    change projection e (t0 a) ∈ MulAction.stabilizer M22 B
    rw [show projection e (t0 a) = (m22HexadSection hB a).val from DFunLike.congr_fun ht0 a]
    exact (m22HexadSection hB a).property)
  have ht : f.comp t = m22HexadSection hB := by
    apply MonoidHom.ext
    intro a
    exact Subtype.ext (DFunLike.congr_fun ht0 a)
  have hc : f.ker ≤ center J := by
    rw [localProjection_ker]
    intro z hz
    exact mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp hz x))
  obtain ⟨b,hsur,heq,hproj⟩ := hexad_augmentation_surjection hB f
    (localProjection_surjective e _) hc t ht
  have hcard : Nat.card R ≤ 32 := by
    have hh := Nat.card_le_card_of_surjective b hsur
    have hn : Nat.card (Multiplicative (BinaryPermutation.core (Fin 6))) = 32 := by
      change Nat.card (BinaryPermutation.core (Fin 6)) = 32
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),BinaryPermutation.finrank_core]
      norm_num
    exact hh.trans_eq hn
  have hRc : Nat.card R = 16 * Nat.card (center d.L) := by
    rw [←card_map_of_injective (f := J.subtype) J.subtype_injective]
    change Nat.card (((m22SetAction B).ker).comap f |>.map J.subtype) = _
    have hr : R.map J.subtype = preimage e (m22HexadPointwiseKernel B) := by
      rw [hR,←preimage_twoCore e hZ,←native_hexad_core hB]
      rfl
    change Nat.card (R.map J.subtype) = _
    rw [hr,preimage_card,m22HexadPointwiseKernel_card hB]
  refine ⟨hVQ,by omega,e,B,hB,hMLH,hMZN,hgen,hm,hAeq,hE,t,ht,b,hsur,heq,hproj⟩
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original marker gives the full covered-core action over the literal
natural quotient and bounds its covering center by two. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad_augmentation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧
          V ≤ d.Q1 ∧ Nat.card (center d.L) ≤ 2 ∧
          ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B, ∃ hB : B ∈ m22Blocks,
            let J := preimage e (MulAction.stabilizer M22 B)
            let H := J.map d.L.subtype
            let f := localProjection e (MulAction.stabilizer M22 B)
            let R := ((m22SetAction B).ker).comap f
            d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
            (R.map J.subtype).map d.L.subtype = H.pCoreIn 2 ∧
            conjugateSpanBy (V ⊓ d.L) H = H.pCoreIn 2 ∧
            IsElementaryAbelian 2 (V ⊔ H.pCoreIn 2 : Subgroup G) ∧
            ∃ t : alternatingGroup (Fin 6) →* J,
              f.comp t = m22HexadSection hB ∧
              ∃ b : Multiplicative (BinaryPermutation.core (Fin 6)) →* R,
                Function.Surjective b ∧
                (∀ a v, b (Multiplicative.ofAdd
                  (BinaryPermutation.coreRepresentation (Fin 6) a.val v.toAdd)) =
                    (MulAut.conjNormal.comp t) a (b v)) ∧
                ∀ v, (m22HexadNaturalCoordinates hB
                  (f.subgroupComap (m22SetAction B).ker (b v))).toAdd =
                    BinaryPermutation.coreToNatural (Fin 6) v.toAdd := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_hexad_augmentation (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
