module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Core
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.LocalSylow
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.DiagonalCore
public import Theory.SpecificGroups.AlternatingFiveCore
/-!
# The two quotient-core bounds in the orthogonal lift

The image of C_H(i) contains the selected diagonal A₅ and lies in C_{H/U}(i*).
Restriction of the component action to its fixed diagonal puts the two-core
of every intermediate subgroup inside ⟨i*⟩. This proves the required bound
for the actual centralizer image, without asserting surjectivity onto the
quotient centralizer. The image of K₀UD is K₀*⟨i*⟩, so the same calculation
proves its bound. The upstream selected-component marking remains explicit.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010; the actual component
configuration is case (3) of 14.4.2, printed pp.1006–1007, and G.11.2(7).

The Sylow centralizer calculation is independent of these core bounds and
is not asserted by this module.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel
open Subgroup Theory.GroupTheory ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
abbrev A5 := alternatingGroup (Fin 5)
private instance : IsQuasisimple A5 where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The image of the actual joint centralizer lies in the quotient centralizer. -/
theorem centralizer_image_le (H : Subgroup G) (i : G) (hi : i ∈ H) :
    ((H ⊓ centralizer ({i} : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H)) ≤
    centralizer ({QuotientGroup.mk' (pCore 2 H) ⟨i,hi⟩} : Set (H ⧸ pCore 2 H)) := by
  rintro a ⟨b,hb,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [← map_mul, ← map_mul]
  apply congrArg (QuotientGroup.mk' (pCore 2 H))
  exact Subtype.ext (mem_centralizer_singleton_iff.mp hb.2)

/-- Both literal quotient cores are bounded by the selected involution.
The action is the faithful conjugation action on the two components, with
coordinates chosen using i; it is not a choice of action on U/Z(U). -/
theorem quotient_core_bounds
    (U : Subgroup G) (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hiz : i ∈ centralizer ({z} : Set G))
    (ρ : ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))) →*
      MulAut (A5 × A5))
    (hρ : Function.Injective ρ)
    (hiρ : ρ (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩) = swap)
    (hdiag : (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))).map ρ =
        diagonalInner.range) :
    let H := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 H)
    (((H ⊓ centralizer ({i} : Set G)).subgroupOf H).map q).pCoreIn 2 ≤
      (zpowers (⟨i,hiz⟩ : H)).map q ∧
    (((diagonalResidual H i ⊔ U ⊔ centralizerLift U z i).subgroupOf H).map q).pCoreIn 2 ≤
      (zpowers (⟨i,hiz⟩ : H)).map q := by
  let H := centralizer ({z} : Set G)
  let K := diagonalResidual H i
  let C := H ⊓ centralizer ({i} : Set G)
  let D := centralizerLift U z i
  let q := QuotientGroup.mk' (pCore 2 H)
  let iH : H := ⟨i,hiz⟩
  have hKC : K ≤ C := map_subtype_le (pResidual 2 C)
  have hUH : U ≤ H := hUcore ▸ pCoreIn_le 2 H
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hiU : i ∈ normalizer (U : Set G) := hHU hiz
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hBU : ⁅U,zpowers i⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  have hDle : D ≤ U ⊔ zpowers i :=
    sup_le (sup_le (hBU.trans le_sup_left) le_sup_right) (hzU.trans le_sup_left)
  have hUintr : U.subgroupOf H = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hUH]
    exact hUcore.symm
  have hUmap : (U.subgroupOf H).map q = ⊥ := by
    rw [hUintr, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hI : (zpowers i).subgroupOf H = zpowers iH := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr hiz), MonoidHom.map_zpowers]
    rfl
  have hDmap : (D.subgroupOf H).map q = zpowers (q iH) := by
    apply le_antisymm
    · have h := map_mono (f := q) (subgroupOf_mono H hDle)
      rw [subgroupOf_sup hUH (zpowers_le.mpr hiz), Subgroup.map_sup, hUmap, hI,
        MonoidHom.map_zpowers, bot_sup_eq] at h
      exact h
    · apply zpowers_le.mpr
      exact mem_map_of_mem q
        ((show zpowers i ≤ D from le_sup_right.trans le_sup_left) (mem_zpowers i))
  have hDH : D ≤ H := hDle.trans (sup_le hUH (zpowers_le.mpr hiz))
  have hCbar : (C.subgroupOf H).map q ≤ centralizer ({q iH} : Set (H ⧸ pCore 2 H)) :=
    centralizer_image_le H i hiz
  have hKbar : (K.subgroupOf H).map q ≤ (C.subgroupOf H).map q :=
    map_mono (subgroupOf_mono H hKC)
  have hJ : ((K ⊔ U ⊔ D).subgroupOf H).map q =
      (K.subgroupOf H).map q ⊔ zpowers (q iH) := by
    rw [subgroupOf_sup (sup_le (hKC.trans inf_le_left) hUH) hDH,
      subgroupOf_sup (hKC.trans inf_le_left) hUH, Subgroup.map_sup, Subgroup.map_sup, hUmap,
      sup_bot_eq, hDmap]
  have hcore (A : Subgroup (H ⧸ pCore 2 H))
      (hKA : (K.subgroupOf H).map q ≤ A)
      (hAC : A ≤ centralizer ({q iH} : Set (H ⧸ pCore 2 H))) :
      A.pCoreIn 2 ≤ (zpowers iH).map q := by
    rw [MonoidHom.map_zpowers]
    exact core_le_of_square_action 2 (alternatingGroup.center_eq_bot (by simp))
      alternatingGroup.five_twoCore_eq_bot ρ hρ (q iH) hiρ A hAC
      (hdiag ▸ map_mono (f := ρ) hKA)
  constructor
  · exact hcore _ hKbar hCbar
  · apply hcore
    · rw [hJ]; exact le_sup_left
    · rw [hJ]
      exact sup_le (hKbar.trans hCbar)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))

/-- Apply the proved quotient bounds to the literal two lift contracts.
No ambient core identity is an input. -/
theorem core_identities_of_components
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hiz : i ∈ centralizer ({z} : Set G))
    (hUcard : Nat.card U = 512)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32)
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (ρ : ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))) →*
      MulAut (A5 × A5))
    (hρ : Function.Injective ρ)
    (hiρ : ρ (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩) = swap)
    (hdiag : (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))).map ρ =
        diagonalInner.range) :
    (centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G)).pCoreIn 2 =
      centralizerLift U z i ∧
    (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U ⊔
      centralizerLift U z i).pCoreIn 2 = U ⊔ centralizerLift U z i := by
  have hHU : centralizer ({z} : Set G) ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact (centralizer ({z} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  obtain ⟨hC,hJ⟩ := quotient_core_bounds U z i hZ hUcore hiz ρ hρ hiρ hdiag
  exact ⟨centralizerLift_eq_joint_core_of_quotient U z i hZ hUcore (hHU hiz) hiz
    hUcard hD hA hAcard hmoved hC,
    core_join_lift_eq_residual_join_core_of_quotient U z i hZ hUcore (hHU hiz) hiz
      hD hmoved hJ⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel
