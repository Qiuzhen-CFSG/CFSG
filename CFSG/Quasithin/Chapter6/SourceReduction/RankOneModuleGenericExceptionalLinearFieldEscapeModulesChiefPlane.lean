module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefNatural
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesBinary
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.GroupTheory.PCoreRestriction

/-!
# The original four-plane and the quotient chief contribution

The cubic acts nontrivially on the actual four-plane, so orbit counting
makes its fixed index four. Local characteristic two puts the original
central involution, and hence the plane, in O₂(LT). Cubic commutators lie
in L, so the intersection with L retains this fixed index and lies in
O₂(L). Thus the original two-core contributes at least one cubic factor.

The literal PSL₂ quotient contributes log₄(2ⁿ) on T∩L, independently of
any module recognition. The Chapter 12 consumer combines these bounds
for n≥4 and applies the existing opposite-image chief-count identity.
Source: Aschbacher--Smith 5.1.21--23, printed pp.644--646,
refs/quasithin.pdf. The n=2 count and middle-layer fixedness remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- Add the kernel and quotient contributions for the original cubic. -/
theorem psl_cubic_sylow_length
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hC : Nat.card C = 3) (hCL : C ≤ L)
    (hCP : C ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G)) :
    conjugationCubicLength C ((T : Subgroup G) ⊓ L) =
      conjugationCubicLength C (L.pCoreIn 2) + Nat.log 4 (2 ^ n) := by
  let R := (T : Subgroup G) ⊓ L
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e := e₀.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hPR : (P : Subgroup L) = R.subgroupOf L := by
    rw [hP]
    ext x
    change (x : G) ∈ (T : Subgroup G) ↔ (x : G) ∈ (T : Subgroup G) ⊓ L
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hAP : C.subgroupOf L ≤ normalizer (P : Set L) := by
    change C.subgroupOf L ≤ normalizer ((P : Subgroup L) : Set L)
    rw [hPR]
    apply le_normalizer_iff.mpr
    intro a ha x hx
    have haC : (a : G) ∈ C := ha
    have hxR : (x : G) ∈ R := hx
    change (a : G) * (x : G) * (a : G)⁻¹ ∈ R
    exact (mem_normalizer_iff.mp (hCP haC) (x : G)).mp hxR
  have hc := CubicComparison.sl2_sylow_length q hq (hk.symm ▸ pCore_isPGroup) P
    (C.subgroupOf L) ((Nat.card_congr (subgroupOfEquivOfLe hCL).toEquiv).trans hC) hAP
  have hcore : (L.pCoreIn 2).subgroupOf L = pCore 2 L :=
    comap_map_eq_self_of_injective L.subtype_injective _
  rw [hPR,hk,← hcore,CubicComparison.length_subgroupOf C R L hCL inf_le_right,
    CubicComparison.length_subgroupOf C (L.pCoreIn 2) L hCL (pCoreIn_le 2 L),hF] at hc
  exact hc

/-- The actual moving four-plane contributes exactly one cubic factor. -/
theorem LocalData.plane_cubic_length (d : LocalData T H C z)
    (hC : Nat.card C = 3) : conjugationCubicLength C (plane C z) = 1 := by
  let P := plane C z
  have hCP : C ≤ normalizer (P : Set G) := le_normalizer_conjugateSpanBy _ _
  let := conjMulDistribMulActionOfLeNormalizer C P hCP
  have hc : FixedPoints.subgroup C P = (centralizer (C : Set G)).subgroupOf P := by
    ext x
    constructor
    · intro hx c hc
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hx ⟨c,hc⟩))
    · intro hx c
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx c c.property)
  have hthree : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hp : IsPGroup 2 P := d.g2.elementary.isPGroup
  have hi := FixedPoints.index_eq_four_pow_cubicLength hthree hp
  rw [← conjugationCubicLength_eq C P hCP,hc] at hi
  have hne : ¬ P ≤ centralizer (C : Set G) := by
    intro he
    obtain ⟨g,hg,hgn⟩ := d.exists_moving_cubic
    exact hgn ((le_centralizer_iff.mp (d.g2.point_le.trans he)).trans
      (Subgroup.centralizer_le_normalizer _) hg)
  have hpos : 0 < conjugationCubicLength C P := by
    by_contra hn
    have hz : conjugationCubicLength C P = 0 := by omega
    rw [hz,pow_zero] at hi
    exact hne (relIndex_eq_one.mp hi)
  have hle : conjugationCubicLength C P ≤ 1 := by
    have hh := Nat.le_of_dvd (Nat.card_pos (α := P))
      ((centralizer (C : Set G)).subgroupOf P).index_dvd_card
    have hl := Nat.log_mono_right (b := 4) hh
    change conjugationCubicLength C P ≤ Nat.log 4 (Nat.card P) at hl
    simpa only [show Nat.card P = 4 from d.plane_card, show Nat.log 4 4 = 1 from by decide] using hl
  exact le_antisymm hle hpos

/-- The plane supplies a noncentral cubic contribution inside O₂(L). -/
theorem LocalData.core_cubic_length_pos
    (d : LocalData T H C z) (hC : Nat.card C = 3) (hCL : C ≤ L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hchar : centralizer (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    1 ≤ conjugationCubicLength C (L.pCoreIn 2) := by
  let J := L ⊔ (T : Subgroup G)
  let P := plane C z
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hz := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp d.point_mem
  have hzQ : z ∈ J.pCoreIn 2 := by
    apply mem_map_of_mem J.subtype (x := ⟨z,mem_sup_right hz.1⟩)
    apply hchar
    intro q hq
    apply Subtype.ext
    exact hz.2.2 q (hQT (mem_map_of_mem J.subtype hq))
  have hJQ : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hPQ : P ≤ J.pCoreIn 2 :=
    conjugateSpanBy_le (zpowers_le.mpr hzQ) (hCL.trans (le_sup_left.trans hJQ))
  have hCP : C ≤ normalizer (P : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCPL : C ≤ normalizer (P ⊓ L : Set G) :=
    (le_inf hCP (hCL.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hPP : P ≤ normalizer (P ⊓ L : Set G) :=
    (le_inf P.le_normalizer (d.g2.V_le_T.trans hTL)).trans inf_normalizer_le_normalizer_inf
  let : ((P ⊓ L).subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hPP
  have hcomm : ⁅P,C⁆ ≤ P ⊓ L := le_inf
    (le_normalizer_iff_commutator_le_left.mp hCP)
    ((commutator_mono le_rfl hCL).trans
      (le_normalizer_iff_commutator_le_right.mp (d.g2.V_le_T.trans hTL)))
  have he := CubicComparison.length_eq_of_commutator_le C P (P ⊓ L)
    (IsPGroup.of_card (n := 1) (by simpa using hC))
    (T.isPGroup'.to_le d.g2.V_le_T) inf_le_left hCP hCPL hcomm
  have hlow := conjugationCubicLength_mono C
    ((le_inf inf_le_right (inf_le_left.trans hPQ)).trans
      (inf_pCoreIn_le_of_le 2 (show L ≤ J from le_sup_left)))
  rw [he,d.plane_cubic_length hC] at hlow
  exact hlow
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
