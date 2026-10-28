module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.MatrixAccounting
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneRadicalCore
public import Theory.GroupTheory.NoncentralChiefRefinement.OneNoncentralLayer
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.OrthogonalActors
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Terminal accounting from the original local matrix image

The specified matrix image of L₀ determines its actual two-core, the
radical action and its quotient of order three. The same quotient supplies
the chief-count actor map. Normality of the original sections constructs
all six normal strata; no stratum or chief-series witness is supplied.
The exterior action also gives the critical intersection indices.

The final application feeds these constructions to the common-cubic
accounting theorem and the faithful H/O₂(H) exclusion on H_C/V_H. In
particular it assumes no elementary abelianness of H_C/V_H and no count
of six surrounding factors. The nine-factor tensor bound, original natural,
exterior and dual markings, the local matrix image and the remaining
critical-pair inputs stay explicit. Their construction remains with
qt-d-138-linear-four-source; earlier 13.8.27(b) is supplied by
qt-d-138-six-g2-source and final 13.8.1 assembly by qt-d-1381-source.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.31–32 and the terminal proof of 13.8.28, printed pp.965–966.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- The local matrix image identifies the actual radical, its kernel containment,
and its odd terminal quotient in the original ambient group. -/
theorem source_matrix_twoCore
    (H D QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (himage : (D.subgroupOf H).map π = PlaneRadical.cubicLocal) :
    ((D.pCoreIn 2).subgroupOf H).map π = PlaneRadical.radical ∧
      QH ⊓ D ≤ D.pCoreIn 2 ∧ Nat.card (D ⧸ pCore 2 D) = 3 ∧
      HasNoTwoChiefFactors (D ⧸ pCore 2 D) := by
  let πD := π.comp (inclusion hDH)
  have hk : πD.ker = QH.subgroupOf D := by
    ext x
    change inclusion hDH x ∈ π.ker ↔ (x:G) ∈ QH
    rw [hker]
    rfl
  have hp : IsPGroup 2 πD.ker := by rw [hk]; exact hQH.comap_subtype
  have hr : πD.range = PlaneRadical.cubicLocal := by
    rw [←himage]
    ext x
    constructor
    · rintro ⟨d,rfl⟩
      exact mem_map_of_mem π d.property
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
  obtain ⟨hm,hcard⟩ := PlaneRadical.lifted_twoCore πD hp hr
  have hmodel : ((D.pCoreIn 2).subgroupOf H).map π = (pCore 2 D).map πD := by
    ext x
    constructor
    · rintro ⟨r,⟨s,hs,he⟩,rfl⟩
      refine ⟨s,hs,?_⟩
      have hh : inclusion hDH s = r := Subtype.ext he
      change π (inclusion hDH s) = π r
      rw [hh]
    · rintro ⟨s,hs,rfl⟩
      exact ⟨inclusion hDH s,mem_map_of_mem D.subtype hs,rfl⟩
  refine ⟨hmodel.trans hm,?_,hcard,?_⟩
  · intro x hx
    have hcore : πD.ker ≤ pCore 2 D := le_sSup ⟨inferInstance,hp⟩
    have hxk : (⟨x,hx.2⟩ : D) ∈ πD.ker := by rw [hk]; exact hx.1
    exact mem_map_of_mem D.subtype (hcore hxk)
  · let : IsSimpleGroup (D ⧸ pCore 2 D) := isSimpleGroup_of_prime_card hcard
    apply noTwoChiefFactors_of_simple
    intro hp2
    have hh := hp2.card_eq_or_dvd
    rw [hcard] at hh
    norm_num at hh

/-- The actual local matrix image supplies the common cubic, radical and terminal quotient. -/
theorem source_linear_four_exclusion_of_local_matrix_image
    (H D UH V1 VH HC QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH) (hVC : VH ≤ HC)
    (hQHD : QH ≤ normalizer (D : Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (ddual : BinaryConjugationSection H QH HC ρ.dual)
    (ξ : Representation (ZMod 2) H Six)
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h v, ρ h v = Matrix.mulVec (π h).val v)
    (hexterior : ∀ h v, ξ h v = exteriorMap (π h).val v)
    (himage : (D.subgroupOf H).map π = PlaneRadical.cubicLocal)
    (hcentral : D ≤ centralizer (V1 : Set G))
    (hnine : ∀ t : ChiefSeries D, t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (Kc Uγ : Subgroup G) (hKcH : Kc ≤ H) (hDK : D ≤ Kc)
    [IsElementaryAbelian 2 Uγ]
    (hQHdef : QH = H.pCoreIn 2)
    (hU : Nat.card Uγ = 32) (houtside : ¬ Uγ ≤ QH)
    (hmeet : Uγ ⊓ UH ≠ ⊥) (hcommV : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH)
    (hcomm : ⁅HC,Uγ⁆ ≤ HC ⊓ Uγ) (hUγH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* BinaryLinear.OuterCyclic.LinearGroup 4)
    (hKc : IsPPerfect 2 Kc)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (Kc.subgroupOf H).subtype)) : False := by
  let Z : NormalNode D := ⟨V1.subgroupOf D,normal_subgroupOf_of_le_normalizer
    (hDH.trans ((normal_subgroupOf_iff_le_normalizer
      (d.kernel_le.trans d.section_le)).mp d.kernel_normal_actor))⟩
  let U : NormalNode D := ⟨UH.subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans d.normalized)⟩
  let V : NormalNode D := ⟨VH.subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans dexterior.normalized)⟩
  let C : NormalNode D := ⟨HC.subgroupOf D,normal_subgroupOf_of_le_normalizer
    (hDH.trans ((normal_subgroupOf_iff_le_normalizer
      (ddual.kernel_le.trans ddual.section_le)).mp ddual.kernel_normal_actor))⟩
  let Q : NormalNode D := ⟨QH.subgroupOf D,
    normal_subgroupOf_of_le_normalizer (hDH.trans ddual.normalized)⟩
  let R : NormalNode D := ⟨pCore 2 D,(show (pCore 2 D).Normal from inferInstance)⟩
  have hRcore : R.val = pCore 2 D := rfl
  have hZ : IsCentral ⊥ Z := by
    rw [isCentral_iff_commutator_le,commutator_le]
    intro a _ b hb
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (hcentral a.property (b:G) hb).symm)
  obtain ⟨hstar,hintersection⟩ := source_critical_indices_of_exterior_action
    H VH UH QH Uγ ξ π hker hexterior dexterior hUγH houtside hcommV
    (hVC.trans ddual.kernel_le) hU hmeet
  obtain ⟨hradical,hQR,hcard,hterm⟩ := source_matrix_twoCore H D QH hDH hQH π hker himage
  have hRdef : R.val = (D.pCoreIn 2).subgroupOf D := by
    rw [hRcore]
    exact (comap_map_eq_self_of_injective D.subtype_injective (pCore 2 D)).symm
  have hterminal : HasNoTwoChiefFactors (D ⧸ R.val) := by
    exact hterm.of_equiv (QuotientGroup.quotientMulEquivOfEq hRcore)
  have hcubic : cubicElement ∈ (D.subgroupOf H).map π := by
    rw [himage]
    exact (show zpowers cubicElement ≤ PlaneRadical.cubicLocal from le_sup_right)
      (mem_zpowers cubicElement)
  let f := QuotientGroup.mk' (pCore 2 D)
  have hp : IsPGroup 2 f.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hX : Nat.card (⊤ : Subgroup (D ⧸ pCore 2 D)) = 3 := by
    rw [card_top,hcard]
  have hq : IsPGroup 2 ((D ⧸ pCore 2 D) ⧸ (⊤ : Subgroup (D ⧸ pCore 2 D))) :=
    IsPGroup.of_card (n := 0) (by simp)
  exact source_linear_four_exclusion_of_matrix_sections
    H D UH V1 VH HC QH hDH hQH hVC hQHD ρ d ddual ξ dexterior
    π hker hnatural hexterior hcubic f (QuotientGroup.mk'_surjective _) hp ⊤ hX hq
    Z U V C Q R rfl rfl rfl rfl rfl hZ hterminal
    (D.pCoreIn 2) hRdef (isPGroup_pCoreIn 2 D) (pCoreIn_le 2 D) hQR hradical
    hnine Kc Uγ hKcH hDK hQHdef hU hstar hintersection hcomm hUγH hcover e hKc hKonto

end CFSG.Quasithin.Chapter13.Section08.LinearFour
