module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.InitialAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.OriginalData
public import Theory.ElementaryAbelian.Quotient

/-!
# Original offender geometry before descent

The earlier source action and the proved initial local structure supply the
original offender data on G_E, with the same Sylow, residual and marked tau.
The action-image comparison uses equality of the two literal kernels. The
marked product lifts through Q_E, which is already contained in C_G(E).
Neither a temporary-core identity nor any conclusion of 15.3.67 is used.

Source: Aschbacher--Smith, 15.3.66 and the first part of the proof of 15.3.67,
printed pp.1152--1153.
-/

@[expose] public section

open Subgroup Stellmacher OrthogonalFourBinary
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.PreDescentSource

open LocalStructure GoldschmidtCore.LocalRelations
open Descent.QuotientIdentification

variable {G : Type*} [Group G]

private theorem conjugation_image_elementary {V M S : Subgroup G}
    (d : NaturalAction V M) (hSM : S ≤ M)
    (hfour : IsKleinFour (actionImage d S)) :
    IsElementaryAbelian 2
      (V.normalizerMonoidHom.comp (inclusion (hSM.trans d.normalizes))).range := by
  let a := d.action.comp (inclusion hSM)
  let b := V.normalizerMonoidHom.comp (inclusion (hSM.trans d.normalizes))
  have hra : a.range = actionImage d S := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, hSM s.property⟩, s.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have hker : a.ker = b.ker := by
    ext x
    change (inclusion hSM x) ∈ d.action.ker ↔
      (inclusion (hSM.trans d.normalizes) x) ∈ V.normalizerMonoidHom.ker
    rw [action_ker d, V.normalizerMonoidHom_ker]
    rfl
  let : IsKleinFour (actionImage d S) := hfour
  let : IsElementaryAbelian 2 (actionImage d S) := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  let : IsElementaryAbelian 2 a.range := hra.symm ▸ inferInstance
  let e : a.range ≃* b.range := (QuotientGroup.quotientKerEquivRange a).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange b))
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

private theorem original_marked_product (Y T E : Subgroup G)
    (d : MarkedDecomposition Y T E) (hQC : lineQ E ≤ centralizer (E : Set G)) :
    (lineNormalizer E : Set G) =
      ((lineY Y E ⊔ zpowers d.tau : Subgroup G) : Set G) *
        (centralizer (E : Set G) : Set G) := by
  let A := lineY Y E ⊔ zpowers d.tau
  have hAN : A ≤ lineNormalizer E :=
    sup_le ((lineY_le Y E).trans inf_le_right) (zpowers_le.mpr d.tau_mem.2)
  let f := d.equiv.toMonoidHom.comp (quotientMap E)
  apply Set.Subset.antisymm
  · intro g hg
    let gN : lineNormalizer E := ⟨g, hg⟩
    have ha : ((f gN).1, (1 : centralizerImage E)) ∈
        (A.subgroupOf (lineNormalizer E)).map f := by
      rw [d.first_factor]
      exact ⟨mem_top _, rfl⟩
    obtain ⟨a, haA, ha⟩ := ha
    obtain ⟨c, hc⟩ := (restrictedQuotient E (centralizer (E : Set G))
      (Subgroup.centralizer_le_normalizer (E : Set G))).rangeRestrict_surjective (f gN).2
    let cN : lineNormalizer E := inclusion (Subgroup.centralizer_le_normalizer (E : Set G)) c
    have hfc : f cN = (1, (f gN).2) := by
      exact (d.centralizer_factor c).trans (congrArg (fun x => (1, x)) hc)
    have heq : f gN = f (a * cN) := by
      rw [map_mul, ha, hfc]
      ext <;> simp
    let k : lineNormalizer E := a⁻¹ * gN * cN⁻¹
    have hk : k ∈ pCore 2 (lineNormalizer E) := by
      apply (QuotientGroup.eq_one_iff k).mp
      apply d.equiv.injective
      change f k = d.equiv 1
      rw [map_one]
      dsimp [k]
      rw [map_mul, map_mul, map_inv, map_inv, heq, map_mul]
      group
    have hkQ : (k : G) ∈ lineQ E := mem_map_of_mem (lineNormalizer E).subtype hk
    refine ⟨(a : G), haA, (k : G) * (c : G),
      (centralizer (E : Set G)).mul_mem (hQC hkQ) c.property, ?_⟩
    change (a : G) * (((a : G)⁻¹ * g * (c : G)⁻¹) * c) = g
    group
  · rintro g ⟨a, ha, c, hc, rfl⟩
    exact (lineNormalizer E).mul_mem (hAN ha) ((Subgroup.centralizer_le_normalizer _) hc)

variable [Finite G] {T : Sylow 2 G} {M Mc P E : Subgroup G}
variable [IsElementaryAbelian 2 (localModule T M)]

/-- The original local structure constructs the exact input of the offender
argument, retaining its original marked quotient and tau. -/
noncomputable def originalData (s : EarlierData T M Mc P E) :
    Offenders.Replacement.Geometry.OriginalData
      (residualY M Mc) T (localModule T M) M E (linePc Mc E) := Classical.choice <| by
  let r := initialStructure s
  let V := localModule T M
  let Y := residualY M Mc
  have hTM : (T : Subgroup G) ≤ M := s.ordering.1.2
  have hYM : Y ≤ M := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hVTE : V ≤ lineT T E := le_inf s.module_le
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      ((centralizer_le s.line_le).trans (Subgroup.centralizer_le_normalizer _)))
  have hTEM : lineT T E ≤ M := inf_le_left.trans hTM
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [s.other_centralizer]
    exact le_centralizer_iff.mp (s.central_fixed.le.trans inf_le_right)
  have hcore : twoCoreAmbient Mc ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow Mc (T.subtype hTMc)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTMc] at h
  have hZE : centralInvolutions T ≤ E := by
    exact (Orthogonal.line_sylow_geometry_of_source s.natural T P E hTM
      s.plane_le s.plane_card s.plane_definite s.line_le s.line_card
      s.line_singular s.central_fixed s.selected s.selected_map).2.2.2.2.1
  have hCMc : centralizer (E : Set G) ≤ Mc :=
    centralizer_line_le_of_Z_le E (centralInvolutions T) Mc hZE s.other_centralizer
  have hQE : lineQ E ≤ lineT T E := by
    exact r.line_sylow_map ▸ pCoreIn_le_sylow (lineNormalizer E) r.line_sylow
  have hS : (lineY Y E ⊔ lineT T E : Subgroup G).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (E : Set G) := r.sylow_kernel
  exact ⟨{
    action := s.natural
    Y_le := hYM
    line_le := s.line_le
    line_card := s.line_card
    singular := s.line_singular
    residual_image := s.residual_image
    residual_kernel := s.residual_core_module
    residual_normal := (normal_subgroupOf_iff_le_normalizer
      ((lineY_le Y E).trans inf_le_right)).mp r.residual_normal
    module_le_sylow := hVTE
    sylow_le_M := hTEM
    sylow := r.line_sylow
    sylow_image := r.line_sylow_map
    core_le_kernel := r.paired.core_centralizes
    local_core := hS.le
    seed_commutator := r.paired.seed_commutator.le
    span_elementary := r.span_elementary
    span_le_sylow := r.span_le_core.trans hQE
    residual_span := r.span_commutator
    sylow_action_elementary := conjugation_image_elementary s.natural hTEM
      (Orthogonal.line_sylow_geometry_of_source s.natural T P E hTM
        s.plane_le s.plane_card s.plane_definite s.line_le s.line_card
        s.line_singular s.central_fixed s.selected s.selected_map).2.2.1
    marked := r.quotient
    product := original_marked_product Y T E r.quotient (r.paired.core_le.trans inf_le_right)
    Pc_le_sylow := linePc_le_lineT Mc T E hcore
    Pc_normalized := (le_inf hCMc (Subgroup.centralizer_le_normalizer _)).trans
      (linePc_normalizer Mc E)
    tau_mem_Pc := r.tau_mem
    tau_outside := by simpa only [← r.sylow_kernel] using r.tau_outside }⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.PreDescentSource
