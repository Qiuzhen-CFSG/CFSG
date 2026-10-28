module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CoreAction
public import Theory.SpecificGroups.Triality.ArmsParabolicPerfectAtTwo
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.NormalizedPerfect
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.SpecificGroups.PSL2.OrdinaryBorelGeometry

/-!
# The first residual and its Sylow image in the triality partner

Perfectness of the actual arms parabolic at q = 2 identifies the original
first endpoint H with its embedded O² residual. Its two-core quotient is
quasisimple and has elementary Sylow two-subgroups of order eight. Original
1.2.4 now supplies the unique normal C-component of Mc containing H.

The core equality from `CoreAction` makes the literal quotient inclusion
H/O₂(H) → Mc/O₂(Mc) injective. It carries the original Sylow image onto the
whole partner Sylow image, establishing the source E₈ assertion without
assuming normality of H in Mc.

Source: Aschbacher--Smith 14.2.16 and the opening of 14.2.18, pp.986--987.
The marked amalgam realization remains an explicit earlier input. Proving
that the containing component equals H, identifying the possible cubic
field extension, and recognizing the ambient group remain with the same
source-family owner. The literal 14.3.15 application is in
`TerminalSolvable/EightBorelResidual.lean`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

omit [Finite G] in
theorem first_perfect (r : MarkedTriality T M Mc H) : Group.IsPerfect H := by
  let := parabolic_arms_isPerfect_at_two (binaryParameters 1 Nat.zero_lt_one)
    rfl (by simp only [binaryParameters_q, pow_one])
  exact Group.IsPerfect.ofSurjective (f := r.left.symm.toMonoidHom) r.left.symm.surjective

theorem first_twoResidual_eq_top (r : MarkedTriality T M Mc H) : pResidual 2 H = ⊤ := by
  let := first_perfect r
  let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ (pResidual 2 H))

theorem first_residual_eq (r : MarkedTriality T M Mc H) : residual H = H := by
  rw [residual, first_twoResidual_eq_top r, ← MonoidHom.range_eq_map, range_subtype]

def firstResidualEquiv (r : MarkedTriality T M Mc H) : pResidual 2 H ≃* H :=
  (MulEquiv.subgroupCongr (first_twoResidual_eq_top r)).trans topEquiv

def firstResidualQuotientEquiv (r : MarkedTriality T M Mc H) :
    (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3 :=
  (QuotientGroup.congr _ _ (firstResidualEquiv r)
    (pCore_map_iso 2 (firstResidualEquiv r))).trans (firstQuotientEquiv r)

omit [Finite G] in
theorem first_quotient_quasisimple (r : MarkedTriality T M Mc H) :
    IsQuasisimple (H ⧸ pCore 2 H) := by
  let := first_perfect r
  let f := (firstQuotientEquiv r).trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
    Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
    ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 3 (by decide)]; decide)⟩
  exact IsQuasisimple.of_mulEquiv f.symm

/-- Every Sylow in the literal quotient is elementary of order eight. -/
theorem first_quotient_sylow (r : MarkedTriality T M Mc H)
    (S : Sylow 2 (H ⧸ pCore 2 H)) : IsElementaryAbelian 2 S ∧ Nat.card S = 8 := by
  let f := firstQuotientEquiv r
  let S' := S.mapSurjective (f := f.toMonoidHom) f.surjective
  let d : S ≃* S' := (S : Subgroup (H ⧸ pCore 2 H)).equivMapOfInjective
    f.toMonoidHom f.injective
  have he := Theory.PSL2.OrdinaryBorel.sylow_elementary S'
  let := he
  refine ⟨IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective, ?_⟩
  rw [Nat.card_congr d.toEquiv, Theory.PSL2.OrdinaryBorel.sylow_card]
  exact GaloisField.card 2 3 (by decide)

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- The first parabolic, now identified with its residual, lies in the actual
Sylow local family of Mc. -/
theorem source_first_mem_local_family (r : MarkedTriality T M Mc H) :
    H ∈ Chapter1.LIn Mc (T : Subgroup G) := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  let := first_perfect r
  let := first_quotient_quasisimple r
  refine Chapter1.mem_LIn_of_normalized_perfect
    (H := Mc) (S := (T : Subgroup G)) ?_ hHM (hH.1.1.2.trans H.le_normalizer) ?_
  · refine ⟨T.subtype (hH.1.1.2.trans hHM), ?_⟩
    exact map_subgroupOf_eq_of_le (hH.1.1.2.trans hHM)
  · intro he
    have hc := firstCore_card r
    rw [he, card_bot] at hc
    norm_num at hc

/-- Original 1.2.4 supplies a unique normal containing component in Mc.
The remaining non-enlargement argument must still identify it with H. -/
theorem source_first_normal_containing_component (r : MarkedTriality T M Mc H) :
    ∃! C : Subgroup Mc, C.IsCComponent ∧ H.subgroupOf Mc ≤ C ∧ C.Normal := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hTM := hH.1.1.2.trans hHM
  let S := T.subtype hTM
  have hL : H.subgroupOf Mc ∈ Chapter1.L Mc S :=
    (Chapter1.mem_LIn_iff_subgroupOf hTM hHM).mp
      (source_first_mem_local_family hG hempty hM hu hmany hcard e hH r)
  have hn : (S : Subgroup Mc) ≤ normalizer (H.subgroupOf Mc : Set Mc) := by
    rw [← subgroupOf_normalizer_eq hHM]
    exact comap_mono (hH.1.1.2.trans H.le_normalizer)
  have hmem : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  exact Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (ChapterE.Structure.sqtk_two_quotient (hG.twoLocal_sqtk hmem.1.1)
      (pCore 2 Mc) pCore_isPGroup) S hL hn


/-- Equality of the original embedded cores identifies the kernel of the
inclusion followed by the partner quotient. -/
theorem source_first_core_comap (r : MarkedTriality T M Mc H) :
    (pCore 2 Mc).comap (inclusion
      (source_first_le_partner hG hempty hM hu hmany hcard e hH)) = pCore 2 H := by
  rw [← source_partner_core_action_kernel hG hempty hM hu hmany hcard e hH r]
  exact source_first_core_action_kernel hG hempty hM hu hmany hcard e hH r

/-- The literal first-quotient inclusion in the original partner quotient. -/
def sourceFirstQuotientMap (r : MarkedTriality T M Mc H) :
    (H ⧸ pCore 2 H) →* (Mc ⧸ pCore 2 Mc) :=
  QuotientGroup.map _ _ (inclusion
    (source_first_le_partner hG hempty hM hu hmany hcard e hH))
      (source_first_core_comap hG hempty hM hu hmany hcard e hH r).ge

theorem sourceFirstQuotientMap_mk (r : MarkedTriality T M Mc H) (x : H) :
    sourceFirstQuotientMap hG hempty hM hu hmany hcard e hH r
      (QuotientGroup.mk' (pCore 2 H) x) =
        QuotientGroup.mk' (pCore 2 Mc) (inclusion
          (source_first_le_partner hG hempty hM hu hmany hcard e hH) x) := rfl

theorem sourceFirstQuotientMap_injective (r : MarkedTriality T M Mc H) :
    Function.Injective (sourceFirstQuotientMap hG hempty hM hu hmany hcard e hH r) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  apply (QuotientGroup.eq_one_iff y).mpr
  rw [← source_first_core_comap hG hempty hM hu hmany hcard e hH r]
  change inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) y ∈ pCore 2 Mc
  apply (QuotientGroup.eq_one_iff _).mp
  exact hx

/-- The original Sylow in Mc, with its actual image modulo O₂(Mc). -/
def sourcePartnerQuotientSylow : Sylow 2 (Mc ⧸ pCore 2 Mc) :=
  (T.subtype (hH.1.1.2.trans
    (source_first_le_partner hG hempty hM hu hmany hcard e hH))).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 Mc))

/-- The first quotient inclusion carries the source Sylow onto the whole
partner quotient Sylow, not merely into it. -/
theorem source_first_quotient_sylow_map (r : MarkedTriality T M Mc H) :
    (((T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)) :
      Sylow 2 (H ⧸ pCore 2 H)) : Subgroup (H ⧸ pCore 2 H)).map
        (sourceFirstQuotientMap hG hempty hM hu hmany hcard e hH r) =
      (sourcePartnerQuotientSylow hG hempty hM hu hmany hcard e hH :
        Subgroup (Mc ⧸ pCore 2 Mc)) := by
  change (((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map _ =
    ((T : Subgroup G).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) z,hz,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    let z : H := ⟨y,hH.1.1.2 hy⟩
    exact ⟨QuotientGroup.mk' (pCore 2 H) z,⟨z,hy,rfl⟩,rfl⟩

/-- The exact E₈ Sylow in Mc/O₂(Mc) required by source 14.2.18. -/
theorem source_partner_quotient_sylow (r : MarkedTriality T M Mc H) :
    IsElementaryAbelian 2 (sourcePartnerQuotientSylow hG hempty hM hu hmany hcard e hH) ∧
      Nat.card (sourcePartnerQuotientSylow hG hempty hM hu hmany hcard e hH) = 8 := by
  let S := (T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let f := sourceFirstQuotientMap hG hempty hM hu hmany hcard e hH r
  let d := ((S : Subgroup (H ⧸ pCore 2 H)).equivMapOfInjective f
    (sourceFirstQuotientMap_injective hG hempty hM hu hmany hcard e hH r)).trans
      (MulEquiv.subgroupCongr
        (source_first_quotient_sylow_map hG hempty hM hu hmany hcard e hH r))
  have hs := first_quotient_sylow r S
  let := hs.1
  exact ⟨IsElementaryAbelian.of_surjective d.toMonoidHom d.surjective,
    (Nat.card_congr d.toEquiv).symm.trans hs.2⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
