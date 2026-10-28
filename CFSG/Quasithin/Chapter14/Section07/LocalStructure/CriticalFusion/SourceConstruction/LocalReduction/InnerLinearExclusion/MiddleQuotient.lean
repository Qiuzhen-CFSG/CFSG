module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SevenNatural
public import Theory.GroupTheory.NormalSymmetricThreeSupplement
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SymmetricThreePair

/-!
# The actual middle quotient and its rank-two parabolics

The normal closure R of the original point two-core in the plane normalizer
lies in the plane parabolic. Point-core movement makes R/O₂(R) an actual
S₃ and gives RT=P. In the middle vertex D=H₂P, R is normal and H₂ is a
proper supplement with its own S₃ quotient. The normal-supplement theorem
therefore identifies D/O₂(D) with S₃ × S₃. Its parabolic classification
identifies the two literal subgroups H₂ and P, including the full lattice
condition needed by I.5. No normality in the ambient group is assumed.

These proofs use only Structural1222At at the original G,T. The source
movement premise 14.7.4(1), derived from earlier 14.5.21(2), is explicit
here; the selected large-component application discharges it separately.
The remaining I.5 assembly and the small-component exclusion are not
asserted by this module.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.4(1–2) and 14.7.11,
printed pp.1043,1045–1046.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Chapter12.Section08 CriticalFusion.Source Chapter12.Section09.NaturalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original full flag has chamber T, with only same-G,T structure. -/
theorem plane_parabolic_inf_point_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    F.P L ⊓ F.H = (T : Subgroup G) := by
  let := h.chosen.elementary
  let A := F.P L ⊓ F.H
  let j := inclusion (show A ≤ L ⊔ (T : Subgroup G) from inf_le_left.trans inf_le_left)
  let f := (F.binarySeedAction L h.chosen.normalizes).comp j
  have hp : IsPGroup 2 (F.binaryFullFlag.comap f) :=
    (F.binaryFullFlag_isPGroup.comap_of_ker_isPGroup
      (F.binarySeedAction L h.chosen.normalizes)
      (F.binarySeedAction_ker_isPGroup L h.chosen.normalizes (h.centralizer_LT_at structural))).comap_of_injective
        j (inclusion_injective _)
  have he : F.binaryFullFlag.comap f = ⊤ := by
    apply top_unique
    intro x _ i v
    have hxi : (x : G) ∈ F.Gi i := by
      by_cases hi : i < 3
      · by_cases hi0 : i = 0
        · subst i
          have hz : F.Vi 0 = ⊥ := card_eq_one.mp (by simpa using F.card 0 (by decide))
          change (x : G) ∈ normalizer (F.Vi 0 : Set G)
          rw [hz,normalizer_eq_top]
          trivial
        · by_cases hi1 : i = 1
          · subst i
            exact x.property.2
          · have hi2 : i = 2 := by omega
            subst i
            exact (F.P_le_G₂ (by decide) L h.chosen.normalizes) x.property.1
      · have hv : F.Vi i = V := le_antisymm (F.le_seed i)
          (F.last.ge.trans (F.monotone (by omega)))
        change (x : G) ∈ normalizer (F.Vi i : Set G)
        rw [hv]
        exact F.P_le_seed_normalizer L h.chosen.normalizes x.property.1
    exact (mem_normalizer_iff.mp hxi (v : G)).symm
  have hA : IsPGroup 2 A := (he ▸ hp).of_equiv Subgroup.topEquiv
  exact T.is_maximal' hA (le_inf (F.binary_sylow_le_P L) (F.invariant 1))


/-- Movement of the original point core makes its plane normal closure supplement
T in the original plane parabolic. -/
theorem plane_core_closure_sup_sylow_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥) :
    planeCoreClosure F ⊔ (T : Subgroup G) = F.P L := by
  let := h.chosen.elementary
  let P := F.P L
  let R := planeCoreClosure F
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hh hx
    exact hy
  have hcore : P.pCoreIn 2 = P ⊓ centralizer (F.Vi 2 : Set G) :=
    (F.binary_parabolic_core (by decide) L h.chosen.normalizes
      (h.full_LT_action_at structural) (h.centralizer_LT_at structural)).1.symm
  have hout : ¬ F.H.pCoreIn 2 ≤ P.pCoreIn 2 := by
    intro hc
    apply hm
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans (hcore.le.trans inf_le_right))
  let f := F.binaryPermutationAction (by decide) L h.chosen.normalizes
  have hf : Function.Surjective f := F.binaryPermutationAction_surjective (by decide)
    L h.chosen.normalizes (h.full_LT_action_at structural)
  have hk : f.ker = pCore 2 P :=
    (F.binaryPermutationAction_ker (by decide) L h.chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L h.chosen.normalizes
        (h.full_LT_action_at structural) (h.centralizer_LT_at structural))
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hgen : R ⊔ P.pCoreIn 2 = P := by
    rw [show R = conjugateSpanBy (F.H.pCoreIn 2) P from planeCoreClosure_eq_parabolic_span h F]
    exact (core_hyperplane_and_generation P (F.H.pCoreIn 2)
      (hQT.trans (F.binary_sylow_le_P L)) (isPGroup_pCoreIn 2 F.H) hout e).2
  have hPT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (F.binary_sylow_le_P L))
    change P.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P).map P.subtype at hh
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from F.binary_sylow_le_P L)] at hh
    exact hh
  exact le_antisymm (sup_le (planeCoreClosure_le_parabolic h F) (F.binary_sylow_le_P L))
    (hgen.ge.trans (sup_le_sup_left hPT R))

/-- The actual middle vertex has quotient S₃ × S₃, and its two actual
parabolics form the line residue. Only the earlier point-core movement is
retained: normality, generation, quotient transport and the parabolics are proved. -/
theorem middle_quotient_and_parabolics_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (H₂ : Subgroup G) (h₂H : H₂ ≤ F.H) (hT₂ : (T : Subgroup G) ≤ H₂)
    (h₂plane : H₂ ≤ F.Gi 2) (e₂ : HStar H₂ ≃* Equiv.Perm (Fin 3)) :
    Nonempty (HStar (H₂ ⊔ F.P L) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      RankTwoParabolics (H₂ ⊔ F.P L : Subgroup G) ((T : Subgroup G).subgroupOf (H₂ ⊔ F.P L))
        (H₂.subgroupOf (H₂ ⊔ F.P L)) ((F.P L).subgroupOf (H₂ ⊔ F.P L)) := by
  let D := H₂ ⊔ F.P L
  let R := planeCoreClosure F
  have hPD : F.P L ≤ D := le_sup_right
  have h₂D : H₂ ≤ D := le_sup_left
  have hRD : R ≤ D := (planeCoreClosure_le_parabolic h F).trans hPD
  have hTD : (T : Subgroup G) ≤ D := hT₂.trans h₂D
  have hDplane : D ≤ F.Gi 2 :=
    sup_le h₂plane (F.P_le_G₂ (by decide) L h.chosen.normalizes)
  have hRn : D ≤ normalizer (R : Set G) := by
    exact hDplane.trans (le_normalizer_conjugateSpanBy _ _)
  let : (R.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hRD).mpr hRn
  have hRT : R ⊔ (T : Subgroup G) = F.P L := plane_core_closure_sup_sylow_at h structural hm
  have hgen : R ⊔ H₂ = D := by
    calc
      R ⊔ H₂ = (R ⊔ (T : Subgroup G)) ⊔ H₂ := by
        rw [sup_assoc,sup_eq_right.mpr hT₂]
      _ = D := by rw [hRT,sup_comm]
  have hgenD : R.subgroupOf D ⊔ H₂.subgroupOf D = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRD,map_subgroupOf_eq_of_le h₂D,
      ←MonoidHom.range_eq_map,range_subtype,hgen]
  obtain ⟨_,⟨eR⟩⟩ := planeCoreClosure_quotient_at h structural hm
  let cR := subgroupOfEquivOfLe hRD
  let aR := (QuotientGroup.congr _ _ cR (pCore_map_iso 2 cR)).trans eR
  let c₂ := subgroupOfEquivOfLe h₂D
  let a₂ := (QuotientGroup.congr _ _ c₂ (pCore_map_iso 2 c₂)).trans e₂
  have h₂top : H₂.subgroupOf D ≠ ⊤ := by
    intro he
    have hDH : D ≤ F.H := by
      have hh := congrArg (map D.subtype) he
      rw [map_subgroupOf_eq_of_le h₂D,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh ▸ h₂H
    have hPT : F.P L ≤ (T : Subgroup G) :=
      (le_inf le_rfl (hPD.trans hDH)).trans_eq (plane_parabolic_inf_point_at h structural)
    have hRP : IsPGroup 2 R := T.isPGroup'.to_le ((planeCoreClosure_le_parabolic h F).trans hPT)
    have hs3 : IsPGroup 2 (Equiv.Perm (Fin 3)) := (hRP.to_quotient _).of_equiv eR
    obtain ⟨n,hn⟩ := hs3.exists_card_eq
    have hd : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [hn] at hd
    exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  obtain ⟨eD⟩ := NormalSymmetricThree.quotient_pair_of_normal_supplement
    (R.subgroupOf D) (H₂.subgroupOf D) aR a₂ (T.subtype hTD)
    (subgroupOf_mono D hT₂) h₂top hgenD
  refine ⟨⟨eD⟩,?_⟩
  have hg := RankTwoParabolics.of_normal_symmetricThree_supplement eD
    (R.subgroupOf D) (H₂.subgroupOf D) aR a₂ (T.subtype hTD)
    (subgroupOf_mono D hT₂) h₂top hgenD
  have he : R.subgroupOf D ⊔ (T : Subgroup G).subgroupOf D = (F.P L).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRD,map_subgroupOf_eq_of_le hTD,
      map_subgroupOf_eq_of_le hPD,hRT]
  change RankTwoParabolics D ((T : Subgroup G).subgroupOf D) (H₂.subgroupOf D)
    (R.subgroupOf D ⊔ (T : Subgroup G).subgroupOf D) at hg
  rwa [he] at hg

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
