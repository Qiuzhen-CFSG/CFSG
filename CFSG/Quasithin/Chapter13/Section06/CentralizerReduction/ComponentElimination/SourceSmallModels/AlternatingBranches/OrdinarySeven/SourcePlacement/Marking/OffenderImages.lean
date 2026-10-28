module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.OffenderImages.StableFamily

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Families

/-!
# Maximal elementary images in the ordinary A₇ plus action

The internal subgroup W_K is normal in the actual plus actor, and plusMk has
exactly its internal centralizer as kernel. The Sylow witness from Y_z and the
nontrivial Thompson image feed the abstract stable-family theorem. Transport
through the actor inclusion identifies the resulting image with the original
J(Tᵥ)⁺. B.3.2(4) then conjugates it to the three literal transpositions.

The final adapter chooses the faithful action in the actual ordinary-block
coordinates. The fixed-codimension comparison with its natural module remains
an explicit independent input; this module does not claim that comparison or
the final source marking without it. Its producer is the ModuleComparison task,
and the parent Marking module retains source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.7–9,
B.3.2(4), and Lemma 13.6.22, printed pp.76–77, 83–84, and 932 (PDF p.949).
-/

@[expose] public section
open Subgroup Equiv Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
variable {G : Type*} [Group G]

/-- The literal internal W_K is elementary abelian whenever the ambient W_K is. -/
instance internalWK_elementary (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)] :
    IsElementaryAbelian 2 ((WK K L T z v).subgroupOf (plusActor K L T v)) where
  toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative _ _
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
    Subtype.ext (Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (A := WK K L T z v) x x.property)))

/-- The plus actor normalizes its literal internal W_K. -/
theorem internalWK_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    ((WK K L T z v).subgroupOf (plusActor K L T v)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  exact (mem_normalizer_iff.mp
    (plusActor_normalizes_WK K L T z v hL hz g.property) n.val).mp hn

/-- The plus projection kills exactly the centralizer of the internal W_K. -/
theorem plusMk_internal_kernel (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hWT : WK K L T z v ≤ Tv T v) :
    (plusMk K L T z v hL hz).ker =
      centralizer ((WK K L T z v).subgroupOf (plusActor K L T v) :
        Set (plusActor K L T v)) := by
  rw [plusMk_ker]
  ext x
  change (x.val ∈ centralizer (WK K L T z v : Set G)) ↔ _
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx w hw
    exact Subtype.ext (hx w.val hw)
  · intro hx w hw
    exact congrArg Subtype.val (hx ⟨w, (show Tv T v ≤ plusActor K L T v from le_sup_right) (hWT hw)⟩ hw)

/-- The genuine centralizer-quotient representation on the internal W_K. -/
noncomputable def plusInternalRepresentation (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) :
    Representation (ZMod 2) (Gplus K L T z v hL hz)
      (Additive ((WK K L T z v).subgroupOf (plusActor K L T v))) := by
  let := internalWK_normal K L T z v hL hz
  exact NormalElementaryQuotient.representation _ (plusMk K L T z v hL hz)
    (plusMk_surjective K L T z v hL hz) (plusMk_internal_kernel K L T z v hL hz hWT)

/-- The subgroup inclusion preserves the maximal-elementary Thompson subgroup. -/
theorem internal_thompson (K L T : Subgroup G) (v : G) :
    elementaryAbelianMaxJ ((Tv T v).subgroupOf (plusActor K L T v)) =
      (elementaryAbelianMaxJ (Tv T v)).subgroupOf (plusActor K L T v) := by
  let H := plusActor K L T v
  have hTH : Tv T v ≤ H := le_sup_right
  have hJH : elementaryAbelianMaxJ (Tv T v) ≤ H :=
    (sSup_le fun _ hA => hA.1).trans hTH
  apply map_injective H.subtype_injective
  rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le hJH]

variable [Finite G]

/-- Apply Sylow localization to the source plus actor, retaining the module
comparison explicitly and identifying both literal subgroup images. -/
theorem plus_exists_stable_image_family
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) (hφ : Function.Injective φ)
    (hAlt : (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7))
    (hc : ∀ A, fixedCodim (plusInternalRepresentation K L T z v hL hz hWT) A =
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ)) :
    Function.Surjective φ ∧
      ∃ (P : Set (Subgroup (Perm (Fin 7)))) (Rbar : Sylow 2 (Perm (Fin 7))),
        P = permutationOffenderImages
          ((Tv T v).subgroupOf (plusActor K L T v))
          ((WK K L T z v).subgroupOf (plusActor K L T v))
          (plusMk K L T z v hL hz) φ ∧
        IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P ∧
        (Rbar : Subgroup _) = (plusImage K L T z v hL hz (Tv T v)).map φ ∧
        (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))).map φ =
          generatedBy P (Rbar : Subgroup _) := by
  let H := plusActor K L T v
  let V := (WK K L T z v).subgroupOf H
  let q := plusMk K L T z v hL hz
  let := internalWK_normal K L T z v hL hz
  have hs := hY.1.2.2.1
  rw [← plusActor_eq K L T v hn hLv] at hs
  obtain ⟨R, hR⟩ := hs
  have hRi : (R : Subgroup H) = (Tv T v).subgroupOf H := by
    rw [← hR]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hj : (elementaryAbelianMaxJ (R : Subgroup H)).map q =
      plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) := by
    rw [hRi, internal_thompson]
    rfl
  have hVR : V ≤ R := by
    rw [hRi]
    exact comap_mono hWT
  have hJ : (elementaryAbelianMaxJ (R : Subgroup H)).map q ≠ ⊥ := by
    rw [hj]
    exact thompson_image_ne_bot K L T z v hL hz hn hY
  obtain ⟨hsur, P, Rbar, hP, hstable, hbar, hgen⟩ :=
    exists_stable_sylow_image_family V R hVR q
      (plusMk_surjective K L T z v hL hz) (plusMk_internal_kernel K L T z v hL hz hWT)
      φ hφ (hAlt ▸ (plusImage K L T z v hL hz K).map_le_range φ) hJ hc
  refine ⟨hsur, P, Rbar, ?_, hstable, ?_, ?_⟩
  · rw [hP, hRi]
  · rw [hbar, hRi]
    rfl
  · rw [← map_map, hj] at hgen
    exact hgen

/-- The actual Thompson plus image is conjugate to the three transpositions,
conditional only on the indicated module comparison and earlier source inputs. -/
theorem plus_exists_conjugated_marking
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) (hφ : Function.Injective φ)
    (hAlt : (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7))
    (hc : ∀ A, fixedCodim (plusInternalRepresentation K L T z v hL hz hWT) A =
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ)) :
    ∃ g : Perm (Fin 7),
      (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))).map
        ((MulAut.conj g).toMonoidHom.comp φ) = threeTranspositions := by
  obtain ⟨_, P, Rbar, _, hs, _, hgen⟩ :=
    plus_exists_stable_image_family K L T z v hL hz hn hLv hY hWT φ hφ hAlt hc
  obtain ⟨g, hg⟩ := exists_generatedBy_marking hs Rbar
  exact ⟨g, by rw [← map_map, hgen]; exact hg⟩

/-- Choose the source action in the actual ordinary-block coordinates. Once its
module comparison is supplied, the literal Thompson image has the three-swap
marking. The comparison remains the independent module owner's obligation. -/
theorem ordinary_action_with_conditional_marking
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hblock : ChapterC.IsAlternatingBlock K 7)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) :
    ∃ φ : Gplus K L T z v hL hz →* Perm (Fin 7),
      Function.Injective φ ∧
      (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7) ∧
      (∀ k : K, φ (plusMk K L T z v hL hz
        ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
          (blockProjection K (ordinaryQuotientEquiv K hblock) k : Perm (Fin 7))) ∧
      ((∀ A, fixedCodim (plusInternalRepresentation K L T z v hL hz hWT) A =
          fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ)) →
        ∃ g : Perm (Fin 7),
          (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))).map
            ((MulAut.conj g).toMonoidHom.comp φ) = threeTranspositions) := by
  obtain ⟨φ, hφ, hAlt, hcompat⟩ :=
    ordinary_action_exists K L T z v hL hz hn hLv hY hR hblock
  exact ⟨φ, hφ, hAlt, hcompat, fun hc =>
    plus_exists_conjugated_marking K L T z v hL hz hn hLv hY hWT φ hφ hAlt hc⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
