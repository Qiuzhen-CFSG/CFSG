module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LocalOvergroups

/-!
# Cubic containment inside the original solvable locals

The cubic completion and Heisenberg norm argument require only that the
selected subgroup normalize L₁. In a solvable J in H_z, the proved equality
O₂(J) O₂(P) = T replaces normality of L₁ in the full point normalizer.
The cubic actor normalizes both cores, hence T, contradicting its literal
S₃ quotient. Thus every such actor in J is contained in N_G(L).

The F.8 point-core obstruction supplies the S₃ quotient of every escaping
cubic actor. The final application discharges relative normalization for
every cubic sublift of the actual normal elementary-nine or Heisenberg lift.
It retains the original models and exact quotient kernels. The terminal solvable exclusions remain required.

Source: Aschbacher–Smith, 14.5.3(2), pp.1013–1017, and 14.7.27–29,
pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Inside the point normalizer, an actor preserving both L₁ and T lies
in the seed normalizer: otherwise R₁ would be normal in an escaping local,
contrary to the original F.8 core obstruction. -/
theorem local_point_sylow_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G))
    (hYT : Y ≤ normalizer (T : Set G)) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let J := B ⊔ Y
  have hBJ : B ≤ J := le_sup_left
  have hJH : J ≤ F.H := sup_le
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)) hYH
  have hc : Nat.card (F.Vi 1) = 2 := F.card 1 (by decide)
  have hpoint : F.Vi 1 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using hc))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBJ))) hJH
  have hcore : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz := le_bot_iff.mp (he ▸ hpoint)
    rw [hz,card_bot] at hc
    omega
  have hJ : J ∈ F.Hz L (normalizer (L : Set G)) :=
    ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hBJ (mem_sup_left ha))
      (fun ha => hBJ (mem_sup_right ha))⟩,hJH,fun hh => hout (le_sup_right.trans hh)⟩
  have hYB : Y ≤ normalizer (B : Set G) :=
    (le_inf hYL hYT).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJR : J ≤ normalizer (F.Ri L 1 : Set G) :=
    (sup_le B.le_normalizer hYB).trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  exact point_core_not_le_local_core h hab structural J hJ
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B)
      ((pCoreIn_le 2 B).trans hBJ) hJR)

/-- An escaping cubic lift normalizing the point has the required literal S₃
Sylow quotient. The original core obstruction rules out trivial Sylow action. -/
theorem local_point_normalized_cubic_sylow_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G))
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hout : ¬ Y ≤ normalizer (L : Set G)) :
    Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  apply cubic_sylow_join_symmetricThree T Y hYT hc
  intro hm
  have hcore : Y.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 Y).le_sylow_of_normalized T
      (hYT.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
  exact hout (local_point_sylow_normalizer_le h hab structural Y hYH hYL
    (le_normalizer_iff_commutator_le_right.mpr (hm.trans hcore)))

/-- Source cubic containment with normalization only by the selected actor
and the original solvable-local hypotheses. -/
private theorem local_solvable_symmetricThree_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (Y : Subgroup G) (hYJ : Y ≤ J)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  have hYH : Y ≤ F.H := hYJ.trans hJ.2.1
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hYP : Y ≤ normalizer ((F.P L).pCoreIn 2 : Set G) := by
    rw [(cubic_generated_equal_two_cores_of_normalizes_point h hab structural previous faithful
      Y hYH hYL hYp hYT hout he).1]
    exact (show Y ≤ D from le_sup_left.trans le_sup_right).trans
      (D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  have hYJcore : Y ≤ normalizer (J.pCoreIn 2 : Set G) :=
    hYJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hYTnorm : Y ≤ normalizer (T : Set G) := by
    change Y ≤ normalizer ((T : Subgroup G) : Set G)
    rw [←local_solvable_core_plane_core_generate_sylow h hab structural previous faithful J hJ hs]
    exact (le_inf hYJcore hYP).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let B := Y ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ B from le_sup_right)
  have hBnorm : B ≤ normalizer (T : Set G) := sup_le hYTnorm (T : Subgroup G).le_normalizer
  have hSnorm : (S : Subgroup B).Normal := normal_subgroupOf_of_le_normalizer hBnorm
  have htop : (S : Subgroup B) = ⊤ := by
    rw [←SymmetricThreeTwoCore.sylow_self_normalizing he.some S]
    exact normalizer_eq_top_iff.mpr hSnorm
  have hi := SymmetricThreeTwoCore.sylow_index_three he.some S
  rw [htop,index_top] at hi
  omega

/-- Every T-invariant two-perfect cubic lift in a solvable local normalizing
L₁ lies in M. Its S₃ overgroup quotient is proved, not assumed. -/
theorem local_solvable_cubic_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (Y : Subgroup G) (hYJ : Y ≤ J)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  have he := local_point_normalized_cubic_sylow_quotient h hab structural Y
    (hYJ.trans hJ.2.1) hYL hYT hc hout
  exact hout (local_solvable_symmetricThree_containment h hab structural previous faithful
    J hJ hs Y hYJ hYL hYp hYT he)

/-- Every normalized cubic sublift of the original selected normal three-lift
is contained in the seed normalizer. The actor's
point normalization is derived from the actual lift and its marked models. -/
theorem local_minimal_solvable_threeCore_cubic_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      (∀ A : Subgroup G, A ≤ Y.map I.subtype → IsPPerfect 2 A →
        (T : Subgroup G) ≤ normalizer (A : Set G) →
        Nat.card (A ⧸ pCore 2 A) = 3 →
        A ≤ normalizer (L : Set G)) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,_,_,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hn,_,he⟩ :=
    local_minimal_solvable_threeCore_geometry h hab structural previous faithful J hJ hs
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,?_,he⟩
  intro A hA hAp hAT hAe
  exact local_solvable_cubic_containment h hab structural previous faithful I hI hIs A
    (hA.trans (map_subtype_le Y)) (hA.trans hn) hAp hAT hAe

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
