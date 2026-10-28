module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FiveExclusion
public import Theory.GroupTheory.NormalComponentParabolicIndex

/-!
# The actual coset degrees of the nonsolvable original pair

The proved component identity O²(X)=K gives X=KT. Restriction of the
common Sylow to K and passage through O₂(K) determine both original
parabolic indices from the same component quotient. The four surviving
13.3.2 models give degrees seven, fifteen, forty-five and sixty-three.
Every row retains its actual model equivalence. In particular the unitary
and triple-cover rows are not discarded by an assumed classification.

This supplies the permutation degrees in the module argument of 13.4.7,
printed pp.900–901. Source1332OneTwo retains its earlier producer
qt-d-1332-source and final discharge with the fixed-core assembly. The
remaining model exclusions and module alternatives are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)

include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK
/-- Both original coset degrees are determined by the same literal component quotient. -/
theorem original_pair_parabolic_index_formula :
    let X := A ⊔ B
    let C := K.map X.subtype
    let n := Nat.card (C ⧸ pCore 2 C)
    A.relIndex X * 3 * 2 ^ n.factorization 2 = n ∧
      B.relIndex X * 3 * 2 ^ n.factorization 2 = n := by
  let X := A ⊔ B
  let S : Sylow 2 X := T.subtype (hTA.trans le_sup_left)
  let C := K.map X.subtype
  let : K.Normal := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  have hgen : K ⊔ (S : Subgroup X) = ⊤ := by
    rw [← (original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1]
    exact pResidual_sup_sylow_eq_top S
  let j := K.equivMapOfInjective X.subtype X.subtype_injective
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 C) j (pCore_map_iso 2 j)
  have hc : Nat.card (K ⧸ pCore 2 K) = Nat.card (C ⧸ pCore 2 C) := Nat.card_congr jq.toEquiv
  have step (P : Subgroup G) (hPX : P ≤ X) (hTP : (T : Subgroup G) ≤ P)
      (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) :
      P.relIndex X * 3 * 2 ^ (Nat.card (C ⧸ pCore 2 C)).factorization 2 =
        Nat.card (C ⧸ pCore 2 C) := by
    let a := subgroupOfEquivOfLe hPX
    have hh := normal_component_parabolic_index K S hgen (P.subgroupOf X)
      (fun _ ht => hTP ht) ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eP)
    rw [hc] at hh
    exact hh
  exact ⟨step A le_sup_left hTA eA,step B le_sup_right hTB eB⟩

/-- Source model comparison retains the precise degrees seven, fifteen,
forty-five and sixty-three; neither exceptional row is silently discarded. -/
theorem original_pair_parabolic_degrees :
    let X := A ⊔ B
    let C := K.map X.subtype
    (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 2 ∧ A.relIndex X = 7 ∧ B.relIndex X = 7) ∨
    (Chapter1.Section02.LocalModels.IsAlternating (C ⧸ pCore 2 C) 6 ∧
      A.relIndex X = 15 ∧ B.relIndex X = 15) ∨
    (Chapter1.Section02.LocalModels.IsAlternatingCover (C ⧸ pCore 2 C) 6 ∧
      A.relIndex X = 45 ∧ B.relIndex X = 45) ∨
    (ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3 ∧ A.relIndex X = 63 ∧ B.relIndex X = 63) := by
  let C := K.map (A ⊔ B).subtype
  obtain ⟨ha,hb⟩ := original_pair_parabolic_index_formula h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  change A.relIndex (A ⊔ B) * 3 * 2 ^ (Nat.card (C ⧸ pCore 2 C)).factorization 2 =
    Nat.card (C ⧸ pCore 2 C) at ha
  change B.relIndex (A ⊔ B) * 3 * 2 ^ (Nat.card (C ⧸ pCore 2 C)).factorization 2 =
    Nat.card (C ⧸ pCore 2 C) at hb
  rcases original_pair_component_quotient_models h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK with hl | ha6 | hc6 | hu
  · have hn : Nat.card (C ⧸ pCore 2 C) = 168 := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hl
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF]
      norm_num
    simp only [hn,show (Nat.factorization 168) 2 = 3 from by decide +kernel] at ha hb
    exact Or.inl ⟨hl,by omega,by omega⟩
  · have hn : Nat.card (C ⧸ pCore 2 C) = 360 := by
      rw [Nat.card_congr ha6.some.toEquiv,nat_card_alternatingGroup]
      norm_num
    simp only [hn,show (Nat.factorization 360) 2 = 3 from by decide +kernel] at ha hb
    exact Or.inr (Or.inl ⟨ha6,by omega,by omega⟩)
  · have hn : Nat.card (C ⧸ pCore 2 C) = 1080 := by
      obtain ⟨_,⟨z⟩,⟨e⟩⟩ := hc6
      rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
        Nat.card_congr e.toEquiv,Nat.card_congr z.toEquiv,nat_card_alternatingGroup]
      norm_num
    simp only [hn,show (Nat.factorization 1080) 2 = 3 from by decide +kernel] at ha hb
    exact Or.inr (Or.inr (Or.inl ⟨hc6,by omega,by omega⟩))
  · have hn : Nat.card (C ⧸ pCore 2 C) = 6048 := by
      obtain ⟨F,_,_,J,hF,hJ,⟨e⟩⟩ := hu
      exact (Nat.card_congr e.toEquiv).trans
        (BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.card_projective J hF hJ)
    simp only [hn,show (Nat.factorization 6048) 2 = 5 from by decide +kernel] at ha hb
    exact Or.inr (Or.inr (Or.inr ⟨hu,by omega,by omega⟩))
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
