module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianRadical
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape

/-!
# Quasisimplicity of the original abelian component

The nonquasisimple A.3.6 alternatives supply an odd Fitting prime p>3.
A.3.8 makes the actual component normal in H. Its characteristic radical
Ξ_p(K) is nontrivial and has p-group two-core quotient, contradicting the
original point-action exclusion. Thus K/O₂(K) is quasisimple. The escaping
component constructor applies this result on the literal reduced actor
K₀L₁T, preserving its inclusion in the original H and its Hz membership.

This proves the quasisimplicity clause of 12.6.30(3). Its F.9.18 model
classification and the alternatives in12.6.31 are separate obligations.
Source: Aschbacher--Smith, printed p.835.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Source12.6.30(3), quasisimplicity clause, for the actual abelian
component. The constrained A.3.6 cases give a nontrivial characteristic
two-by-p radical, excluded by the original point action. -/
theorem SourceHypothesis.original_abelian_component_quasisimple
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  classical
  by_contra hn
  let Ki := K.subgroupOf H
  let C := Ki.map (QuotientGroup.mk' (pCore 2 H))
  let eK : K ≃* Ki := (subgroupOfEquivOfLe hKH).symm
  let e : (K ⧸ pCore 2 K) ≃* C :=
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans
      (cComponentTwoCoreQuotientEquiv hK)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hC : C.IsCComponent := hK.map_quotient _
  have hnC : ¬ IsQuasisimple C := fun h => hn (h.of_mulEquiv e.symm)
  have hQ := S.original_star_sqtk D hZ z hz hH
  have hCN : C.Normal :=
    (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hQ
      (pCore_quotient_pCore_eq_bot 2) hC).resolve_right hnC
  have hKN : Ki.Normal := cComponent_normal_of_quotient_normal hK (pCore 2 H) hCN
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hKN
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have ha := hA36 _ hQ (pCore_quotient_pCore_eq_bot 2) C hC
  have hs := Chapter1.RadicalStructure.nonsimple_radical ha hnC
  have hfitne : Nat.card (fittingSubgroup C) ≠ 1 := by
    intro hc
    have hf : fittingSubgroup C = ⊥ := card_eq_one.mp hc
    have hgf : generalizedFitting C = fittingSubgroup C := hs.elim And.left And.left
    have hct : (⊤ : Subgroup C) ≤ ⊥ := by
      intro a _
      have hh := centralizer_generalizedFitting_le C
      rw [hgf,hf] at hh
      apply hh
      intro b hb
      have hb1 : b = 1 := mem_bot.mp hb
      simp only [hb1,one_mul,mul_one]
    let : Subsingleton C := ⟨fun a b => (mem_bot.mp (hct (mem_top a))).trans
      (mem_bot.mp (hct (mem_top b))).symm⟩
    exact hC.not_isSolvable inferInstance
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hfitne
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3,hω⟩ := Chapter1.RadicalStructure.core_omega hs hd
  have ho : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  let eCore : pCore p (K ⧸ pCore 2 K) ≃* pCore p C :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
  have hq : Chapter1.XiOddQuotient p (Chapter1.XiQuotient (Chapter1.XiP p K)) :=
    hω.of_mulEquiv ((Chapter1.xiPQuotientEquivOmega ho K).trans (eCore.omega p 1)).symm
  exact Chapter1.XiP_ne_bot_of_oddQuotient hp K hq
    (S.original_no_normal_large_prime_radical D hZ z hz hTV hTz hbound hTI hns hH
      ((Chapter1.XiP_le p K).trans hKH) (Chapter1.XiP_invariant p hHK)
      (Chapter1.XiP_isPPerfect p K) hp3 hq.isPGroup)

/-- Select the escaping quasisimple component and change to the literal
reduced actor K₀L₁T. No component from the contrary nonabelian branch is used. -/
theorem SourceHypothesis.original_abelian_quasisimple_reduced_actor_exists
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
        (K.subgroupOf J).IsCComponent := by
  obtain ⟨K,hKH,hK,hout,hL,hK₀,hJH,hJ,hKJ⟩ := S.original_abelian_reduced_actor_exists
    D hZ z hz hTV hTz hbound hTI hns hH
  exact ⟨K,hKH,hK,hout,
    S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK,
    hL,hK₀,hJH,hJ,hKJ⟩
end CFSG.Quasithin.Chapter12.Section06
