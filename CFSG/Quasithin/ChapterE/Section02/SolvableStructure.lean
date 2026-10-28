module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PCoreCharacteristicCentralizer
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.CentralizerModulo
public import Theory.ElementaryAbelian.ExtraspecialEquiv
-- Internal access is needed only for the defining normal-core containment
-- J ≤ M; the public source statement keeps the original canonical objects.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The solvable source theorem E.2.1

Retain the original SQTK group, prescribed Sylow subgroup, canonical unique
maximal overgroup M and its normal core J. The two-core of M lies in
C_T(J/O₂(J)), and O₂(J)=O₂(H), so either original escape condition supplies a
nontrivial two-subgroup in the core quotient centralizing the image of J.

B.6.8 identifies the residual of H/O₂(H) with an odd prime core. A
supercritical subgroup detects its ambient centralizer. Its image therefore
cannot lie in J: otherwise the escaping two-subgroup would lie in the odd
prime core. The normal-subgroup dichotomy of B.6.8 then makes this image the
whole residual. A.1.25(1), including its A.1.24 rank-two classification,
supplies the actual cyclic, elementary-plane, or Heisenberg model. Odd-prime
rank descends through the normal two-kernel, using the original SQTK bound.

Source: Aschbacher--Smith, E.2.1, printed p.215; B.6.8(2,4), pp.113--114;
and A.1.20--25, pp.24--25. No irreducibility, supercritical, Frattini-action,
model or cardinality premise is added to the source theorem.
-/
public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
open ChapterB
variable {H : Type*} [Group H] [Finite H]

instance core_pCoreIn_normal (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    ((minimalParabolicCore T hP).pCoreIn 2).Normal := by
  exact ConjAct.normal_of_characteristic_of_normal

omit [Finite H] in
/-- The source quotient in the centralizer is the actual ambient two-core. -/
theorem core_pCoreIn_eq (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    (minimalParabolicCore T hP).pCoreIn 2 = pCore 2 H :=
  minimalParabolic_pCore_core_eq T hP

omit [Finite H] in
/-- The first source alternative implies the second: O₂(M) lies in the
Sylow centralizer of J/O₂(J). -/
theorem maximal_twoCore_le_centralizer (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    (minimalParabolicMax T hP).pCoreIn 2 ≤
      centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) := by
  let M := minimalParabolicMax T hP
  let J := minimalParabolicCore T hP
  have hJM : J ≤ M := normalCore_le _
  have hTM := (minimalParabolicMax_spec T hP).2
  have hMT : M.pCoreIn 2 ≤ (T : Subgroup H) := by
    have hh := pCoreIn_le_sylow M (T.subtype hTM)
    change M.pCoreIn 2 ≤ ((T : Subgroup H).subgroupOf M).map M.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTM] at hh
  have hn : M ≤ normalizer (M.pCoreIn 2 : Set H) := by
    have hh := (pCore 2 M).le_normalizer_map M.subtype
    change M ≤ normalizer ((pCore 2 M).map M.subtype : Set H)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  intro x hx
  apply mem_centralizerModulo_iff.mpr
  refine ⟨hMT hx, ?_⟩
  intro j hj
  apply inf_pCoreIn_le_of_le 2 hJM
  have hm := commutator_mem_commutator hj hx
  exact ⟨commutator_le_left J (M.pCoreIn 2) hm,
    le_normalizer_iff_commutator_le_right.mp (hJM.trans hn) hm⟩

/-- A supercritical subgroup of the odd residual cannot remain in the core
once a nontrivial two-subgroup centralizes the core image. -/
theorem supercritical_eq_top (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hR : pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H))
    (hr : ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
      (pCore 2 H) ≤ pCore 2 H)
    (X : Subgroup (pCore p (H ⧸ pCore 2 H))) (hX : IsSupercriticalPSubgroup p X) : X = ⊤ := by
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let P := pCore p (H ⧸ Q)
  let R := centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP) Q
  let E := X.map P.subtype
  let : X.Characteristic := hX.characteristic
  let : E.Normal := ConjAct.normal_of_characteristic_of_normal
  have hq := QuotientGroup.mk'_surjective Q
  have htwo : pCore 2 (H ⧸ Q) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (p := 2) Q (pCore_isPGroup (G := H) (p := 2))]
    exact (map_eq_bot_iff (f := q) (H := Q)).mpr (by simp [q])
  have hcent : centralizer (P : Set (H ⧸ Q)) ≤ P := by
    change centralizer (pCore p (H ⧸ pCore 2 H) : Set _) ≤ pCore p (H ⧸ pCore 2 H)
    rw [← hR]
    exact centralizer_pResidual_le_of_pCore_eq_bot htwo
  have hdetect : centralizer (E : Set (H ⧸ Q)) ≤ P :=
    centralizer_le_pCore_of_characteristic_detection p hcent X
      (hX.isPGroup_restriction_kernel pCore_isPGroup hp)
  have hRC : R.map q ≤ centralizer (minimalParabolicCoreImage T hP : Set (H ⧸ Q)) := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨j, hj, rfl⟩
    have hh := (mem_centralizerModulo_iff.mp hr).2 j hj
    have he : ⁅q j, q r⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hh
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  have hne : R.map q ≠ ⊥ := by
    intro he
    exact hr (((map_eq_bot_iff (f := q) (H := R)).mp he).trans (by rw [QuotientGroup.ker_mk']))
  have hRp : IsPGroup 2 (R.map q) :=
    (T.isPGroup'.to_le (centralizerModulo_le _ _ _)).map q
  have hnot : ¬ E ≤ minimalParabolicCoreImage T hP := by
    intro he
    have hRP : R.map q ≤ P := (hRC.trans (centralizer_le he)).trans hdetect
    have hd := hRp.disjoint_of_coprime (pCore_isPGroup (p := p) (G := H ⧸ Q))
      (Nat.coprime_two_left.mpr hp)
    exact hne (le_bot_iff.mp ((le_inf le_rfl hRP).trans hd.le_bot))
  have hPE : P ≤ E := by
    obtain hle | hle := minimalParabolic_normal_subgroup_residual_dichotomy T hP (E.comap q)
    · apply False.elim
      apply hnot
      have hh := map_mono (f := q) hle
      rwa [map_comap_eq_self_of_surjective hq] at hh
    · change pCore p (H ⧸ pCore 2 H) ≤ E
      rw [← hR, ← map_pResidual_quotient 2 Q]
      exact map_le_iff_le_comap.mpr hle
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hPE x.property
  exact P.subtype_injective he ▸ hy

/-- The full solvable E.2.1 alternatives, with the source's canonical maximal
and core, its literal quotient, and actual cyclic/elementary/Heisenberg models. -/
theorem source_models {K : GroupClass} (hH : IsSQTK K H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hescape : ¬ (minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) ≤ pCore 2 H) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      ((Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = p ∧
        Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃* Multiplicative (ZMod p))) ∨
       (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = p ^ 2 ∧
        Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃*
          (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) ∨
       (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = p ^ 3 ∧
        IsExtraspecial p (pResidual 2 (H ⧸ pCore 2 H)) ∧
        Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃* HeisenbergPrime p))) := by
  have hr : ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
      (pCore 2 H) ≤ pCore 2 H := by
    have he : centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) =
        centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP) (pCore 2 H) := by
      ext x
      simp only [mem_centralizerModulo_iff, core_pCoreIn_eq T hP]
    rw [← he]
    rcases hescape with hm | hr
    · exact fun h => hm ((maximal_twoCore_le_centralizer T hP).trans h)
    · exact hr
  obtain ⟨p,hp,ho,hR,_,_,_,_⟩ := minimalParabolic_solvable_structure T hP hs
  let : Fact p.Prime := ⟨hp⟩
  let P := pCore p (H ⧸ pCore 2 H)
  have hp2 : p ≠ 2 := fun h => by subst p; exact (by decide : ¬ Odd 2) ho
  obtain ⟨X,hX⟩ := (pCore_isPGroup (p := p) (G := H ⧸ pCore 2 H)).exists_supercriticalPSubgroup hp2
  have hXt : X = ⊤ := supercritical_eq_top T hP ho hR hr X hX
  have hne : P ≠ ⊥ := by
    intro he
    have hm : (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) = ⊥ :=
      (map_pResidual_quotient 2 (pCore 2 H)).trans (hR.trans he)
    have hle := (map_eq_bot_iff (f := QuotientGroup.mk' (pCore 2 H))
      (H := pResidual 2 H)).mp hm
    rw [QuotientGroup.ker_mk'] at hle
    exact minimalParabolic_residual_not_le_core T hP
      (hle.trans (minimalParabolicTwoCore_le_core T hP))
  let : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hne
  have hrank : primeRank p P ≤ 2 :=
    (primeRank_subgroup_le p P).trans
      ((primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
        (hH.stronglyQuasithin p hp ho))
  have hm := (ChapterA.lemma_A_1_25_1 ho pCore_isPGroup hrank X hX).2
  subst X
  let e : (⊤ : Subgroup P) ≃* pResidual 2 (H ⧸ pCore 2 H) :=
    Subgroup.topEquiv.trans (MulEquiv.subgroupCongr hR.symm)
  refine ⟨p,hp,ho,?_⟩
  rcases hm with ⟨hc,⟨d⟩⟩ | ⟨hc,⟨d⟩⟩ | ⟨hc,hex,⟨d⟩⟩
  · exact Or.inl ⟨(Nat.card_congr e.toEquiv).symm.trans hc,⟨e.symm.trans d⟩⟩
  · exact Or.inr (Or.inl ⟨(Nat.card_congr e.toEquiv).symm.trans hc,⟨e.symm.trans d⟩⟩)
  · exact Or.inr (Or.inr ⟨(Nat.card_congr e.toEquiv).symm.trans hc,
      hex.of_mulEquiv e,⟨e.symm.trans d⟩⟩)

end CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
