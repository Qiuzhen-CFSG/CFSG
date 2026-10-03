module

public import Stellmacher.SectionFiveToSeven.SixThreeCrossNormalizers
public import Stellmacher.SectionFiveToSeven.PFamilyConjugation
public import Stellmacher.BaumannNormalizer
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# A core-free pair for Stellmacher (6.3)

Let E and F be local-family members with shared Sylow subgroup B(S),
generating P1 and P2 together with S. Suppose the nontrivial module
W1=[Omega_1(Z(B)),O^2(E)] lies in B and is normalized by the P1-normal
closure of B. Then some S-conjugate of E has a core-free join with F.

If every such join had nontrivial two-core, the cross-normalizer theorem
would make F normalize every S-conjugate of W1. Its maximal-local
hypothesis follows either from S=S0 or from P1 not being contained in
the unique maximal local subgroup in alternative (5.1)(c). The normal
closure of B also normalizes every conjugate of W1, by its P1-normality.
Thus the S-orbit closure of W1 is normalized by both P1 and P2. This
nontrivial two-subgroup inside B would lie in their join's trivial core.

Source: Stellmacher (6.3), Journal of Algebra 190 (1997), p.31,
refs/latex/stellmacher-n-group.tex, selection of the core-free local pair.
The module equality is the explicit omega-coordinate input supplied by
(2.2); no unproved identification with a full core commutator is used.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixThree_exists_core_free_pair
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (E F W1 M : Subgroup H)
    (hE : E ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hF : F ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hEL : E ≤ sectionSixL (baumannIn S) P1)
    (hgenE : E ⊔ S = P1) (hgenF : F ⊔ S = P2)
    (hW1 : W1 = ⁅omegaOneCenter (baumannIn S), twoResidualIn E⁆)
    (hW1ne : W1 ≠ ⊥) (hW1B : W1 ≤ baumannIn S)
    (hLW1 : sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W1 : Set H))
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    ∃ s : H, s ∈ S ∧ twoCoreIn (conjugateBy E s ⊔ F) = ⊥ := by
  classical
  by_contra! hcore
  let B := baumannIn S
  let L := sectionSixL B P1
  let W := conjugateClosure W1 S
  have hBS : B ≤ S := inf_le_left
  have hSP1 : S ≤ P1 := by rw [← hgenE]; exact le_sup_right
  have hSB : S ≤ Subgroup.normalizer (B : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hP1L : P1 ≤ Subgroup.normalizer (L : Set H) := by
    rw [show L = conjugateClosure B P1 from rfl, conjugateClosure,
      Subgroup.le_normalizer_closure_iff]
    intro p hp x hx
    obtain ⟨q, b, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨⟨p * (q : H), P1.mul_mem hp q.property⟩, b, ?_⟩
    change p * ((q : H) * (b : H) * (q : H)⁻¹) * p⁻¹ =
      (p * (q : H)) * (b : H) * (p * (q : H))⁻¹
    group
  have hEsfamily (s : S) : conjugateBy E (s : H) ∈ PFamily (⊤ : Subgroup H) B :=
    (conjugateBy_mem_pFamily_iff B E s (hSB s.property)).mpr hE
  have hEsgen (s : S) : conjugateBy E (s : H) ⊔ S = P1 := by
    have hSm : S.map (MulAut.conj (s : H)).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer s.property)
    have hPm : P1.map (MulAut.conj (s : H)).toMonoidHom = P1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (P1.le_normalizer (hSP1 s.property))
    have hm := congrArg (fun A : Subgroup H => A.map (MulAut.conj (s : H)).toMonoidHom) hgenE
    rw [Subgroup.map_sup, hSm, hPm] at hm
    exact hm
  have halt (s : S) : S = (S0 : Subgroup H) ∨ ¬ (conjugateBy E (s : H) ⊔ F) ≤ M := by
    cases h.fiveOne.alternative with
    | a hS _ _ => exact Or.inl hS
    | b hS _ => exact Or.inl hS
    | c M' hM' _ _ _ _ _ hP1 _ _ _ _ _ =>
      right
      have hMM' : M = M' := hM'.2 M hM
      subst M'
      intro hjoin
      apply hP1
      rw [← hEsgen s]
      exact sup_le (le_sup_left.trans hjoin) (h.fiveOne.S_le_S0.trans hM.2)
  have hWs (s : S) : conjugateBy W1 (s : H) =
      ⁅omegaOneCenter B, twoResidualIn (conjugateBy E (s : H))⁆ := by
    have hBmap : B.map (MulAut.conj (s : H)).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSB s.property)
    have hOmap : (omegaOneCenter B).map (MulAut.conj (s : H)).toMonoidHom = omegaOneCenter B := by
      change (omegaOneCenterAmbient B).map _ = omegaOneCenterAmbient B
      rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj (s : H)).injective, hBmap]
    have hRmap : (twoResidualIn E).map (MulAut.conj (s : H)).toMonoidHom =
        twoResidualIn (conjugateBy E (s : H)) :=
      map_twoResidualAmbient_of_subgroup_image E (MulAut.conj (s : H)).toMonoidHom _ rfl
    change W1.map (MulAut.conj (s : H)).toMonoidHom = _
    rw [hW1, Subgroup.map_commutator, hOmap, hRmap]
  have hFWs (s : S) : F ≤ Subgroup.normalizer (conjugateBy W1 (s : H) : Set H) := by
    rw [hWs s]
    exact (sixThree_cross_normalizers S0 S P1 P2 h (conjugateBy E (s : H)) F M
      (hEsfamily s) hF hM (hcore s s.property) (halt s)).1
  have hLWs (s : S) : L ≤ Subgroup.normalizer (conjugateBy W1 (s : H) : Set H) := by
    have hLm : L.map (MulAut.conj (s : H)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP1L (hSP1 s.property))
    have hm := Subgroup.map_mono (f := (MulAut.conj (s : H)).toMonoidHom) hLW1
    change L.map (MulAut.conj (s : H)).toMonoidHom ≤ _ at hm
    rw [Subgroup.map_equiv_normalizer_eq, hLm] at hm
    exact hm
  have hactors (A : Subgroup H)
      (hA : ∀ s : S, A ≤ Subgroup.normalizer (conjugateBy W1 (s : H) : Set H)) :
      A ≤ Subgroup.normalizer (W : Set H) := by
    rw [show W = conjugateClosure W1 S from rfl, conjugateClosure,
      Subgroup.le_normalizer_closure_iff]
    intro a ha x hx
    obtain ⟨s, w, rfl⟩ := hx
    have hmem : a * ((s : H) * (w : H) * (s : H)⁻¹) * a⁻¹ ∈ conjugateBy W1 (s : H) :=
      (Subgroup.mem_normalizer_iff.mp (hA s ha) _).mp ⟨w, w.property, rfl⟩
    obtain ⟨z, hz, heq⟩ := hmem
    apply Subgroup.subset_closure
    exact ⟨s, ⟨z, hz⟩, heq.symm⟩
  have hSW : S ≤ Subgroup.normalizer (W : Set H) := by
    rw [show W = conjugateClosure W1 S from rfl, conjugateClosure,
      Subgroup.le_normalizer_closure_iff]
    intro s hs x hx
    obtain ⟨t, w, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨⟨s * (t : H), S.mul_mem hs t.property⟩, w, ?_⟩
    change s * ((t : H) * (w : H) * (t : H)⁻¹) * s⁻¹ =
      (s * (t : H)) * (w : H) * (s * (t : H))⁻¹
    group
  have hWB : W ≤ B := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s, w, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hSB s.property) (w : H)).mp (hW1B w.property)
  have hW1W : W1 ≤ W := by
    intro w hw
    exact Subgroup.subset_closure ⟨1, ⟨w, hw⟩, by simp⟩
  have hP1W : P1 ≤ Subgroup.normalizer (W : Set H) := by
    rw [← hgenE]
    exact sup_le (hEL.trans (hactors L hLWs)) hSW
  have hP2W : P2 ≤ Subgroup.normalizer (W : Set H) := by
    rw [← hgenF]
    exact sup_le (hactors F hFWs) hSW
  let J := P1 ⊔ P2
  have hWJ : W ≤ J := hWB.trans (hBS.trans (hSP1.trans le_sup_left))
  have hWnormal : (W.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWJ).mpr (sup_le hP1W hP2W)
  have hWp : IsPGroup 2 W := S0.isPGroup'.to_le (hWB.trans (hBS.trans h.fiveOne.S_le_S0))
  have hWJp : IsPGroup 2 (W.subgroupOf J) :=
    hWp.comap_of_injective J.subtype J.subtype_injective
  have hWcore : W ≤ twoCoreIn J := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWJ]
    exact Subgroup.map_mono (show W.subgroupOf J ≤ pCore 2 J from le_sSup ⟨hWnormal, hWJp⟩)
  exact hW1ne (le_bot_iff.mp (hW1W.trans (hWcore.trans_eq h.fiveOne.join_twoCore_eq_bot)))

end Stellmacher.SectionsFiveToSeven

