module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Contracts
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Center
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Rank
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Residual
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Quotient

/-!
# Conditional assembly of the first local-cover reduction

The rank bound makes L normal in its eligible outside overgroup and selects
the marked diagonal branch. A root subgroup in a four-group forces n=2.
The compatible centralizing plane excludes the second choice of 15.3.10;
the cyclic supplement then excludes the order-27 quotient of Y₊.

Once the Borel and residual data have been constructed, the actual diagonal
actor transfers to Y_D before the intrinsic cover calculations are used.
The central-omega argument, conjugate core orders, and fixed-root inclusions
then identify Z(L), C_S(L), and C_I(L) with the chosen first plane. The product
order formula gives O₂(Y)=S∩L. Full marked automorphism coverage supplies the
literal product I=L Y_D S, with normality only relative to I.

`local_cover_of_prepared_data` is conditional: construction of the two output
data records remains mandatory. It is not source 15.3.38. The outside-family
condition and uniformly quantified local rank, Sylow and odd-core inputs are
retained so the source owner can reuse the reduction for N_G(V₁).

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1135--1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The centralizing plane rules out the second source choice before either
plane is identified with the component center. -/
theorem OrientedBorelData.yplus_eq_y
    {M Y Yplus S L V₁ V₂ : Subgroup G} {n : ℕ}
    {c : ProjectiveMarking L (2 ^ n)} (b : OrientedBorelData M Yplus S L V₁ V₂ c)
    (h10 : Hypothesis15310 M Y S V₁ Yplus)
    (hcase : Chapter4.UniqueMaximalOvergroup (Y ⊔ S) M →
      Yplus = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G)) →
      normalizer (V₁ : Set G) ≤ M ∧ normalizer (V₂ : Set G) ≤ M)
    (hLM : ¬ L ≤ M) : Yplus = Y := by
  apply yplus_eq_y_of_centralized_plane h10 hcase
    (show b.W₁ = V₁ ∨ b.W₁ = V₂ from b.planes.imp And.left And.left) _ hLM
  have hWC : b.W₁ ≤ S ⊓ centralizer (componentPart Yplus L : Set G) :=
    le_inf b.first_le_sylow (le_centralizer_iff.mp b.component_centralizes)
  exact (hWC.trans b.sylow_centralizer.le).trans inf_le_right

/-- Conditional assembly of the local-cover paragraph. The two data inputs
are outputs whose construction remains the source reduction's obligation.
All three center/centralizer identities and n=2 are deductions. -/
theorem local_cover_of_prepared_data
    {M Y Yplus S V V₁ V₂ I L : Subgroup G} {n : ℕ}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hrank : ∀ J ∈ outsideFamily Yplus S M, primeRank 3 J ≤ 2)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hLrank : primeRank 3 L = 2) (hLM : ¬ L ≤ M)
    (hSM : S ≤ M) (hMY : M ≤ normalizer (Y : Set G))
    (hΩ : centralOmegaIn S ≤ V) (hVY : V ⊓ centralizer (Y : Set G) = ⊥)
    (h10 : Hypothesis15310 M Y S V₁ Yplus)
    (hcase : Chapter4.UniqueMaximalOvergroup (Y ⊔ S) M →
      Yplus = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G)) →
      normalizer (V₁ : Set G) ≤ M ∧ normalizer (V₂ : Set G) ≤ M)
    (hquot : (IsElementaryAbelian 3 (Yplus ⧸ pCore 2 Yplus) ∧
      Nat.card (Yplus ⧸ pCore 2 Yplus) = 9) ∨ Nat.card (Yplus ⧸ pCore 2 Yplus) = 27)
    (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (y : G) (hyY : y ∈ Yplus) (hy : c.Diagonal y)
    (hprod : (Yplus : Set G) = (componentPart Yplus L : Set G) * (zpowers y : Set G))
    (b : OrientedBorelData M Yplus S L V₁ V₂ c)
    (hresidual : Yplus = Y →
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (Fin 2 → ZMod 3)) →
      ResidualPlaneData M Y Yplus L b.W₁ b.W₂)
    (hcalculations : n = 2 → ResidualPlaneData M Y Yplus L b.W₁ b.W₂ →
      (∃ z ∈ planeResidual M Y b.W₂, c.Diagonal z) →
      CoverCalculations S L (planeResidual M Y b.W₂) b.W₂ c) :
    n = 2 ∧ Yplus = Y ∧ (L.subgroupOf I).Normal ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
      componentPart Yplus L = planeResidual M Y b.W₁ ∧
      (Y : Set G) = (componentPart Yplus L : Set G) * (planeResidual M Y b.W₂ : Set G) ∧
      center L = pCore 2 L ∧ centerImage L = b.W₁ ∧
      S ⊓ centralizer (L : Set G) = b.W₁ ∧
      I ⊓ centralizer (L : Set G) = b.W₁ ∧
      S ⊓ L = Y.pCoreIn 2 ∧
      (I : Set G) = (L : Set G) * (planeResidual M Y b.W₂ : Set G) * (S : Set G) ∧
      ∃ h : 2 ^ n = 4, (resizeMarking c h).Diagonal y ∧
        ∃ z ∈ planeResidual M Y b.W₂, (resizeMarking c h).Diagonal z := by
  let A := componentPart Yplus L
  let D := planeResidual M Y b.W₂
  have hYeq := b.yplus_eq_y h10 hcase hLM
  have hn2 := parameter_eq_two_of_root c hn heven
    (b.second_le_component_sylow.trans inf_le_right) b.second_card b.root
  have hnormal := rank_two_component_normal_in hLI hL (hodd I hI) (hrank I hI) hLrank
  have hIL := (normal_subgroupOf_iff_le_normalizer hLI).mp hnormal
  have hYplusI : Yplus ≤ I := le_sup_left.trans hI.1.2
  have hYI : Y ≤ I := hYeq ▸ hYplusI
  have hYA : Y ≤ normalizer (A : Set G) := by
    rw [← hYeq]
    exact ComponentIntersection.normalizes_intersectionResidual (hYplusI.trans hIL)
  have hbound := quotient_card_le_nine_of_cyclic_supplement
    ((map_subtype_le _).trans inf_le_left)
    (ComponentIntersection.normalizes_intersectionResidual (hYplusI.trans hIL))
    hyY hy.1 hprod b.component_quotient
  have hE : IsElementaryAbelian 3 (Yplus ⧸ pCore 2 Yplus) ∧
      Nat.card (Yplus ⧸ pCore 2 Yplus) = 9 := by
    rcases hquot with h | h
    · exact h
    · omega
  have h9 : Nat.card (Y ⧸ pCore 2 Y) = 9 := hYeq ▸ hE.2
  have he9 : Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (Fin 2 → ZMod 3)) := by
    rw [← hYeq]
    let := hE.1
    exact ComponentIntersection.quotient_equiv_elementaryNine_of_card hE.2
      (IsElementaryAbelian.exponent_dvd_p 3 _)
  have r := hresidual hYeq he9
  have hDY : D ≤ Y := (planeResidual_le M Y b.W₂).trans inf_le_left
  obtain ⟨z, hzD, hz3, hzL⟩ := r.outside_actor
  have hz := diagonal_from_cyclic_supplement c (hYplusI.trans hIL) hyY hy hprod
    (hYeq.symm ▸ hDY hzD) hz3 hzL
  have m := hcalculations hn2 r ⟨z, hzD, hz⟩
  have hDN : D ≤ normalizer (A : Set G) := hDY.trans hYA
  have hSY : S ≤ normalizer (Y : Set G) := hSM.trans hMY
  have hSD : S ≤ normalizer (D : Set G) :=
    normalizes_planeResidual (hSM.trans M.le_normalizer) hSY b.second_invariant
  have hMt : M.map (MulAut.conj b.t).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer b.t_mem)
  have hYt : Y.map (MulAut.conj b.t).toMonoidHom = Y :=
    mem_normalizer_iff_map_conj_eq.mp (hMY b.t_mem)
  have hAD : A.map (MulAut.conj b.t).toMonoidHom = D := by
    change (componentPart Yplus L).map _ = _
    rw [r.component_eq, planeResidual_map, hMt, hYt, b.first_interchange]
  have hDA : D.map (MulAut.conj b.t).toMonoidHom = A := by
    change (planeResidual M Y b.W₂).map _ = _
    rw [planeResidual_map, hMt, hYt, b.second_interchange, ← r.component_eq]
  obtain ⟨P, hP⟩ := hSylow I hI
  obtain ⟨hZ, hZW, hCS, hCI, hDcore, _⟩ := center_and_centralizers
    I L Y S V A D b.W₁ b.W₂ hLI hL hIL P hP (hodd I hI)
    hSY hΩ hVY r.generated b.t b.sylow_invariant hAD hDA b.second_interchange
    b.component_core (inf_le_left.trans hSD) m.normalizes_sylow m.commutator
    b.sylow_centralizer b.second_le_component_sylow
    ((planeResidual_le M Y b.W₂).trans (inf_le_right.trans inf_le_right))
    m.root_fixed m.sylow_fixed
  have hDcard : Nat.card D = Nat.card A := by
    rw [← hAD, card_map_of_injective (MulAut.conj b.t).injective]
  have hYcore := core_of_residual_product r.generated hDN b.component_core hDcore
    hDcard b.component_quotient h9
  have hC : I ⊓ centralizer (L : Set G) ≤ L :=
    hCI ▸ hZW ▸ centerImage_le L
  let : IsQuasisimple (L.subgroupOf I) := hL.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLI).toMonoidHom) (subgroupOfEquivOfLe hLI).surjective
  have hIprod := product_of_marked_automorphism_coverage c hZ.ge hLI (hDY.trans hYI)
    (le_sup_right.trans hI.1.2) hIL hC m.automorphisms
  have hYprod : (Y : Set G) = (A : Set G) * (D : Set G) := by
    rw [r.generated, coe_mul_of_right_le_normalizer_left A D hDN]
  have hq : 2 ^ n = 4 := by rw [hn2]; norm_num
  exact ⟨hn2, hYeq, hnormal, he9, r.component_eq, hYprod,
    hZ, hZW, hCS, hCI, hYcore.symm, hIprod, hq, hy, z, hzD, hz⟩


/-- Select the marked diagonal branch using the genuine rank-two hypotheses.
The earlier alternatives and local rank/odd-core inputs are uniform over
eligible outside overgroups, as required for the later normalizer reuse. -/
theorem marked_diagonal_of_rank_two {M Yplus S I L : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hrank : ∀ J ∈ outsideFamily Yplus S M, primeRank 3 J ≤ 2)
    (hLrank : primeRank 3 L = 2) (hYL : ¬ Yplus ≤ L)
    (hmodels : ∀ K : Subgroup G, Candidates.RankOneModel K → primeRank 3 K ≤ 1)
    (h37 : ∀ J ∈ outsideFamily Yplus S M, ∀ K : Subgroup G,
      K ≤ J → IsComponent J (K.subgroupOf J) →
      Yplus ≤ localSpan K S ∨ Candidates.RankOneModel K ∨
        Candidates.RankTwoDiagonal Yplus K (localSpan K S)) :
    (L.subgroupOf I).Normal ∧ ∃ n : ℕ, 0 < n ∧ Even n ∧
      ∃ y ∈ Yplus, ∃ c : ProjectiveMarking L (2 ^ n), c.Diagonal y ∧
        (Yplus : Set G) = (componentPart Yplus L : Set G) * (zpowers y : Set G) := by
  obtain ⟨hn, hd⟩ := diagonal_of_rank_two hLI (le_sup_right.trans hI.1.2) hL
    (hodd I hI) (hrank I hI) hLrank hYL (hmodels L) (h37 I hI L hLI hL)
  exact ⟨hn, marking_of_rankTwoDiagonal hd⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
