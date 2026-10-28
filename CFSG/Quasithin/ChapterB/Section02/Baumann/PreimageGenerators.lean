module

public import CFSG.Quasithin.ChapterB.Section02.Baumann
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# Baumann's argument for full preimages of the generating images

This is the two-kernel specialization of B.2.19 used in the natural-point
case of C.1.37. The generating groups Dᵢ are the actual full inverse images
under G → G/C_G(V). Their elementary Thompson subgroups satisfy (a)–(d)
of B.2.18. Source condition (E) factors every maximum elementary image
into equal-weight subgroups contained in component conjugates of Dᵢ*.

The common kernel normalizes every J(Dᵢ). The preliminary Frattini cover
therefore shows that L normalizes I = ⟨J(Dᵢ)⟩. Replacement lifts each
factor into a maximum elementary subgroup in a conjugate Dᵢ. Its full
rank puts the lift in J(Dᵢ), and the kernel part lies in J(C_R(V)). Thus
J(R) ≤ I, discharging precisely the missing condition (e). Applying the
proved B.2.18 gives all four conclusions of B.2.19 on the original groups.

When C_G(V) is a two-group, the source Sylow preimages in (D) really are
full preimages. No module classification or characteristic-normal-subgroup
alternative is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.19,
printed pp.81–82, and its natural L₃(2) application in C.1.37, p.143.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Finite G] in
private theorem maxJ_normalizer (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer (elementaryAbelianMaxJ D : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (elementaryAbelianMaxJ D).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp hg

private theorem max_le_J_of_order (R D A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hAD : A ≤ D)
    (horder : elementaryAbelianMaxOrder D = elementaryAbelianMaxOrder R) :
    A ≤ elementaryAbelianMaxJ D := by
  apply le_sSup
  refine ⟨hAD, hA.2.1, ?_⟩
  intro E hED hE
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty D
  calc
    Nat.card E ≤ Nat.card B := hB.2.2 E hED hE
    _ = elementaryAbelianMaxOrder D := card_eq_elementaryAbelianMaxOrder D B hB
    _ = elementaryAbelianMaxOrder R := horder
    _ = Nat.card A := maxOrder_eq_card_of_mem R A hA

private theorem maxJ_le_of_order (Q D : Subgroup G) (hQD : Q ≤ D)
    (horder : elementaryAbelianMaxOrder Q = elementaryAbelianMaxOrder D) :
    elementaryAbelianMaxJ Q ≤ elementaryAbelianMaxJ D :=
  (elementaryAbelianMaxOrder_le_and_j_le_of_eq Q D hQD).2 horder

/-- Equal-weight factorization of the actual maximum images puts the entire
Thompson subgroup in the generated family. No Thompson containment is an input. -/
theorem maxJ_le_generated_of_preimage_cover
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (D : ι → Subgroup G)
    (h : HypothesesAD V R (fun i => elementaryAbelianMaxJ (D i)))
    (hD : ∀ i, ((D i).map (actionMap V)).comap (actionMap V) = D i)
    (hrank : ∀ i, twoRank (D i) = twoRank R)
    (hcover : ∀ A ∈ elementaryAbelianMaxSubgroups R, A.map (actionMap V) ≠ ⊥ →
      ∃ E : Set (Subgroup (G ⧸ centralizer (V : Set G))),
        sSup E = A.map (actionMap V) ∧
        ∀ B ∈ E,
          IsElementaryTwo B ∧
          EqualWeightLE (NormalElementaryQuotient.representation V (actionMap V)
            (QuotientGroup.mk'_surjective _) (actionMap_ker V)) B (A.map (actionMap V)) ∧
          ∃ i, ∃ g ∈ pResidual 2 G,
            B ≤ ((D i).map (MulAut.conj g).toMonoidHom).map (actionMap V)) :
    elementaryAbelianMaxJ R ≤ ⨆ i, elementaryAbelianMaxJ (D i) := by
  classical
  let q := actionMap V
  let Q := R ⊓ centralizer (V : Set G)
  let I := ⨆ i, elementaryAbelianMaxJ (D i)
  have hkerD (i : ι) : q.ker ≤ D i := by
    rw [← hD i, comap_map_eq]
    exact le_sup_right
  have hQD (i : ι) : Q ≤ D i :=
    inf_le_right.trans ((actionMap_ker V).symm ▸ hkerD i)
  have hQI : Q ≤ normalizer (I : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change I.map (MulAut.conj g).toMonoidHom = I
    dsimp only [I]
    rw [Subgroup.map_iSup]
    congr 1
    funext i
    exact mem_normalizer_iff_map_conj_eq.mp
      (maxJ_normalizer (D i) ((D i).le_normalizer (hQD i hg)))
  have hLI : pResidual 2 G ≤ normalizer (I : Set G) :=
    (residual_le_generated_sup_centralizer V R _ h).trans
      (sup_le I.le_normalizer hQI)
  have hconj (i : ι) (g : G) (hg : g ∈ pResidual 2 G) :
      elementaryAbelianMaxJ ((D i).map (MulAut.conj g).toMonoidHom) ≤ I := by
    rw [elementaryAbelianMaxJ_map_equiv]
    exact (map_mono (le_iSup (fun j => elementaryAbelianMaxJ (D j)) i)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hLI hg))
  have horderD (i : ι) : elementaryAbelianMaxOrder (D i) = elementaryAbelianMaxOrder R := by
    rw [maxOrder_eq_two_pow_rank, maxOrder_eq_two_pow_rank, hrank i]
  have horderQ : elementaryAbelianMaxOrder Q = elementaryAbelianMaxOrder R := by
    rw [maxOrder_eq_two_pow_rank, maxOrder_eq_two_pow_rank,
      (centralizer_rank_and_alpha V R h.V_le_R h.no_strong).1]
  have hJQI : elementaryAbelianMaxJ Q ≤ I := by
    let i : ι := Classical.choice inferInstance
    exact (maxJ_le_of_order Q (D i) (hQD i)
      (horderQ.trans (horderD i).symm)).trans
      (le_iSup (fun j => elementaryAbelianMaxJ (D j)) i)
  apply sSup_le
  intro A hA
  have hAK : A ⊓ q.ker ≤ I := by
    let C := V ⊔ (A ⊓ centralizer (V : Set G))
    have hC := maximal_replacement V R A h.V_le_R h.no_strong hA
    have hCQ : C ≤ Q := le_inf hC.1 (sup_le V.le_centralizer inf_le_right)
    have hCJ : C ≤ elementaryAbelianMaxJ Q :=
      max_le_J_of_order R Q C hC hCQ horderQ
    rw [actionMap_ker V]
    exact (show A ⊓ centralizer (V : Set G) ≤ C from le_sup_right).trans (hCJ.trans hJQI)
  by_cases hz : A.map q = ⊥
  · have hAk := (map_eq_bot_iff A).mp hz
    exact (le_inf le_rfl hAk).trans hAK
  obtain ⟨E, hE, hparts⟩ := hcover A hA hz
  have hmap : A.map q ≤ (A ⊓ I).map q := by
    rw [← hE]
    apply sSup_le
    intro B hB
    obtain ⟨hBe, hBA, i, g, hg, hBg⟩ := hparts B hB
    let B₀ := A ⊓ B.comap q
    let C := B₀ ⊔ (V ⊓ centralizer (B₀ : Set G))
    obtain ⟨hC, hCmap⟩ := lemma_B_2_8_construct V q
      (QuotientGroup.mk'_surjective _) (actionMap_ker V) R h.V_le_R A hA B hBe hBA
    have hkerConj : q.ker ≤ (D i).map (MulAut.conj g).toMonoidHom := by
      intro x hx
      refine ⟨g⁻¹ * x * g, hkerD i ?_, ?_⟩
      · change q (g⁻¹ * x * g) = 1
        rw [map_mul, map_mul, map_inv, show q x = 1 from hx]
        simp
      · dsimp; group
    have hCD : C ≤ (D i).map (MulAut.conj g).toMonoidHom := by
      have hh : C.map q ≤ ((D i).map (MulAut.conj g).toMonoidHom).map q := hCmap ▸ hBg
      exact (le_comap_map q C).trans
        ((comap_mono hh).trans_eq (comap_map_eq_self hkerConj))
    have hCI : C ≤ I := by
      apply (max_le_J_of_order R _ C hC hCD ?_).trans (hconj i g hg)
      rw [maxOrder_eq_two_pow_rank, twoRank_map_equiv, ← maxOrder_eq_two_pow_rank]
      exact horderD i
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBA.1 hb
    exact ⟨a, ⟨ha, hCI (mem_sup_left (show a ∈ B₀ from ⟨ha, hb⟩))⟩, rfl⟩
  intro a ha
  obtain ⟨b, hb, he⟩ := hmap (mem_map_of_mem q ha)
  have hab : a * b⁻¹ ∈ A ⊓ q.ker := by
    refine ⟨A.mul_mem ha (A.inv_mem hb.1), ?_⟩
    change q (a * b⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using I.mul_mem (hAK hab) hb.2



/-- The four conclusions of B.2.19 for the literal full-preimage family.
This applies B.2.18 after proving its Thompson-generation hypothesis. -/
theorem baumann_of_preimage_cover
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (D : ι → Subgroup G)
    (h : HypothesesAD V R (fun i => elementaryAbelianMaxJ (D i)))
    (hD : ∀ i, ((D i).map (actionMap V)).comap (actionMap V) = D i)
    (hrank : ∀ i, twoRank (D i) = twoRank R)
    (hcover : ∀ A ∈ elementaryAbelianMaxSubgroups R, A.map (actionMap V) ≠ ⊥ →
      ∃ E : Set (Subgroup (G ⧸ centralizer (V : Set G))),
        sSup E = A.map (actionMap V) ∧
        ∀ B ∈ E,
          IsElementaryTwo B ∧
          EqualWeightLE (NormalElementaryQuotient.representation V (actionMap V)
            (QuotientGroup.mk'_surjective _) (actionMap_ker V)) B (A.map (actionMap V)) ∧
          ∃ i, ∃ g ∈ pResidual 2 G,
            B ≤ ((D i).map (MulAut.conj g).toMonoidHom).map (actionMap V))
    (hQ : IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
      ((pResidual 2 G ⊔ R) ⊓ centralizer (V : Set G))) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann R ∧
      thompsonAlpha R =
        (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set G))
        ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G)) ∧
      (IsSylowSubgroupIn ((baumann R).map (actionMap V))
          ((pResidual 2 G).map (actionMap V) ⊔ (baumann R).map (actionMap V)) →
        IsSylowSubgroupIn (baumann R) (pResidual 2 G ⊔ baumann R)) := by
  have hJI := maxJ_le_generated_of_preimage_cover V R D h hD hrank hcover
  obtain ⟨hc, ha, hs⟩ := lemma_B_2_18 V R _ h hJI
  exact ⟨hc, ha, (hs hQ).1, (hs hQ).2⟩

end CFSG.Quasithin.ChapterB.BaumannArgument
