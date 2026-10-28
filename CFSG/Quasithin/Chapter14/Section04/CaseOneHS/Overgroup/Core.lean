module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.NaturalSetup

/-!
# The original center span is the two-core of LU

G.2.5 expresses O₂(LU) as three conjugates of its intersection with U.
That intersection is VZ(U), so the core is the original L-span of Z(U).
The same product bounds its order by 64. Squaring onto the original
order-eight seed then identifies the square kernel with that seed.

Source: Aschbacher--Smith, 14.3.33(1), printed p.1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The earlier Frattini theorem at the original same-G,T hypotheses. -/
theorem closure_frattini
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    (frattini F.U).map F.U.subtype = F.Vi 1 := by
  let := h.chosen.elementary
  rw [F.localKernel_frattini_eq_point h.source.simpleQTKE L
    (normalizer (L : Set G)) (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives) hne]
  exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))

/-- The actual G.2.5 kernel has precisely the previously calculated U-intersection. -/
theorem marked_core_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (g k : G) (B : ChapterG.Section02.LinearThree.Hypothesis
      (sourceSetup F L) (ZMod 2) 1 g k) :
    ChapterG.Section02.LinearThree.W (sourceSetup F L) g k = V ⊔ F.ZU := by
  let := h.chosen.elementary
  have hUT := closure_le_sylow F s
  have hphi := (closure_frattini h structural alternatives F hne).le
  change F.U ⊓ ChapterG.Section02.LinearThree.S (sourceSetup F L) g k = _
  rw [B.S_eq_star_kernel hUT hphi, ← inf_assoc,
    inf_eq_left.mpr (show F.U ≤ ChapterG.Section02.LinearThree.I (sourceSetup F L) g k
      from le_sup_left.trans le_sup_left), inf_comm]
  exact join_core_inf_closure h structural alternatives F s hne

/-- The literal two-core of LU, before identifying it with O₂(L). -/
theorem centerSpan_eq_join_closure_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    centerSpan L F = (L ⊔ F.U).pCoreIn 2 := by
  let := h.chosen.elementary
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator h structural F
  obtain ⟨k, hk, _, _, ⟨B⟩⟩ := source_almostSpecial h structural alternatives F s hne g hg hgP hgH
  have hUT := closure_le_sylow F s
  have hphi := (closure_frattini h structural alternatives F hne).le
  let I := ChapterG.Section02.LinearThree.I (sourceSetup F L) g k
  let S := ChapterG.Section02.LinearThree.S (sourceSetup F L) g k
  have heI : I = L ⊔ F.U := B.I_eq_LU hUT hphi
  have hW := marked_core_intersection h structural alternatives F s hne g k B
  have hWS : V ⊔ F.ZU ≤ S := hW ▸ inf_le_right
  have hLS : L ≤ normalizer (S : Set G) := (B.L_le_I hUT hphi).trans
    (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hPS : centerSpan L F ≤ S :=
    conjugateSpanBy_le (le_sup_right.trans hWS) hLS
  have hWP : V ⊔ F.ZU ≤ centerSpan L F :=
    sup_le (seed_le_centerSpan h F) (le_conjugateSpanBy _ _)
  have hSP : S ≤ centerSpan L F := by
    dsimp only [S]
    rw [B.S_eq_WProduct hUT hphi]
    dsimp only [ChapterG.Section02.LinearThree.WProduct]
    rw [hW]
    exact sup_le (sup_le hWP (conjugate_le_of_normalizes hWP g
      (le_normalizer_conjugateSpanBy _ _ hg)))
      (conjugate_le_of_normalizes hWP k (le_normalizer_conjugateSpanBy _ _ hk))
  exact (le_antisymm hPS hSP).trans (congrArg (fun J : Subgroup G => J.pCoreIn 2) heI)

omit [Finite G] in
private theorem normalizes_in_abelian (P A B : Subgroup G) [IsMulCommutative P]
    (hA : A ≤ P) (hB : B ≤ P) : B ≤ normalizer (A : Set G) := by
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro b hb a ha
  exact congrArg Subtype.val (mul_comm (⟨a, hA ha⟩ : P) ⟨b, hB hb⟩)

/-- The three original factors of order sixteen bound the full center span. -/
theorem centerSpan_card_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    Nat.card (centerSpan L F) ≤ 64 := by
  let := h.chosen.elementary
  let := centerSpan_abelian h structural F s
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator h structural F
  obtain ⟨k, hk, _, _, ⟨B⟩⟩ := source_almostSpecial h structural alternatives F s hne g hg hgP hgH
  have hUT := closure_le_sylow F s
  have hphi := (closure_frattini h structural alternatives F hne).le
  let A := V ⊔ F.ZU
  have hA : A ≤ centerSpan L F :=
    sup_le (seed_le_centerSpan h F) (le_conjugateSpanBy _ _)
  have hX (x : G) (hx : x ∈ L) : conjugate A x ≤ centerSpan L F :=
    conjugate_le_of_normalizes hA x (le_normalizer_conjugateSpanBy _ _ hx)
  have hVX (x : G) (hx : x ∈ L) : V ≤ conjugate A x := by
    have he : conjugate V x = V := (conjugate_eq_iff V x).mpr (h.chosen.normalizes hx)
    rw [← he]
    exact map_mono le_sup_left
  have hcardA : Nat.card A = 16 := by
    dsimp only [A]
    rw [← centerSpan_inf_closure h structural alternatives F s hne]
    exact centerSpan_inf_closure_card h structural alternatives F s hne
  have hcardX (x : G) : Nat.card (conjugate A x) = 16 := by
    rw [conjugate, card_map_of_injective (MulAut.conj x⁻¹).injective, hcardA]
  have hV : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hfirst := card_mul_eq_card_inf_mul_card_sup_of_normalizes A (conjugate A g)
    (normalizes_in_abelian (centerSpan L F) _ _ hA (hX g hg))
  have hfirstInf := card_le_of_le (le_inf (show V ≤ A from le_sup_left) (hVX g hg))
  rw [hV] at hfirstInf
  rw [hcardA, hcardX] at hfirst
  have hfirstCard : Nat.card (A ⊔ conjugate A g : Subgroup G) ≤ 32 := by nlinarith
  have hsecond := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (A ⊔ conjugate A g) (conjugate A k)
    (normalizes_in_abelian (centerSpan L F) _ _ (sup_le hA (hX g hg)) (hX k hk))
  have hsecondInf := card_le_of_le
    (le_inf (show V ≤ A ⊔ conjugate A g from le_sup_left.trans le_sup_left) (hVX k hk))
  rw [hV] at hsecondInf
  rw [hcardX] at hsecond
  have hS : centerSpan L F = (A ⊔ conjugate A g) ⊔ conjugate A k := by
    have heI : ChapterG.Section02.LinearThree.I (sourceSetup F L) g k = L ⊔ F.U :=
      B.I_eq_LU hUT hphi
    rw [centerSpan_eq_join_closure_core h structural alternatives F s hne, ← heI]
    change ChapterG.Section02.LinearThree.S (sourceSetup F L) g k = _
    rw [B.S_eq_WProduct hUT hphi]
    dsimp only [ChapterG.Section02.LinearThree.WProduct]
    rw [marked_core_intersection h structural alternatives F s hne g k B]
    rfl
  rw [hS]
  nlinarith

/-- Squaring has kernel exactly V, and the original center span has order 64. -/
theorem centerSpan_square_kernel_and_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    (∀ x ∈ centerSpan L F, x ^ 2 = 1 ↔ x ∈ V) ∧ Nat.card (centerSpan L F) = 64 := by
  let := h.chosen.elementary
  obtain ⟨f, hf, hfx⟩ := centerSpan_square_map h structural F s
  have hV : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hN : (V.subgroupOf (centerSpan L F)) ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    rw [hfx]
    exact elemPow_eq_one_of_isElementaryAbelian _ hx
  have hcN : Nat.card (V.subgroupOf (centerSpan L F)) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (seed_le_centerSpan h F)).toEquiv, hV]
  have hlo := card_le_of_le hN
  rw [hcN] at hlo
  have hmul := f.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, hV] at hmul
  have hhi := centerSpan_card_le h structural alternatives F s hne
  have hcK : Nat.card f.ker = 8 := by omega
  have heK : f.ker = V.subgroupOf (centerSpan L F) :=
    (eq_of_le_of_card_ge hN (by rw [hcN, hcK])).symm
  refine ⟨?_, by omega⟩
  intro x hx
  change x ^ 2 = 1 ↔ (⟨x, hx⟩ : centerSpan L F) ∈ V.subgroupOf (centerSpan L F)
  rw [← heK, MonoidHom.mem_ker, Subtype.ext_iff, hfx]
  rfl

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
