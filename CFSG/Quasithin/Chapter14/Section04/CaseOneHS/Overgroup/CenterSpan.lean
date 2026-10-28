module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Contracts
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AmbientControl
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.CyclicSpan
public import Theory.GroupTheory.CyclicFourCentralSquares

/-!
# The original cyclic center and its abelian L-span

The local central-product structure identifies Z(U) with C₄. Its unique
involution is the original flag point. Since the point normalizer preserves
Z(U), the cyclic TI criterion and I.7.5 apply to its actual conjugates.
The original natural action puts their L-span in O₂(LT), so these conjugates
commute. Their squares generate precisely the original natural seed V.

This proves the TI and commuting-conjugates step of 14.3.33(1). The equality
of this span with O₂(L), and the terminal overgroup and transfer arguments,
are not asserted here. Source: Aschbacher--Smith, printed pp.1004--1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The cyclic center in its original ambient embedding. -/
theorem center_model (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    Nonempty (F.ZU ≃* Multiplicative (ZMod 4)) := by
  obtain ⟨e⟩ := s.core_shape.center_model
  exact ⟨((center F.U).equivMapOfInjective F.U.subtype F.U.subtype_injective).symm.trans e⟩

/-- Normality in the actual point centralizer places U in the chosen Sylow. -/
theorem closure_le_sylow [IsMulCommutative V]
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    F.U ≤ (T : Subgroup G) := by
  have hp : IsPGroup 2 F.U := IsPGroup.of_card (n := 6) s.core_shape.card
  have hc : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes hp F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)
  apply hc.trans
  have hcT := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
  change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hcT
  rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)] at hcT

/-- The cyclic center is TI in G, using the literal normalizer of the flag point. -/
theorem center_TI (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) : IsTISubgroup F.ZU := by
  let := h.chosen.elementary
  obtain ⟨e⟩ := center_model F s
  let := e.isCyclic.mpr inferInstance
  have hc : Nat.card F.ZU = 4 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 4
  exact cyclic_two_TI_of_point_normalizer F.ZU (F.Vi 1)
    (IsPGroup.of_card (n := 2) hc) (by simpa using F.card 1 (by decide))
    (F.point_le_ZU (by decide)) F.H_normalizes_ZU

/-- The source L-span, kept distinct from the still-to-be-identified O₂(L). -/
def centerSpan (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G :=
  conjugateSpanBy F.ZU L

/-- The original action kernel contains the entire center span. -/
theorem centerSpan_le_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    centerSpan L F ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := h.chosen.elementary
  have hz : F.ZU ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← h.centralizer_LT_at structural]
    exact le_inf ((map_subtype_le (center F.U)).trans
      ((closure_le_sylow F s).trans le_sup_right))
      ((centerIn_le_centralizer F.U).trans (centralizer_le (le_conjugateSpanBy V F.H)))
  exact conjugateSpanBy_le hz (le_sup_left.trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))

/-- I.7.5 makes the original L-conjugates of Z(U) commute. -/
theorem centerSpan_abelian
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    IsMulCommutative (centerSpan L F) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hPQ : centerSpan L F ≤ Q := centerSpan_le_core h structural F s
  have hZQ : F.ZU ≤ Q := (le_conjugateSpanBy F.ZU L).trans hPQ
  obtain ⟨e⟩ := center_model F s
  let := e.isCyclic.mpr inferInstance
  have hc : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  let := conjugateSpanIn_abelian_of_cyclic_four hc (center_TI h F s)
    (isPGroup_pCoreIn 2 _) hZQ
  have hle : centerSpan L F ≤ conjugateSpanIn F.ZU Q := by
    apply (closure_le _).mpr
    rintro _ ⟨l, hl, z, hz, rfl⟩
    apply conjugate_le_conjugateSpanIn l ?_ (mem_map_of_mem _ hz)
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hPQ (subset_closure ⟨l, hl, a, ha, rfl⟩)
  refine ⟨⟨fun a b => (inclusion_injective hle) ?_⟩⟩
  simp only [map_mul, mul_comm]

/-- Every nonzero vector of the original seed is a conjugate of the central point. -/
theorem seed_le_centerSpan
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) : V ≤ centerSpan L F := by
  let := h.chosen.elementary
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
    intro he; simp [he] at hc)
  intro v hv
  by_cases hv1 : v = 1
  · exact hv1 ▸ (centerSpan L F).one_mem
  obtain ⟨l, hl, he⟩ := h.vector_transitive (F.le_seed 1 z.property) hv
    (fun he => hz (Subtype.ext he)) hv1
  exact subset_closure ⟨l, hl, z, F.point_le_ZU (by decide) z.property, he⟩

/-- Squaring the original cyclic center gives exactly the flag point. -/
theorem center_squares_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    (centralSquares F.U).map F.U.subtype = F.Vi 1 := by
  let := h.chosen.elementary
  obtain ⟨e⟩ := s.core_shape.center_model
  let := e.isCyclic.mpr inferInstance
  have hc : Nat.card (center F.U) = 4 :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · intro v hv
    obtain ⟨z, hz, he⟩ := F.point_le_ZU (by decide) hv
    refine ⟨z, (mem_centralSquares_iff hc z).mpr ⟨hz, ?_⟩, he⟩
    apply Subtype.ext
    change (z : G) ^ 2 = 1
    change (z : G) = v at he
    rw [he]
    exact elemPow_eq_one_of_isElementaryAbelian v (F.le_seed 1 hv)
  · rw [card_map_of_injective F.U.subtype_injective, centralSquares_card hc]
    exact (show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)).ge

/-- All squares in the original L-span lie in V. -/
theorem centerSpan_square_mem_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    {x : G} (hx : x ∈ centerSpan L F) : x ^ 2 ∈ V := by
  let := centerSpan_abelian h structural F s
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, z, hz, rfl⟩ := hx
    have hz2 : z ^ 2 ∈ F.Vi 1 := by
      rw [← center_squares_eq_point h F s]
      obtain ⟨a, ha, rfl⟩ := hz
      exact ⟨a ^ 2, mem_centralSquares.mpr ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    have hm := (mem_normalizer_iff.mp (h.chosen.normalizes hl) (z ^ 2)).mp
      (F.le_seed 1 hz2)
    simpa only [← MulAut.conj_apply, ← map_pow] using hm
  | one => simp
  | mul x y hx hy hx2 hy2 =>
    have hxy : Commute x y := by
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : centerSpan L F) ⟨y, hy⟩)
    rw [hxy.mul_pow]
    exact V.mul_mem hx2 hy2
  | inv x _ hx => simpa only [inv_pow] using V.inv_mem hx

/-- Every original seed vector is an actual square in the L-span. -/
theorem seed_exists_centerSpan_square
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    {v : G} (hv : v ∈ V) : ∃ x ∈ centerSpan L F, x ^ 2 = v := by
  by_cases hv1 : v = 1
  · exact ⟨1, (centerSpan L F).one_mem, by simp [hv1]⟩
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
    intro he; simp [he] at hc)
  have hzsq : (z : G) ∈ (centralSquares F.U).map F.U.subtype :=
    (center_squares_eq_point h F s).symm ▸ z.property
  obtain ⟨a, ha, hea⟩ := hzsq
  obtain ⟨b, rfl⟩ := mem_centralSquares.mp ha
  obtain ⟨l, hl, he⟩ := h.vector_transitive (F.le_seed 1 z.property) hv
    (fun he => hz (Subtype.ext he)) hv1
  refine ⟨l * (b.val : G) * l⁻¹, subset_closure
    ⟨l, hl, b.val, mem_map_of_mem F.U.subtype b.property, rfl⟩, ?_⟩
  calc
    (l * (b.val : G) * l⁻¹) ^ 2 = l * (b.val : G) ^ 2 * l⁻¹ :=
      (map_pow (MulAut.conj l) _ 2).symm
    _ = v := by rw [show (b.val : G) ^ 2 = z from hea, he]

/-- The source span has exponent four, with its square image equal to V. -/
theorem centerSpan_exponent_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (x : centerSpan L F) : x ^ 4 = 1 := by
  let := h.chosen.elementary
  apply Subtype.ext
  change (x : G) ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact elemPow_eq_one_of_isElementaryAbelian _
    (centerSpan_square_mem_seed h structural F s x.property)

/-- The literal square map onto the original natural module. -/
theorem centerSpan_square_map
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    ∃ f : centerSpan L F →* V, Function.Surjective f ∧
      ∀ x : centerSpan L F, (f x : G) = (x : G) ^ 2 := by
  let := centerSpan_abelian h structural F s
  let f : centerSpan L F →* V :=
    ((centerSpan L F).subtype.comp (powMonoidHom 2)).codRestrict V
      (fun x => centerSpan_square_mem_seed h structural F s x.property)
  refine ⟨f, ?_, fun _ => rfl⟩
  intro v
  obtain ⟨x, hx, he⟩ := seed_exists_centerSpan_square h F s v.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- The actual Frattini subgroup of the span is the original V. -/
theorem centerSpan_frattini
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    (frattini (centerSpan L F)).map (centerSpan L F).subtype = V := by
  have hp : IsPGroup 2 (centerSpan L F) :=
    (isPGroup_pCoreIn 2 _).to_le (centerSpan_le_core h structural F s)
  apply le_antisymm
  · rw [map_le_iff_le_comap, hp.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact centerSpan_square_mem_seed h structural F s x.property
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := seed_exists_centerSpan_square h F s hv
    let : Fact (IsPGroup 2 (centerSpan L F)) := ⟨hp⟩
    exact ⟨(⟨x, hx⟩ : centerSpan L F) ^ 2,
      pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
