module

public import CFSG.Quasithin.Chapter13.Section07.NaturalAction
public import CFSG.Quasithin.Chapter13.Section07.ConjugateIntersections
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import Theory.Frattini.BinarySquares

/-!
# The first source consequences of the abelian V₃-span

The actual natural action proves [V,C_LT(V₃)]≤V₁. With F.9.1 and the
abelian U_H from 13.5.12, the F.9 kernel identity places V_H in O₂(H),
centralizes U_H, and puts its L-span in O₂(LT). The same calculation
bounds [V_H,V_H] by V₁; conjugate generators have order two, so the
Frattini subgroup is trivial or precisely V₁. The full H-centralizer of
U_H acts trivially on V_H/V₁ as well. The final literal 13.7.10 consumer
therefore no longer assumes either its core placement or centralizer bound.

F.9 applicability is the genuine 13.5.7 source obligation; abelianness of
U_H is the separate 13.5.12 recognition consequence. Neither V_H abelianness
nor the final 13.7.8 contradiction is assumed or established here.
Source: Aschbacher–Smith, 13.7.3(1–3),(5),(7) and 13.7.10(1),(6), pp.936,941–942.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

include d

/-- The original L acts transitively on the nonidentity vectors of V. -/
theorem natural_nonzero_transitive {x y : G} (hx : x ∈ V) (hy : y ∈ V)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ l ∈ L, l * x * l⁻¹ = y := by
  have hnx : (d.coordinate ⟨x, hx⟩).toAdd ≠ 0 := by
    intro h
    have he : (⟨x, hx⟩ : V) = 1 := d.coordinate.injective (h.trans (map_one d.coordinate).symm)
    exact hx1 (congrArg Subtype.val he)
  have hny : (d.coordinate ⟨y, hy⟩).toAdd ≠ 0 := by
    intro h
    have he : (⟨y, hy⟩ : V) = 1 := d.coordinate.injective (h.trans (map_one d.coordinate).symm)
    exact hy1 (congrArg Subtype.val he)
  obtain ⟨a, ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    _ _ hnx hny
  obtain ⟨q, hq⟩ := d.local_quotient.surjective a
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨l, l.property, ?_⟩
  have hc := d.conjugation l ⟨x, hx⟩
  rw [hl, hq] at hc
  have he : V.normalizerMonoidHom
      ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ ⟨x, hx⟩ = ⟨y, hy⟩ :=
    d.coordinate.injective (hc.trans ha)
  exact congrArg Subtype.val he


/-- 13.7.3(1): the actual V-span lies in O₂(H), using 13.7.2 only for U_H. -/
theorem VH_le_core (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH) : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH ≤ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).QH := by
  have huc : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH ≤ centralizer (V₃ : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr hU).trans
      (centralizer_le (le_conjugateSpanBy V₃ H))
  have hut : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH ≤ L ⊔ (T : Subgroup G) := h.UH_le_QH.trans (h.QH_le_T.trans le_sup_right)
  have hc : ⁅V, (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH⁆ ≤ V₁ :=
    (commutator_mono le_rfl (le_inf hut huc)).trans (NaturalAction.seed_centralizer_bound d)
  have hvq : V ≤ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).QH := by
    rw [commutator_comm] at hc
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro v hv
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨h.V_le_H hv, fun u hu =>
      hc (commutator_mem_commutator hu hv)⟩
  exact conjugateSpanBy_le hvq (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H))

/-- 13.7.3(2), retaining centralizers in the original ambient group. -/
theorem VH_centralizes_UH (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH) :
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH ≤ H ⊓ centralizer ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH : Set G) := by
  refine le_inf h.VH_le_H ?_
  apply conjugateSpanBy_le
    ((h.V_centralizes_UH_of_le_QH ((le_conjugateSpanBy V H).trans (VH_le_core d h hU))).trans
      inf_le_right)
  exact (le_normalizer_conjugateSpanBy V₃ H).trans (normalizer_le_normalizer_centralizer _)

/-- The seed-span and all its L-conjugates lie in the original O₂(LT). -/
theorem span_UH_L_le_core (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH) :
    conjugateSpanBy (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH L ≤ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  have huc : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mp
    exact (le_conjugateSpanBy V H).trans ((VH_centralizes_UH d h hU).trans inf_le_right)
  have huq : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH ≤ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).LT.pCoreIn 2 := by
    rw [← h.sylow_centralizer]
    exact le_inf (h.UH_le_QH.trans h.QH_le_T) huc
  apply conjugateSpanBy_le huq
  exact (le_sup_left.trans (L ⊔ (T : Subgroup G)).le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- Every V/V-conjugate commutator is in the literal line V₁. -/
theorem commutator_V_VH_le_point (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH) :
    ⁅V, (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH⁆ ≤ V₁ := by
  apply le_trans (commutator_mono le_rfl ?_) (NaturalAction.seed_centralizer_bound d)
  refine le_inf ((VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)) ?_
  exact ((VH_centralizes_UH d h hU).trans inf_le_right).trans
    (centralizer_le (le_conjugateSpanBy V₃ H))

omit d in
private theorem centralizer_UH_le_core (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    H ⊓ centralizer ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH : Set G) ≤ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).QH := by
  apply le_trans _ h.kernel_UH_eq_QH.le
  intro x hx
  exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hx.1, fun u hu => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
    exact V₁.one_mem⟩

omit d in
private theorem span_commutator_bound (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (B : Subgroup G)
    (hB : B ≤ H) (hn : H ≤ normalizer (B : Set G))
    (hc : ⁅V, B⁆ ≤ V₁) : ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH, B⁆ ≤ V₁ := by
  let : (V₁.subgroupOf H).Normal := h.point_normal
  let : (B.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hn
  have hnK : ((h.kernel B).subgroupOf H).Normal := by
    change ((centralizerModulo ⊤ (B.subgroupOf H) (V₁.subgroupOf H)).map
      H.subtype |>.comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact centralizerModulo_top_normal _ _
  have hNK : H ≤ normalizer (h.kernel B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp hnK
  have hvK : V ≤ h.kernel B := by
    rw [commutator_comm] at hc
    intro v hv
    exact (h.mem_kernel_iff hB).mpr ⟨h.V_le_H hv, fun b hb =>
      hc (commutator_mem_commutator hb hv)⟩
  have hspan : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH ≤ h.kernel B := conjugateSpanBy_le hvK hNK
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb v hv
  exact (h.mem_kernel_iff hB).mp (hspan hv) |>.2 b hb

/-- The common conclusion of both alternatives in 13.7.3(7), with the
actual H-centralizer; no local-placement or commutator conclusion is assumed. -/
theorem centralizer_UH_commutator (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    ⁅H ⊓ centralizer ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH : Set G), (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH⁆ ≤ V₁ := by
  rw [commutator_comm]
  apply span_commutator_bound h _ inf_le_left
    ((le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy V₃ H).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf)
  apply le_trans (commutator_mono le_rfl ?_) (NaturalAction.seed_centralizer_bound d)
  exact le_inf ((centralizer_UH_le_core h).trans (h.QH_le_T.trans le_sup_right))
    (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V₃ H)))

/-- The actual full V-span is abelian modulo the original point. -/
theorem commutator_VH_le_point (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH) :
    ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH, (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH⁆ ≤ V₁ :=
  span_commutator_bound h (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH h.VH_le_H (le_normalizer_conjugateSpanBy V H)
    (commutator_V_VH_le_point d h hU)

/-- Every element of the actual V-span squares into V₁. -/
theorem square_VH_mem_point (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH)
    {x : G} (hx : x ∈ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH) : x ^ 2 ∈ V₁ := by
  let := h.elementary
  have hcomm := commutator_VH_le_point d h hU
  refine closure_induction (fun y hy => ?_) ?_ (fun a b ha hb hpa hpb => ?_)
    (fun a _ hpa => ?_) hx
  · obtain ⟨g, _, v, hv, rfl⟩ := hy
    rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]
    exact V₁.one_mem
  · simp only [one_pow]
    exact V₁.one_mem
  · have hc := hcomm (commutator_mem_commutator ha hb)
    have hbN : b ∈ normalizer (V₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (h.H_centralizes (h.VH_le_H hb))
    have hn := (mem_normalizer_iff.mp hbN (a ^ 2)).mp hpa
    have he : (a * b) ^ 2 = ⁅a, b⁆ * (b * a ^ 2 * b⁻¹) * b ^ 2 := by
      simp only [commutatorElement_def, pow_two]
      group
    rw [he]
    exact V₁.mul_mem (V₁.mul_mem hc hn) hpb
  · rw [inv_pow]
    exact V₁.inv_mem hpa

/-- The intrinsic Frattini subgroup, embedded into G, lies in V₁. -/
theorem frattini_VH_le_point (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH) :
    (frattini (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH).map (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH.subtype ≤ V₁ := by
  have hp : IsPGroup 2 (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH := (pCore_isPGroup.map H.subtype).to_le (VH_le_core d h hU)
  rw [map_le_iff_le_comap, hp.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  exact square_VH_mem_point d h hU x.property

/-- 13.7.3(5): the nonabelian source span has precisely the original point
as its Frattini subgroup. -/
theorem abelian_or_frattini_eq_point (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) (hU : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH) :
    IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH ∨ (frattini (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH).map (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH.subtype = V₁ := by
  classical
  by_cases hc : IsMulCommutative (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH
  · exact Or.inl hc
  right
  have hf := frattini_VH_le_point d h hU
  have hp : IsPGroup 2 (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH := (pCore_isPGroup.map H.subtype).to_le (VH_le_core d h hU)
  let : Fact (IsPGroup 2 (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH) := ⟨hp⟩
  have hn : (frattini (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH).map (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH.subtype ≠ ⊥ := by
    intro he
    have he' : frattini (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH = ⊥ := by
      apply map_injective (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH.subtype_injective
      simpa only [Subgroup.map_bot] using he
    exact hc ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp he').toIsMulCommutative
  have hd : Nat.card ((frattini (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH).map (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH.subtype) ∣ 2 :=
    h.point_card ▸ card_dvd_of_le hf
  have hecard : Nat.card ((frattini (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH).map (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).VH.subtype) = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with ho | ho
    · exact (hn (eq_bot_of_card_eq _ ho)).elim
    · exact ho
  exact eq_of_le_of_card_ge hf (by rw [hecard, d.line_card])

/-- The actual 13.7.10 consumer: the original natural action discharges both
13.7.3 placement and centralizer inputs of the chosen-conjugator theorem. -/
theorem source_intersections_of_natural
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g) ^ 2 = 1)
    (hspan : V ≤ V₃ ⊔ ChapterF.Section09.Setup.conjugate V₁ (g : G))
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ¬ ChapterF.Section09.Setup.conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
    ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DH (g : G),
      ChapterF.Section09.Setup.conjugate (Section08.Source.UH H V₃) (g : G)⁆ = ⊥ ∧
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DHg (g : G) ≤
      H ⊓ centralizer (Section08.Source.UH H V₃ : Set G) ∧
    ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DH (g : G),
      ChapterF.Section09.Setup.conjugate (Section08.Source.VH H V) (g : G) ⊓
        (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2⁆ = ⊥ ∧
    ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DHg (g : G),
      Section08.Source.VH H V⁆ ≤ V₁ := by
  exact ConjugateIntersections.source_centralizer_conclusions h g hs
    ((le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)) hspan hU hV
    (centralizer_UH_commutator d h)

end CFSG.Quasithin.Chapter13.Section07
