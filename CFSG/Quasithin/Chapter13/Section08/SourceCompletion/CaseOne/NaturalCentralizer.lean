module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalKernel
public import CFSG.Quasithin.Chapter13.Section07.TranspositionImage

/-!
# The original centralizer intersections in the natural case-one branch

The realized natural action sends H_C into the pointwise fixer of the
seed hyperplane, of order two. Its kernel is O₂(LT) on the source Sylow;
that invariant core lies in every chosen conjugate Hˡ. Consequently H_C
and V_H meet Hˡ in index at most two. Normalization and the exact kernel
U_Hˡ∩O₂(H)=V₃ˡ put the corresponding commutators inside V₃ˡ≤V.

The actual source application combines these bounds with the constructed
conjugator, its marked even radical O₂(L₁*), and the two-element quotient
VU_H/U_H. The later constituent and chief-factor comparison is still
required to exclude the nonabelian branch; the complete source exclusion
and terminal application remain with SourceCompletion.CaseOne.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 13.8.33, printed pp.966--967, using 13.7.3(2),(3),(7).
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem centralizer_le_local_core
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    Source.HC H V₃ ≤ Source.QH H := by
  apply le_trans _ h.kernel_UH_eq_QH.le
  intro x hx
  exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hx.1, fun u hu => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
    exact V₁.one_mem⟩

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The seed hyperplane fixer bounds the index in H_C of the original
O₂(LT), without assuming that V_H or U_L is nonabelian. -/
theorem centralizer_global_core_index_le_two
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    ((L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).relIndex (Source.HC H V₃) ≤ 2 := by
  rw [Section07.core_relIndex_eq_image_card (localNaturalSetup d) h _
    ((centralizer_le_local_core h).trans h.QH_le_T)]
  obtain ⟨t, ht, htf⟩ := Section07.source_hyperplane_fixer (localNaturalSetup d)
  have hi : ((Source.HC H V₃).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d)) ≤ zpowers t := by
    rintro _ ⟨x, hx, rfl⟩
    rcases htf x ((centralizer_le (le_conjugateSpanBy V₃ H)) hx.2) with he | he
    · rw [he]; exact one_mem _
    · rw [he]; exact mem_zpowers _
  have hc := Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)
  rwa [Nat.card_zpowers, ht.orderOf] at hc

/-- H_C and its subgroup V_H meet the literal conjugate local group in
index at most two. The invariant global core lies in that conjugate. -/
theorem centralizer_conjugate_indices
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (l : L) :
    (Source.HC H V₃ ⊓ H.conjBy (l : G)).relIndex (Source.HC H V₃) ≤ 2 ∧
    (Source.VH H V ⊓ H.conjBy (l : G)).relIndex (Source.VH H V) ≤ 2 := by
  let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    have hsc : (T : Subgroup G) ⊓ centralizer (V : Set G) = Q := h.sylow_centralizer
    rw [← hsc]
    exact inf_le_left
  have hQn : (L ⊔ (T : Subgroup G) : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have he : Q.conjBy (l : G) = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hQn (mem_sup_left l.property))
  have hQHl : Q ≤ H.conjBy (l : G) := by
    rw [← he]
    exact map_mono (hQT.trans h.T_le_H)
  have hi : (H.conjBy (l : G)).relIndex (Source.HC H V₃) ≤ 2 :=
    (relIndex_le_of_le_left hQHl index_ne_zero_of_finite).trans
      (centralizer_global_core_index_le_two d h)
  rw [inf_relIndex_left, inf_relIndex_left]
  exact ⟨hi, (relIndex_le_of_le_right
    (Section07.VH_centralizes_UH (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance))
    index_ne_zero_of_finite).trans hi⟩

/-- The exact kernel bounds both source commutators by the actual
conjugate seed. This gives centralization on H_C/V_H and at most a line
of movement on V_H/U_H, on their index-at-most-two intersections. -/
theorem conjugate_seed_commutator_bounds
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (l : L) (hlH : (Source.UH H V₃).conjBy (l : G) ≤ H)
    (hk : (Source.UH H V₃).conjBy (l : G) ⊓ Source.QH H = V₃.conjBy (l : G)) :
    ⁅(Source.UH H V₃).conjBy (l : G), Source.HC H V₃ ⊓ H.conjBy (l : G)⁆ ≤
      V₃.conjBy (l : G) ∧
    ⁅(Source.UH H V₃).conjBy (l : G), Source.HC H V₃ ⊓ H.conjBy (l : G)⁆ ≤ Source.VH H V ∧
    ⁅(Source.UH H V₃).conjBy (l : G), Source.VH H V ⊓ H.conjBy (l : G)⁆ ≤ V := by
  have hHC : H ≤ normalizer (Source.HC H V₃ : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy V₃ H).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hUn : H.conjBy (l : G) ≤ normalizer ((Source.UH H V₃).conjBy (l : G) : Set G) :=
    (map_mono (le_normalizer_conjugateSpanBy V₃ H)).trans (le_normalizer_map _)
  have hc : ⁅(Source.UH H V₃).conjBy (l : G), Source.HC H V₃ ⊓ H.conjBy (l : G)⁆ ≤
      V₃.conjBy (l : G) := by
    rw [← hk]
    apply le_inf (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hUn))
    exact ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hlH.trans hHC))).trans (centralizer_le_local_core h)
  have hV : V.conjBy (l : G) = V :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizes_V (mem_sup_left l.property))
  have hpV : V₃.conjBy (l : G) ≤ V := (map_mono d.seed_le).trans hV.le
  refine ⟨hc, (hc.trans hpV).trans (le_conjugateSpanBy V H), ?_⟩
  exact ((commutator_mono le_rfl (inf_le_inf_right _
    (Section07.VH_centralizes_UH (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)))).trans hc).trans hpV

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The source seed intersection gives the literal two-element image
of V in VU_H/U_H. Relative normality is only taken inside that join. -/
theorem case_one_quotient_line
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    (Source.UH H V₃).relIndex (Source.UH H V₃ ⊔ V) = 2 := by
  let U := Source.UH H V₃
  let J := U ⊔ V
  have hn : J ≤ normalizer (U : Set G) :=
    sup_le U.le_normalizer (h.V_le_H.trans (le_normalizer_conjugateSpanBy V₃ H))
  let : (U.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hn
  have hi := relIndex_sup_left (V.subgroupOf J) (U.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  change U.relIndex J = U.relIndex V at hi
  rw [hi, ← inf_relIndex_left, seed_intersection d h c hDH hDg]
  have hVc : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  have hc := (V₃.subgroupOf V).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe d.seed_le).toEquiv, d.seed_card, hVc] at hc
  change 8 * V₃.relIndex V = 16 at hc
  omega

/-- The actual nonabelian source branch supplies one conjugator with the
exact radical, both index bounds and both commutator bounds. In particular
all groups here use the same source point and the same star marking. -/
theorem exists_nonabelian_local_action
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (hmark : (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2) :
    ∃ l : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left l)) ^ 2 = 1 ∧
      ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      (Source.UH H V₃).conjBy (l : G) ⊓ Source.QH H = V₃.conjBy (l : G) ∧
      (Source.UH H V₃).conjBy (l : G) ⊓ V = V₃.conjBy (l : G) ∧
      Nat.card (Source.starImage H ((Source.UH H V₃).conjBy (l : G))) = 4 ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) =
        (Source.starImage H (sourceOne L T V₁)).pCoreIn 2 ∧
      (Source.HC H V₃ ⊓ H.conjBy (l : G)).relIndex (Source.HC H V₃) ≤ 2 ∧
      (Source.VH H V ⊓ H.conjBy (l : G)).relIndex (Source.VH H V) ≤ 2 ∧
      ⁅(Source.UH H V₃).conjBy (l : G), Source.HC H V₃ ⊓ H.conjBy (l : G)⁆ ≤
        V₃.conjBy (l : G) ∧
      ⁅(Source.UH H V₃).conjBy (l : G), Source.HC H V₃ ⊓ H.conjBy (l : G)⁆ ≤ Source.VH H V ∧
      ⁅(Source.UH H V₃).conjBy (l : G), Source.VH H V ⊓ H.conjBy (l : G)⁆ ≤ V ∧
      (Source.UH H V₃).relIndex (Source.UH H V₃ ⊔ V) = 2 := by
  obtain ⟨l, hs, hp, hlH, hk, hi, hc, hrad⟩ :=
    exists_nonabelian_core_image d h c hH hDH hDg hcentral a e model hn hmark
  obtain ⟨hCi, hVi⟩ := centralizer_conjugate_indices d h l
  obtain ⟨hCs, hCV, hVV⟩ := conjugate_seed_commutator_bounds d h l hlH hk
  exact ⟨l, hs, hp, hlH, hk, hi, hc, hrad, hCi, hVi, hCs, hCV, hVV,
    case_one_quotient_line d h c hDH hDg⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
