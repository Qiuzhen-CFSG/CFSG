module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RankTwoExclusion
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Centralization and exclusion of the rank-two fixed kernel

Once generation has given R = VU₀, the bound |U₀| ≤ 4 makes U₀/V₁
have order at most two. The original Q normalizes both terms, so [U₀,Q] ≤ V₁.
Since Q centralizes V, [R,Q] ≤ V₁. Both R and Q are L-invariant, whereas
no nontrivial subgroup of V₁ is L-invariant. Consequently [R,Q] = 1.
In particular R ≤ Z(Q) when the earlier setup places U in Q.

The final application supplies the centralization, elementary abelianness,
Sylow placement and normalizer premises of the existing rank-two exclusion.
The two generation conclusions R = VU₀ and [R,L] ≤ V remain explicit here;
they are not assumed by a theorem advertised as the complete 14.7.72.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076,
combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

/-- Commutators in V make VU₀ invariant, so it already equals the full span. -/
theorem R_eq_join_of_commutator_le (hcomm : ⁅R d,L⁆ ≤ V) : R d = V ⊔ d.U₀ := by
  have hJR : V ⊔ d.U₀ ≤ R d := sup_le (V_le_R d) (U₀_le_R d)
  have hNJ : L ≤ normalizer (V ⊔ d.U₀ : Subgroup G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hJR le_rfl).trans (hcomm.trans le_sup_left))
  exact le_antisymm (conjugateSpanBy_le le_sup_right hNJ) hJR

/-- The rank bound already bounds the Q-displacements by the original point. -/
theorem U₀_commutator_Q_le_point (hbound : Nat.card d.U₀ ≤ 4) :
    ⁅d.U₀, Q T L⁆ ≤ F.Vi 1 := by
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) d.U₀ bot_le d.point_le_U₀
  simp only [relIndex_bot_left, hcard] at hprod
  have hn : (F.Vi 1).relIndex d.U₀ ≠ 0 :=
    ((F.Vi 1).subgroupOf d.U₀).index_ne_zero_of_finite
  have hQP : Q T L ≤ normalizer (F.Vi 1 : Set G) :=
    (Q_le_H F).trans (d.H_centralizes_point.trans (Subgroup.centralizer_le_normalizer _))
  have hQU : Q T L ≤ normalizer (d.U₀ : Set G) :=
    (Q_le_H F).trans d.H_normalizes_U₀
  have hi : (F.Vi 1).relIndex d.U₀ = 1 ∨ (F.Vi 1).relIndex d.U₀ = 2 := by omega
  rcases hi with hi | hi
  · exact (commutator_mono (relIndex_eq_one.mp hi) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hQP)
  · exact commutator_le_of_normalized_index_two _ _ _ d.point_le_U₀ hi hQU hQP

/-- Generation and the rank bound force centralization in the original Q. -/
theorem R_centralizes_Q (hgen : R d = V ⊔ d.U₀)
    (hbound : Nat.card d.U₀ ≤ 4) : R d ≤ centralizer (Q T L : Set G) := by
  have hRU : R d ≤ F.U := hgen.le.trans (sup_le (Data.V_le_U F) d.U₀_le_U)
  have hRP : R d ≤ normalizer (F.Vi 1 : Set G) :=
    (hRU.trans d.conjugationSection.section_le).trans
      (d.H_centralizes_point.trans (Subgroup.centralizer_le_normalizer _))
  have hVQ : ⁅V,Q T L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp d.natural.chosen.core_centralizes)
  have hpre : R d ≤ commutatorPreimage (R d) (Q T L) (F.Vi 1) := by
    rw [hgen]
    exact sup_le (le_commutatorPreimage le_sup_left (hVQ.le.trans bot_le))
      (le_commutatorPreimage le_sup_right (U₀_commutator_Q_le_point d hbound))
  have hcomm : ⁅R d,Q T L⁆ ≤ F.Vi 1 :=
    (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hRP)
  have hLQ : L ≤ normalizer (Q T L : Set G) :=
    le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  have hnormal : L ≤ normalizer (⁅R d,Q T L⁆ : Subgroup G) := by
    intro l hl
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (L_normalizes_R d hl),
      mem_normalizer_iff_map_conj_eq.mp (hLQ hl)]
  exact commutator_eq_bot_iff_le_centralizer.mp
    (eq_bot_of_normalized_le_point d _ hcomm hnormal)

/-- This is the literal center of Q, not a center of an actor quotient. -/
theorem R_le_center_Q (hgen : R d = V ⊔ d.U₀)
    (hbound : Nat.card d.U₀ ≤ 4) (hUQ : F.U ≤ Q T L) :
    R d ≤ (center (Q T L)).map (Q T L).subtype := by
  have hRQ : R d ≤ Q T L := hgen.le.trans ((sup_le (Data.V_le_U F) d.U₀_le_U).trans hUQ)
  intro r hr
  refine ⟨⟨r,hRQ hr⟩, mem_center_iff.mpr (fun q => ?_), rfl⟩
  exact Subtype.ext (R_centralizes_Q d hgen hbound hr q q.property)

/-- The source generator bound puts the original U₀ at the flag point.
Only the preceding generation identities and earlier local setup remain. -/
theorem U₀_eq_point_of_generation
    (earlier : d.ModuleSeparation)
    (hgen : R d = V ⊔ d.U₀) (hcomm : ⁅R d,L⁆ ≤ V)
    (hbound : Nat.card d.U₀ ≤ 4) (hUQ : F.U ≤ Q T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hL₁K : F.Li L 1 ≤ K F)
    (hVfix : V ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    d.U₀ = F.Vi 1 := by
  let := d.U_elementary
  let : IsElementaryAbelian 2 (R d) :=
    IsElementaryAbelian.of_le (hgen.le.trans (sup_le (Data.V_le_U F) d.U₀_le_U))
  have hQT : Q T L ≤ (T : Subgroup G) := by
    exact (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hcore : L.pCoreIn 2 ≤ Q T L := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans le_sup_left)
    exact (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  apply source_U₀_eq_point_of_generation d earlier (R d) hgen hbound
    (d.U₀_le_U.trans (hUQ.trans hQT)) (L_normalizes_R d) hcore
    (R_centralizes_Q d hgen hbound) hcomm ((F.Li_le L 1).trans inf_le_left)
    (le_centralizer_iff.mp (hL₁K.trans d.K_centralizes_U₀)) hVfix hTL
    (T_normalizes_R d hTL) h68
  intro hLH
  exact not_L_normalizes_point d
    (hLH.trans (d.H_centralizes_point.trans (Subgroup.centralizer_le_normalizer _)))

/-- The generation branch need only deliver [R,L] ≤ V: the join identity,
centralization and collapse of the original fixed kernel are then proved here. -/
theorem fixed_kernel_and_span
    (earlier : d.ModuleSeparation)
    (hcomm : ⁅R d,L⁆ ≤ V)
    (hbound : Nat.card d.U₀ ≤ 4) (hUQ : F.U ≤ Q T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hL₁K : F.Li L 1 ≤ K F)
    (hVfix : V ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    d.U₀ = F.Vi 1 ∧ R d = V := by
  have hgen := R_eq_join_of_commutator_le d hcomm
  have hp := U₀_eq_point_of_generation d earlier hgen hcomm hbound hUQ hTL hL₁K hVfix h68
  exact ⟨hp, by rw [hgen, hp, sup_eq_left.mpr (F.le_seed 1)]⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
