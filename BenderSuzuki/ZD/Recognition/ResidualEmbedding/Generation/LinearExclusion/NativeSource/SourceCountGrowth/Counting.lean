module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountGrowth.Quotients
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus.Conjugates

/-!
# The first normalizer has exactly q²|U| elements

The M-conjugate TI family makes AU proper in V. The normalizer condition
therefore makes AU proper in R₁=N_V(AU). Coprime torus lifting gives
[R₁:AU]≥q, while the distinct R₁-conjugates of U all lie in AU and avoid A.
Counting their nonidentity elements gives [R₁:AU]≤q. No normality of R₁ in M
or involution census is used in this calculation.

Source: GLS IV, Chapter 2, Lemma 15.6, first paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
open scoped Pointwise
universe u

public theorem pgroup_lt_relative_normalizer
    {H : Type*} [Group H] [Finite H] {P W : Subgroup H}
    (hP : IsPGroup 2 P) (hWP : W < P) :
    W < P ⊓ normalizer (W : Set H) := by
  refine lt_of_le_of_ne (le_inf hWP.le le_normalizer) ?_
  intro he
  let : Group.IsNilpotent P := hP.isNilpotent
  have hn : normalizer (W.subgroupOf P : Set P) = W.subgroupOf P := by
    rw [← subgroupOf_normalizer_eq hWP.le]
    ext p
    exact ⟨fun hp => he.symm ▸ ⟨p.property, hp⟩,
      fun hp => le_normalizer hp⟩
  have ht := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := P)) _ hn
  exact hWP.ne (le_antisymm hWP.le (subgroupOf_eq_top.mp ht))

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "K" => residualCommutator M t
local notation "V" => pointCore M
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

public theorem sup_lt_pointCore (hs : CentralizerLocalTwoData d) : A ⊔ U < V := by
  have hle := sup_le (distinguished_le_pointCore d) (twoCore_le_pointCore d hs)
  refine lt_of_le_of_ne hle ?_
  intro he
  have hb := Census.pointCore_card_lower d hs
  rw [← he, sup_card d] at hb
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by have := d.parameter; omega) (by decide)
  have hr : 1 < Nat.card U :=
    (Subgroup.one_lt_card_iff_ne_bot U).mpr (twoCore_ne_bot d hs)
  have hrsub : Nat.card U - 1 + 1 = Nat.card U := Nat.sub_add_cancel (by omega)
  have hq2 : 2 ^ n < (2 ^ n) ^ 2 := by nlinarith
  have hm := Nat.mul_lt_mul_of_pos_right hq2 (show 0 < Nat.card U - 1 by omega)
  have heq : 2 ^ n * Nat.card U = 2 ^ n * (Nat.card U - 1) + 2 ^ n := by
    conv_lhs => rw [← hrsub]
    ring
  rw [heq] at hb
  omega

public theorem sup_lt_sourceNormalizer (hs : CentralizerLocalTwoData d) : A ⊔ U < R :=
  pgroup_lt_relative_normalizer ((pCore_isPGroup (p := 2) (G := M)).map M.subtype)
    (sup_lt_pointCore d hs)

public theorem sourceNormalizer_sup_index_lower (hs : CentralizerLocalTwoData d) :
    2 ^ n ≤ (A ⊔ U).relIndex R :=
  torus_section_index_lower d hs R (A ⊔ U) inf_le_left (sup_lt_sourceNormalizer d hs)
    inf_le_right le_sup_right (torus_normalizes_sourceNormalizer d hs) (torus_normalizes_sup d hs)

omit [Finite G] in
private theorem relative_conjugate_card (P W : Subgroup G) :
    Nat.card (Set.range fun p : P => W.conjBy (p : G)) =
      (normalizer (W : Set G)).relIndex P := by
  let : MulAction P (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp P.subtype)
  have hstab : MulAction.stabilizer P W = (normalizer (W : Set G)).subgroupOf P := by
    ext p
    exact mem_normalizer_iff_map_conj_eq.symm
  change Nat.card (MulAction.orbit P W) = _
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer P W), hstab]
  rfl

public theorem sourceNormalizer_sup_index_upper (hs : CentralizerLocalTwoData d) :
    (A ⊔ U).relIndex R ≤ 2 ^ n := by
  let F := Set.range fun r : R => (U).conjBy (r : G)
  let f : F → Census.conjugateFamily M z t := fun C => ⟨C.val, by
    obtain ⟨r, hr⟩ := C.property
    exact ⟨⟨r, sourceNormalizer_le_point r.property⟩, hr⟩⟩
  have hf : Function.Injective f := by
    intro C E he
    exact Subtype.ext (congrArg (fun C : Census.conjugateFamily M z t => C.val) he)
  have hc := Census.family_union_card A (A ⊔ U) (fun C : F => C.val) le_sup_left
    (fun C => by
      obtain ⟨r, hr⟩ := C.property
      rw [← hr]
      rintro x ⟨u, hu, rfl⟩
      exact (mem_normalizer_iff.mp r.property.2 u).mp
        ((show U ≤ A ⊔ U from le_sup_right) hu))
    (fun C => Census.conjugate_disjoint_distinguished d (f C))
    (fun C E hne => Census.conjugate_pairwise_disjoint d (f C) (f E)
      (fun he => hne (hf he)))
    (fun C => Census.conjugate_card (f C))
  have hnorm : R ⊓ normalizer (U : Set G) = A ⊔ U := by
    apply le_antisymm
    · exact (inf_le_inf inf_le_left le_rfl).trans (pointCore_inf_twoCore_normalizer d hs).le
    · refine le_inf (sup_le_sourceNormalizer d hs) ?_
      rw [← pointCore_inf_twoCore_normalizer d hs]
      exact inf_le_right
  have hfc : Nat.card F = (A ⊔ U).relIndex R := by
    rw [relative_conjugate_card, ← inf_relIndex_left, hnorm]
  rw [hfc, d.distinguished_elementary_card.2, sup_card d] at hc
  have hr : 1 < Nat.card U :=
    (Subgroup.one_lt_card_iff_ne_bot U).mpr (twoCore_ne_bot d hs)
  have hrsub : Nat.card U - 1 + 1 = Nat.card U := Nat.sub_add_cancel (by omega)
  have hmul : (A ⊔ U).relIndex R * (Nat.card U - 1) ≤ 2 ^ n * (Nat.card U - 1) := by
    have heq : 2 ^ n * Nat.card U = 2 ^ n * (Nat.card U - 1) + 2 ^ n := by
      conv_lhs => rw [← hrsub]
      ring
    rw [heq] at hc
    omega
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

public theorem sourceNormalizer_sup_index (hs : CentralizerLocalTwoData d) :
    (A ⊔ U).relIndex R = 2 ^ n :=
  le_antisymm (sourceNormalizer_sup_index_upper d hs) (sourceNormalizer_sup_index_lower d hs)

public theorem sourceNormalizer_card (hs : CentralizerLocalTwoData d) :
    Nat.card R = (2 ^ n) ^ 2 * Nat.card U := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊔ U) R bot_le
    (sup_le_sourceNormalizer d hs)
  simp only [relIndex_bot_left] at hc
  rw [sourceNormalizer_sup_index d hs, sup_card d] at hc
  rw [← hc]
  ring

end BenderSuzuki.ZD.LinearExclusion.SourceCount
