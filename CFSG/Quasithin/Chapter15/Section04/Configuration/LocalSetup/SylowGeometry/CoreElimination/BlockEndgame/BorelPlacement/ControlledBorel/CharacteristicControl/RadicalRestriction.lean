module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.Setup
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.PRadical
public import CFSG.Quasithin.ChapterC.Section02

/-!
# Restricting the contrary radical to the first-block product

For R = O₂(XU) and D = K₁R, prove that R is radical in D and hence
O₂(D) ≤ R. This establishes the instance of C.2.2(3) needed in the
exchanged-block case directly from the actual contrary Sylow geometry.

Relative subnormality supplies U ∩ K₁ as a Sylow subgroup of K₁. Since R
normalizes K₁, (U ∩ K₁)R is Sylow in D, so U ∩ D is Sylow there. Both U
and X normalize R. Also X ≤ K₁K₂ and the two blocks commute, so X
normalizes D and N_D(R). Thus Q = O₂(N_D(R)) lies in U and is normalized
by X. The section-kernel identity R = U ∩ C_{XU}(X/O₂(X)) places Q in R:
[X,Q] lies in Q ∩ X ≤ O₂(X). The reverse inclusion is normality of R in
its normalizer. Transporting this equality to D permits C.2.1(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.2.1–2, printed pp.143–144; the restriction in the proof of C.2.7,
p.146; and the proof of 15.4.20, p.1164.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable (c : ContraryData κ d i j)

omit [Finite G] in
private theorem core_normalized (D : Subgroup G) :
    D ≤ normalizer (D.pCoreIn 2 : Set G) :=
  D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))

private theorem upper_two : IsPGroup 2 c.U := by
  rw [← c.sylow_image]
  exact c.sylow.isPGroup'.map _

-- X-normalized subgroups of U act trivially on the section X/O₂(X).
private theorem le_contraryCore_of_le_U_of_X_normalizes (Q : Subgroup G)
    (hQU : Q ≤ c.U) (hXQ : d.wholeX ≤ normalizer (Q : Set G)) :
    Q ≤ contraryCore c := by
  have hUX : c.U ≤ normalizer (d.wholeX : Set G) :=
    c.upper_lt.le.trans c.T_le_M₁
  have hQcore : Q ⊓ d.wholeX ≤ d.wholeX.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((upper_two c).to_le (inf_le_left.trans hQU)) inf_le_right
      ((le_inf hXQ d.wholeX.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hQC : Q ≤ ChapterA.Section04.twoSectionCentralizer d.wholeX (d.wholeX ⊔ c.U) := by
    apply (ChapterA.Section04.le_twoSectionCentralizer_iff _ _ _).mpr
    refine ⟨hQU.trans le_sup_right, hQU.trans hUX, ?_⟩
    exact (le_inf (le_normalizer_iff_commutator_le_right.mp hXQ)
      (le_normalizer_iff_commutator_le_left.mp (hQU.trans hUX))).trans hQcore
  change Q ≤ (d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2
  rw [contrary_core_eq_section_kernel le_sup_left le_sup_right
    (sup_le c.X_le_H (c.sylow_image ▸ map_subtype_le (c.sylow : Subgroup c.H)))
    (sup_le d.wholeX.le_normalizer hUX) c.sylow c.sylow_image]
  exact le_inf hQU hQC

private theorem block_join_sylow (b : ExchangedBlock c) :
    ∃ S : Sylow 2 (b.first ⊔ contraryCore c : Subgroup G),
      (S : Subgroup (b.first ⊔ contraryCore c : Subgroup G)).map
        (b.first ⊔ contraryCore c : Subgroup G).subtype =
          c.U ⊓ (b.first ⊔ contraryCore c) := by
  let T := (c.U ⊓ b.first) ⊔ contraryCore c
  have hTU : T ≤ c.U := sup_le inf_le_left (contraryCore_le_U c)
  have hnT : T ≤ normalizer (b.first : Set G) :=
    sup_le (inf_le_right.trans b.first.le_normalizer) b.core_normalizes
  obtain ⟨S, hS⟩ := exists_first_sylow b
  have hST : (S : Subgroup b.first).map b.first.subtype ≤ T := by
    rw [hS, subgroupOf_map_subtype]
    exact le_sup_left
  have hjoin : b.first ⊔ T = b.first ⊔ contraryCore c := by
    dsimp only [T]
    rw [← sup_assoc, sup_eq_left.mpr (show c.U ⊓ b.first ≤ b.first from inf_le_right)]
  have hex := IsPGroup.exists_sylow_sup_of_coprime_index b.first T
    ((upper_two c).to_le hTU) hnT (S : Subgroup b.first) S.not_dvd_index hST
  rw [hjoin] at hex
  obtain ⟨P, hP⟩ := hex
  exact ⟨P, (inf_eq_sylow_map P (upper_two c) (hP ▸ hTU)).symm⟩

private theorem X_normalizes_block_join (b : ExchangedBlock c)
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥) :
    d.wholeX ≤ normalizer ((b.first ⊔ contraryCore c : Subgroup G) : Set G) := by
  have hXL : d.wholeX ≤ normalizer (b.first : Set G) := by
    apply (ContraryData.X_le_K c).trans
    rw [← b.product]
    exact sup_le b.first.le_normalizer
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hXR : d.wholeX ≤ normalizer (contraryCore c : Set G) :=
    le_sup_left.trans (core_normalized _)
  exact (le_inf hXL hXR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem block_normalizer_core (b : ExchangedBlock c)
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥) :
    ((b.first ⊔ contraryCore c) ⊓ normalizer (contraryCore c : Set G)).pCoreIn 2 =
      contraryCore c := by
  let D := b.first ⊔ contraryCore c
  let N := D ⊓ normalizer (contraryCore c : Set G)
  have hUR : c.U ≤ normalizer (contraryCore c : Set G) :=
    le_sup_right.trans (core_normalized _)
  have hXR : d.wholeX ≤ normalizer (contraryCore c : Set G) :=
    le_sup_left.trans (core_normalized _)
  obtain ⟨S, hS⟩ := block_join_sylow c b
  have hSN : (S : Subgroup D).map D.subtype ≤ N :=
    hS.le.trans (le_inf inf_le_right (inf_le_left.trans hUR))
  have hQN : N.pCoreIn 2 ≤ c.U := by
    have h := pCoreIn_le_sylow N (restrictSylow S inf_le_left hSN)
    rw [restrictSylow_image, hS] at h
    exact h.trans inf_le_left
  have hXN : d.wholeX ≤ normalizer (N : Set G) :=
    (le_inf (X_normalizes_block_join c b hc)
      (hXR.trans (normalizer (contraryCore c : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · exact le_contraryCore_of_le_U_of_X_normalizes c _ hQN
      (hXN.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      (le_inf le_sup_right le_normalizer) inf_le_right

/-- C.2.2(3) for the actual first-block product: the contrary core remains
radical after restriction, using the commuting exchanged blocks. -/
theorem contraryCore_radical_in_block (b : ExchangedBlock c)
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥) :
    IsPRadical 2 ((contraryCore c).subgroupOf (b.first ⊔ contraryCore c)) := by
  let D := b.first ⊔ contraryCore c
  refine ⟨?_, ?_⟩
  · intro he
    have hm := congrArg (Subgroup.map D.subtype) he
    rw [map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_bot] at hm
    exact contraryCore_ne_bot c hm
  · change (normalizer ((contraryCore c).subgroupOf D : Set D)).pCoreIn 2 =
      (contraryCore c).subgroupOf D
    apply Subgroup.map_injective D.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ D.subtype D.subtype_injective,
      ← subgroupOf_normalizer_eq (show contraryCore c ≤ D from le_sup_right),
      subgroupOf_map_subtype, inf_comm (normalizer (contraryCore c : Set G)) D,
      block_normalizer_core c b hc, map_subgroupOf_eq_of_le le_sup_right]

/-- C.2.1(2) after the local radical restriction. -/
theorem blockRadicalCore_le_contraryCore (b : ExchangedBlock c)
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥) :
    blockRadicalCore b ≤ contraryCore c := by
  have hr := contraryCore_radical_in_block c b hc
  have h := ChapterC.twoCore_le_radical _ hr.isPGroup hr.2
  have hm := map_mono (f := (b.first ⊔ contraryCore c : Subgroup G).subtype) h
  rw [map_subgroupOf_eq_of_le le_sup_right] at hm
  exact hm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
