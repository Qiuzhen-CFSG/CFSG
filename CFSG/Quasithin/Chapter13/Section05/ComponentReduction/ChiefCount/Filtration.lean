module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Assembly.Chapter13
public import Theory.GroupTheory.NoncentralChiefRefinement

/-!
# The literal residual filtration for 13.5.22

Intersect the three G.2.4 layers with the original two-residual. The middle
section is central by G.2.4(5), and the final quotient above the local two-core
has order three. The marked map to the actual A₄ point stabilizer has kernel
S∩L₁. These facts leave precisely the orthogonal, natural and parabolic-core
sections to refine; they do not assume or assert a numerical chief count.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.22, printed p.924 (PDF p.941), using G.2.4, printed pp.334–335.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

omit [Finite G] in
/-- Containment of the embedded O²(N_L(V₁)), retaining the residual convention. -/
theorem residual_le_L (D : Setup G) : D.L₁ ≤ D.L :=
  (map_subtype_le _).trans inf_le_left

/-- V∩L₁, as a normal subgroup of the actual L₁. -/
def first (_d : Hypothesis D g) : NormalNode D.L₁ :=
  ⟨D.VL.subgroupOf D.L₁, normal_subgroupOf_of_le_normalizer
    ((residual_le_L D).trans (L_normalizes_VL D))⟩

/-- V(U∩Uᵍ)∩L₁; S₂ is the literal product layer of G.2.4. -/
def second (d : Hypothesis D g) : NormalNode D.L₁ :=
  ⟨(AlternatingFive.S₂ D g).subgroupOf D.L₁,
    normal_subgroupOf_of_le_normalizer (((residual_le_L D).trans d.L_le_I).trans
      (le_normalizer_iff_commutator_le_left.mpr
        ((d.second_commutator d.L_le_I).trans le_sup_left)))⟩

/-- S∩L₁, where S is the two-core of the generated group I. -/
def core (d : Hypothesis D g) : NormalNode D.L₁ :=
  ⟨(D.S g).subgroupOf D.L₁, normal_subgroupOf_of_le_normalizer
    (((residual_le_L D).trans d.L_le_I).trans (I_normalizes_core D g))⟩

/-- The local two-core, distinct from S∩L₁. -/
def localCore (D : Setup G) : NormalNode D.L₁ :=
  ⟨pCore 2 D.L₁, inferInstanceAs (pCore 2 D.L₁).Normal⟩

theorem first_le_second (d : Hypothesis D g) : first d ≤ second d :=
  comap_mono le_sup_left

theorem second_le_core (d : Hypothesis D g) : second d ≤ core d :=
  comap_mono (d.second_le_core d.L_le_I)

theorem core_le_localCore (d : Hypothesis D g) : core d ≤ localCore D :=
by
  change (core d).val ≤ pCore 2 D.L₁
  exact le_sSup ⟨(core d).property, (isPGroup_pCoreIn 2 (D.I g)).comap_subtype⟩

/-- The real normal filtration 1≤V∩L₁≤S₂∩L₁≤S∩L₁≤O₂(L₁). -/
def sourceFiltration (d : Hypothesis D g) : Filtration D.L₁ 4 where
  term := ![⊥, first d, second d, core d, localCore D]
  monotone := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    · exact bot_le
    · exact first_le_second d
    · exact second_le_core d
    · exact core_le_localCore d

/-- The centrality statement is about the actual restricted conjugation action. -/
theorem middle_central (d : Hypothesis D g) : IsCentral (first d) (second d) := by
  rw [isCentral_iff_commutator_le, commutator_le]
  intro x _ y hy
  have hc : ⁅D.I g, AlternatingFive.S₂ D g⁆ ≤ D.VL := by
    rw [commutator_comm]
    exact d.second_commutator d.L_le_I
  exact hc (commutator_mem_commutator
    (((residual_le_L D).trans d.L_le_I) x.property) hy)

/-- Every refinement of the central source interval contributes zero. -/
theorem middle_count_zero (d : Hypothesis D g) (t : ChiefSeries D.L₁)
    (h0 : t.head = first d) (h1 : t.last = second d) :
    t.noncentralTwoCount = 0 := by
  apply t.noncentralTwoCount_eq_zero_of_central
  rw [h0, h1]
  exact middle_central d

/-- The full Borel at the singular point derived from the original V₁. -/
noncomputable abbrev Borel (d : Hypothesis D g) :=
  MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex

/-- The literal star map on the local two-residual, with its marked A₄ image. -/
noncomputable def localProjection (d : Hypothesis D g) : D.L₁ →* Borel d :=
  (d.fiveAction.comp (inclusion (residual_le_L D))).codRestrict _ (fun x => by
    change d.fiveAction (inclusion (residual_le_L D) x) ∈
      MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex
    rw [← d.local_fiveAction]
    exact mem_map.mpr ⟨inclusion (residual_le_L D) x, x.property, rfl⟩)

theorem localProjection_surjective (d : Hypothesis D g) :
    Function.Surjective (localProjection d) := by
  intro b
  have hb : b.val ∈ MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex := b.property
  rw [← d.local_fiveAction] at hb
  obtain ⟨x, hx, he⟩ := hb
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- Its kernel is S∩L₁, not the larger O₂(L₁). -/
theorem localProjection_kernel (d : Hypothesis D g) :
    (localProjection d).ker = (core d).val := by
  ext x
  change localProjection d x = 1 ↔ (x : G) ∈ D.S g
  rw [Subtype.ext_iff]
  change d.model (starProjection D (inclusion (residual_le_L D) x)) = 1 ↔ _
  rw [d.model.map_eq_one_iff, Subtype.ext_iff]
  let xLT : D.LT := ⟨x, ((residual_le_L D).trans le_sup_left) x.property⟩
  change QuotientGroup.mk' (pCore 2 D.LT) xLT = 1 ↔ _
  have hq : QuotientGroup.mk' (pCore 2 D.LT) xLT = 1 ↔
      xLT ∈ pCore 2 D.LT := QuotientGroup.eq_one_iff xLT
  rw [hq, d.S_eq_star_kernel]
  constructor
  · intro hx
    refine ⟨((residual_le_L D).trans d.L_le_I) x.property, ?_⟩
    exact mem_map.mpr ⟨_, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, he⟩ := hx.2
    exact (show y = xLT from
      Subtype.ext he) ▸ hy

/-- The residual core quotient has no two-chief factors; its order-three
calculation comes from the actual star map and its two-group kernel. -/
theorem terminal_no_two (d : Hypothesis D g) :
    HasNoTwoChiefFactors (D.L₁ ⧸ (localCore D).val) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A B hAB hp
  have hd : Nat.card (Section A B) ∣ 3 := by
    have h := (A.val.subgroupOf B.val).index_dvd_card.trans B.val.card_subgroup_dvd_card
    rw [index_eq_card] at h
    change Nat.card (Section A B) ∣ Nat.card (D.L₁ ⧸ pCore 2 D.L₁) at h
    rw [d.terminal_local_core_quotient_card d.earlierStructure] at h
    exact h
  have hcard : Nat.card (Section A B) = 1 := by
    rcases hp.card_eq_or_dvd with h | h
    · exact h
    · have := h.trans hd
      norm_num at this
  have hs : Subsingleton (Section A B) := Nat.card_eq_one_iff_unique.mp hcard |>.1
  have he : B.val ≤ A.val := subgroupOf_eq_top.mp (QuotientGroup.subsingleton_iff.mp hs)
  exact hAB.lt.not_ge he

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
