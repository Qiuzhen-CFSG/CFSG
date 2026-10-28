module

public import CFSG.Quasithin.ChapterG.Section10.Basic
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The low-rank specialization of G.11.1

The extra witness is an element of the original actor whose displacement
contains the marked point and has dimension at most two. Normality is relative
to a Sylow subgroup fixing that point, not normality in the whole group.
The odd point-stabilizer index identifies the source's local Sylow formulation
with the ambient Sylow formulation used by the consumers.

These are input definitions and their elementary consequences, not a
classification theorem. Source: Aschbacher--Smith G.11.1(3ii),(4), printed p.364.
-/

@[expose] public section
open Subgroup Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Exactly G.11.1(3ii); no assertion about the separate case (3i). -/
def LowRankWitness (ρ : Representation (ZMod 2) G V) (v : V) (X : Subgroup G) : Prop :=
  ∃ a ∈ X, finrank (ZMod 2) (RankTwo.movedSpace ρ a) ≤ 2 ∧
    v ∈ RankTwo.movedSpace ρ a

/-- G.11.1(4), with normality explicitly inside the chosen ambient Sylow. -/
def NormalSylow (ρ : Representation (ZMod 2) G V) (v : V) (X : Subgroup G) : Prop :=
  ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Section10.pointCentralizer ρ v ∧
    X ≤ S ∧ (X.subgroupOf (S : Subgroup G)).Normal

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The same relative normality can be supplied as a normalizer containment. -/
theorem normalSylow_iff_normalizer (ρ : Representation (ZMod 2) G V) (v : V)
    (X : Subgroup G) : NormalSylow ρ v X ↔
      ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Section10.pointCentralizer ρ v ∧
        X ≤ S ∧ (S : Subgroup G) ≤ normalizer (X : Set G) := by
  constructor
  · rintro ⟨S, hS, hX, hn⟩
    exact ⟨S, hS, hX, (normal_subgroupOf_iff_le_normalizer hX).mp hn⟩
  · rintro ⟨S, hS, hX, hn⟩
    exact ⟨S, hS, hX, (normal_subgroupOf_iff_le_normalizer hX).mpr hn⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- The local Sylow in the book and the ambient Sylow in applications are
identical subgroups after the actual inclusion of the point centralizer. -/
theorem normalSylow_iff_local (ρ : Representation (ZMod 2) G V) (v : V)
    (X : Subgroup G) (hodd : Odd (Section10.pointCentralizer ρ v).index) :
    NormalSylow ρ v X ↔
      ∃ S : Sylow 2 (Section10.pointCentralizer ρ v),
        X ≤ (S : Subgroup (Section10.pointCentralizer ρ v)).map
          (Section10.pointCentralizer ρ v).subtype ∧
        (X.subgroupOf ((S : Subgroup (Section10.pointCentralizer ρ v)).map
          (Section10.pointCentralizer ρ v).subtype)).Normal := by
  let C := Section10.pointCentralizer ρ v
  constructor
  · rintro ⟨S, hS, hX, hn⟩
    refine ⟨S.subtype hS, ?_, ?_⟩
    · change X ≤ ((S : Subgroup G).subgroupOf C).map C.subtype
      rwa [map_subgroupOf_eq_of_le hS]
    · change (X.subgroupOf (((S : Subgroup G).subgroupOf C).map C.subtype)).Normal
      rwa [map_subgroupOf_eq_of_le hS]
  · rintro ⟨S, hX, hn⟩
    let P := (S : Subgroup C).map C.subtype
    have hp : IsPGroup 2 P := S.isPGroup'.map C.subtype
    have hi : ¬ 2 ∣ P.index := by
      rw [Subgroup.index_map_subtype]
      exact Nat.Prime.not_dvd_mul Nat.prime_two S.not_dvd_index
        (by simpa only [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hodd))
    exact ⟨hp.toSylow hi, map_subtype_le _, hX, hn⟩

variable {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

omit [Finite G] in
/-- The nonzero marked point rules out the identity witness. -/
theorem LowRankWitness.exists_involution (hw : LowRankWitness ρ v X) (hv : v ≠ 0) :
    ∃ a ∈ X, orderOf a = 2 ∧
      0 < finrank (ZMod 2) (RankTwo.movedSpace ρ a) ∧
      finrank (ZMod 2) (RankTwo.movedSpace ρ a) ≤ 2 ∧
      v ∈ RankTwo.movedSpace ρ a := by
  obtain ⟨a, ha, hr, hm⟩ := hw
  have hne : a ≠ 1 := by
    rintro rfl
    exact hv (by simpa [RankTwo.movedSpace] using hm)
  have hpos : 0 < finrank (ZMod 2) (RankTwo.movedSpace ρ a) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hb := Submodule.finrank_eq_zero.mp hz
    rw [hb] at hm
    exact hv hm
  exact ⟨a, ha, orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne,
    hpos, hr, hm⟩

/-- In particular the original actor has positive rank; the rank-zero defect
of unrestricted G.9.4 cannot occur in this specialization. -/
theorem LowRankWitness.actor_rank_pos (hw : LowRankWitness ρ v X) (hv : v ≠ 0) :
    0 < finrank (ZMod 2) (Additive X) := by
  obtain ⟨a, ha, ho, _⟩ := hw.exists_involution hv
  have hX : X ≠ ⊥ := by
    intro he
    have h1 : a = 1 := mem_bot.mp (he ▸ ha)
    simp [h1] at ho
  let : Nontrivial X := X.nontrivial_iff_ne_bot.mpr hX
  exact Module.finrank_pos

/-- G.10.2 supplies the literal G.9 setup, without a Fitting or component
classification premise and without changing the given actor. -/
theorem setup (h : Section10.Hypothesis ρ B v W X X₀) :
    Section09.Setup ρ X (finrank (ZMod 2) (Additive X)) := by
  refine ⟨h.faithful, inferInstance, ?_, ?_⟩
  · change Nat.card (Additive X) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  · have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective X₀)).trans
      (IsElementaryAbelian.rank_le_finrank (p := 2) X)
    exact h.dimension_bound.1.trans (by omega)

end CFSG.Quasithin.ChapterG.Section11
