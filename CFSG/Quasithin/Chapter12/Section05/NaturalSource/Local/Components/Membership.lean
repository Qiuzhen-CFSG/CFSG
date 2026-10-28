module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Quotients
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# Local-family membership of the four exterior residuals

Each residual is perfect with a quasisimple two-core quotient. The aligned
Sylow subgroup normalizes it, so it is a C-component of its join with T.
The unchanged original V lies in that join's two-core and is nontrivial.
This proves all three clauses of the actual local-family definition.

The standard point lies in every Vᵢ, making every Gᵢ an actual two-local
subgroup; these facts feed the source containment theorem in Components.
Source: Aschbacher--Smith, notation and proof of 12.5.3, printed p.817.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)

theorem V₁_le_Vi (i : ℕ) (hi : LocalIndex i) : a.Vi 1 ≤ a.Vi i := by
  rcases hi with rfl | rfl | rfl | rfl
  · exact le_rfl
  · apply a.subspace_mono
    apply Submodule.span_mono
    apply Set.image_mono
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_singleton] at hj
    subst j
    decide
  · apply a.subspace_mono
    apply Submodule.span_mono
    apply Set.image_mono
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_singleton] at hj
    subst j
    decide
  · exact a.V₁_le_V₆

theorem Vi_ne_bot (i : ℕ) (hi : LocalIndex i) : a.Vi i ≠ ⊥ := by
  intro he
  exact a.z_ne_one (mem_bot.mp (he ▸ a.V₁_le_Vi i hi a.z_mem_V₁))

theorem Gi_twoLocal (i : ℕ) (hi : LocalIndex i) : IsTwoLocal (a.Gi i) := by
  let := D.elementary
  exact ⟨a.Vi i, a.Vi_ne_bot i hi,
    (IsElementaryAbelian.isPGroup 2 V).to_le (a.subspace_le _), rfl⟩
end ExteriorMarking

namespace SylowExteriorMarking
variable [Finite G] (s : SylowExteriorMarking D)

omit [Finite G] in
/-- This is O₂(LᵢT), not the two-core of the full normalizer Gᵢ. -/
theorem seed_le_Ri (i : ℕ) : V ≤ s.marking.Ri i := by
  let := D.elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (D.le_sylow.trans le_sup_right)
    ((sup_le_sup (s.marking.Li_le_L i) le_rfl).trans s.normalizes)

/-- Source local-family membership, with the original V witnessing nontrivial core. -/
theorem Li_mem_local (i : ℕ) (hi : LocalIndex i) :
    s.marking.Li i ∈ Chapter1.L G (T : Subgroup G) := by
  let B := s.marking.Li i
  let J := B ⊔ (T : Subgroup G)
  let A := B.subgroupOf J
  let : Group.IsPerfect B := s.marking.Li_perfect i
  let : IsQuasisimple (B ⧸ pCore 2 B) := s.marking.Li_core_quasisimple i hi
  have hp : IsPPerfect 2 B := by
    intro N hN hP
    let := hN
    by_contra hne
    let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hP.isNilpotent
  have ht : (⊤ : Subgroup B).IsCComponent :=
    isCComponent_top_of_isPPerfect_of_quasisimple_quotient (pCore 2 B) pCore_isPGroup hp
  let e : B ≃* A := (subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).symm
  have htA : (⊤ : Subgroup A).IsCComponent := by
    have he : (⊤ : Subgroup B).map e.toMonoidHom = ⊤ :=
      (MonoidHom.range_eq_map e.toMonoidHom).symm.trans
        (MonoidHom.range_eq_top.mpr e.surjective)
    exact he ▸ ht.map_equiv e
  have hn : A.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le B.le_normalizer (s.sylow_normalizes_Li i hi))
  have hA : A.IsCComponent := by
    simpa only [← MonoidHom.range_eq_map, range_subtype] using htA.map_subtype hn.isSubnormal
  refine ⟨hA, ⟨T.subtype le_sup_right, ?_⟩, ?_⟩
  · simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  · intro he
    exact D.ne_bot (bot_unique (he ▸ s.seed_le_Ri i))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
