module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Containment
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Local-family membership from the actual rank-one quotient

Each flag residual is perfect and T-invariant. Its preceding PSL₂(q)
identification makes its two-core quotient simple, so it is a C-component
of its join with T. The original seed V witnesses the nontrivial two-core
of that join. Thus the containment theorems require only the preceding
quotient model, not a separate local-component membership premise.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
the opening of 11.1 and the proof of 11.1.1, printed pp.760--761.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual PSL₂(q) quotient supplies local-family membership, including
the nontrivial two-core clause, for each of the original residuals. -/
theorem flag_mem_local_of_model (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree)) :
    f.Li i ∈ Chapter1.L G T := by
  let B := f.Li i
  let J := B ⊔ (T : Subgroup G)
  let A := B.subgroupOf J
  let : Group.IsPerfect B := localResidual_perfect _
  obtain ⟨E, _, _, hE, ⟨e⟩⟩ := hm
  have hfour : 4 ≤ Nat.card E := by
    rw [hE]
    exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
      (Nat.pow_le_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    rcases (inferInstance : (center (B ⧸ pCore 2 B)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative (B ⧸ pCore 2 B)
        (center_eq_top_iff.mp ht)).elim
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    { toIsPerfect := inferInstance
      simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  have hp : IsPPerfect 2 B := by
    intro N hN hP
    let := hN
    by_contra hne
    let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hP.isNilpotent
  have htop : (⊤ : Subgroup B).IsCComponent :=
    isCComponent_top_of_isPPerfect_of_quasisimple_quotient (pCore 2 B) pCore_isPGroup hp
  let eA : B ≃* A := (subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).symm
  have htopA : (⊤ : Subgroup A).IsCComponent := by
    have he : (⊤ : Subgroup B).map eA.toMonoidHom = ⊤ :=
      (MonoidHom.range_eq_map eA.toMonoidHom).symm.trans
        (MonoidHom.range_eq_top.mpr eA.surjective)
    exact he ▸ htop.map_equiv eA
  have hn : A.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le B.le_normalizer (f.sylow_normalizes_Li i))
  have hA : A.IsCComponent := by
    simpa only [← MonoidHom.range_eq_map, range_subtype] using
      IsCComponent.map_subtype hn.isSubnormal htopA
  refine ⟨hA, ⟨T.subtype le_sup_right, ?_⟩, ?_⟩
  · simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  · intro he
    apply f.V_ne_bot i.castSucc
    apply bot_unique
    have hseed : V ≤ J.pCoreIn 2 := f.seed_le_Ri S i
    exact (D.centralQuotientPreimage_le _).trans (he ▸ hseed)

/-- The first containment consumer, now with only the preceding quotient model. -/
theorem flag_exists_unique_normal_component_of_model (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi i.castSucc : Set G)) K ∧
      f.Li i ≤ K ∧ K ∈ Chapter1.He G ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) J →
        f.Li i ≤ J → J = K :=
  flag_exists_unique_normal_component D S f i (flag_mem_local_of_model D S f i hm)

/-- The arbitrary-U consumer, with its exact Sylow and pointwise-action hypotheses. -/
theorem subspace_exists_unique_normal_component_of_model (U : Subgroup G) (hU : U ≠ ⊥)
    (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (U : Set G)) K ∧
      f.Li 0 ≤ K ∧ ∀ J : Subgroup G, Source.ComponentIn (normalizer (U : Set G)) J →
        f.Li 0 ≤ J → J = K :=
  subspace_exists_unique_normal_component D S f U hU hUV hSyl
    (flag_mem_local_of_model D S f 0 hm) hfix

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
