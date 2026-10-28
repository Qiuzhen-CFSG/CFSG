module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.Held
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.JankoTwo
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.ThreeSubgroup
public import Theory.Mathieu.M11.Properties.Sylow3
public import Theory.Mathieu.M12.Properties.PointStabilizer
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.HigmanSims
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Automorphisms
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.Alternating.Aut

/-!
# Finite rank-one cases with existing intrinsic certificates

For Aschbacher--Smith, proof of 15.3.38, printed p.1137 (PDF p.1154),
we inspect the alternating and sporadic alternatives of Theorem C,
printed p.33 (PDF p.44). Two disjoint three-cycles reduce the alternating
case to A₅. The actual automorphism theorem for A₅, and the checked outer
quotients for J₁ and HS, force every cubic automorphism subgroup to be inner
and hence cyclic when the simple group has three-rank one.

The five Mathieu groups, J₂, J₄, He and Ru have three-rank at least two.
We use actual embedded elementary groups, and noncyclic three-subgroups
in the fixed carriers. In particular the J₄ subgroup has order 27 and a
nonidentity commutator; both matrix-generator premises are discharged.
No model recognition, outer coverage or rank premise is assumed.
The final sporadic case split is in the parent module.

Model sources: GLS3, Tables 5.3a--i, m, p and r. The imported certificate
modules retain their individual ATLAS sources and action conventions.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.FiniteModels
universe u
variable {S : Type u} [Group S] [Finite S]

private theorem pgroup_cyclic_of_rank_one (hr : primeRank 3 S ≤ 1)
    (P : Subgroup S) (hp : IsPGroup 3 P) : IsCyclic P := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  let : IsCyclic Q := Q.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  exact isCyclic_of_injective (Subgroup.inclusion hQ) (Subgroup.inclusion_injective hQ)

private theorem cubic_of_outer_two [IsSimpleGroup S]
    (hna : ¬ IsMulCommutative S) (hr : primeRank 3 S ≤ 1)
    (ho : IsPGroup 2 (MulAut.Outer S)) : CubicAutomorphismsAbelian S := by
  have hi : Function.Injective (MulAut.conj : S →* MulAut S) := by
    apply (MonoidHom.ker_eq_bot_iff (MulAut.conj : S →* MulAut S)).mp
    rcases (MulAut.conj : S →* MulAut S).normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply hna
      apply IsMulCommutative.of_comm
      intro x y
      have hx : MulAut.conj x = 1 := by
        exact (show x ∈ (MulAut.conj : S →* MulAut S).ker from h ▸ mem_top x)
      have he := congrArg (fun a : MulAut S => a y) hx
      exact mul_inv_eq_iff_eq_mul.mp he
  intro A hA
  have hp : IsPGroup 3 A := fun a => ⟨1, by simpa using hA a⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup S)
  have hbot : A.map q = ⊥ := disjoint_self.mp
    ((hp.map q).disjoint_of_coprime (ho.to_subgroup (A.map q)) (by decide))
  have hle : A ≤ MulAut.innerSubgroup S := by
    intro a ha
    apply (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup S) a).mp
    have hm := Subgroup.mem_map_of_mem q ha
    rwa [hbot, Subgroup.mem_bot] at hm
  let K := A.comap (MulAut.conj : S →* MulAut S)
  let f : K →* A := (MulAut.conj.comp K.subtype).codRestrict A (fun k => k.property)
  have hf : Function.Injective f := fun x y h => Subtype.ext (hi (congrArg Subtype.val h))
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨s, hs⟩ := hle a.property
    exact ⟨⟨s, by change MulAut.conj s ∈ A; rw [hs]; exact a.property⟩, Subtype.ext hs⟩
  let : IsCyclic K := pgroup_cyclic_of_rank_one hr K (hp.of_injective f hf)
  let : IsCyclic A := isCyclic_of_surjective f hs
  infer_instance

private theorem alternating_outer_five :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 5))) := by
  intro q
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective
    (MulAut.innerSubgroup (alternatingGroup (Fin 5))) q
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide)
      (by decide)).surjective α
  refine ⟨1, ?_⟩
  simp only [pow_one, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hσ : σ ^ 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_pow]
    exact Int.units_sq _
  exact ⟨⟨σ ^ 2, hσ⟩, MulAut.conjNormal_val.symm⟩

/-- Every rank-one nonabelian simple alternating model has abelian cubic automorphism subgroups. -/
theorem cubic_alternating [IsSimpleGroup S]
    (hna : ¬ IsMulCommutative S) (hr : primeRank 3 S = 1)
    {n : ℕ} (_hn : n ≤ 8) (iso : Nonempty (S ≃* alternatingGroup (Fin n))) :
    CubicAutomorphismsAbelian S := by
  obtain ⟨e⟩ := iso
  have hn5 : 5 ≤ n := by
    by_contra! h
    let f : S →* Equiv.Perm (Fin 4) :=
      (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (show n ≤ 4 by omega))).comp
        ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective (f := f)
      ((Equiv.Perm.viaEmbeddingHom_injective _).comp (Subtype.val_injective.comp e.injective))
    exact hna (IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))
  have hn6 : ¬ 6 ≤ n := by
    intro h
    have := alternatingGroup.TwoThreeCycles.two_le_primeRank h
    rw [← primeRank_equiv 3 e, hr] at this
    omega
  have hn : n = 5 := by omega
  subst n
  apply cubic_of_outer_two hna hr.le
  exact alternating_outer_five.of_injective (MulAut.outerCongr e).toMonoidHom
    (MulAut.outerCongr e).injective


open Sporadic.Mathieu

/-- The checked elementary Sylow subgroup of M₁₁ has order nine. -/
theorem m11_rank_ge_two : 2 ≤ primeRank 3 M11 := by
  let f := (m11Sylow3 : Subgroup M11).subtype.comp m11Sylow3_mulEquiv_e9.symm.toMonoidHom
  exact primeRank_ge_of_elementary_embedding
    (by decide +kernel : ∀ a : Multiplicative (Fin 3 × Fin 3), a ^ 3 = 1)
    (by simp [Nat.card_eq_fintype_card] : Nat.card (Multiplicative (Fin 3 × Fin 3)) = 3 ^ 2)
    f ((m11Sylow3 : Subgroup M11).subtype_injective.comp m11Sylow3_mulEquiv_e9.symm.injective)

/-- The natural M₁₁ point stabilizer transfers its rank bound to M₁₂. -/
theorem m12_rank_ge_two : 2 ≤ primeRank 3 M12 := by
  exact m11_rank_ge_two.trans ((Theory.GroupTheory.primeRank_le_of_injective 3
    m11ToM12PointStabilizer m11ToM12PointStabilizer_injective).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 _ (MulAction.stabilizer M12 (12 : Fin 12)).subtype_injective))

/-- The checked elementary subgroup of M₂₂ has order nine. -/
theorem m22_rank_ge_two : 2 ≤ primeRank 3 M22 := by
  exact m22_primeRank_three.ge

/-- The natural M₂₂ point stabilizer transfers its rank bound to M₂₃. -/
theorem m23_rank_ge_two : 2 ≤ primeRank 3 M23 := by
  exact m22_rank_ge_two.trans ((primeRank_equiv 3 m23EquivM22PointStabilizer).le.trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 _ (MulAction.stabilizer M23 (9 : Fin 23)).subtype_injective))

/-- The natural M₂₃ point stabilizer transfers its rank bound to M₂₄. -/
theorem m24_rank_ge_two : 2 ≤ primeRank 3 M24 := by
  exact m23_rank_ge_two.trans ((primeRank_equiv 3 m23EquivM24PointStabilizer).le.trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 _ (MulAction.stabilizer M24 (24 : Fin 24)).subtype_injective))

/-- The actual nonabelian three-subgroup of order 27 excludes cyclic Sylow subgroups in J₄. -/
theorem j4_rank_ge_two : 2 ≤ primeRank 3 Janko4.Model := by
  by_contra! hr
  let P := Janko4.Simplicity.threeLocalSubgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  have hp : IsPGroup 3 P := IsPGroup.of_card (n := 3)
    (Janko4.Simplicity.threeLocal_card _ _)
  let := pgroup_cyclic_of_rank_one (by omega) P hp
  exact Janko4.Simplicity.threeLocal_not_isMulCommutative _ _ inferInstance

/-- The certified trivial outer group of J₁ gives the required intrinsic automorphism property. -/
theorem cubic_j1 [IsSimpleGroup S] (hna : ¬ IsMulCommutative S)
    (hr : primeRank 3 S = 1) (e : S ≃* Janko1.Model) : CubicAutomorphismsAbelian S := by
  let := Janko1.OuterCertificate.outer_subsingleton
  apply cubic_of_outer_two hna hr.le
  have ho : IsPGroup 2 (MulAut.Outer Janko1.Model) := fun a => ⟨0, Subsingleton.elim _ _⟩
  exact ho.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The certified outer two-group of HS gives the required intrinsic automorphism property. -/
theorem cubic_hs [IsSimpleGroup S] (hna : ¬ IsMulCommutative S)
    (hr : primeRank 3 S = 1) (e : S ≃* Sporadic.LeechRelated.HS.Carrier) :
    CubicAutomorphismsAbelian S := by
  apply cubic_of_outer_two hna hr.le
  have ho := Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
    Sporadic.LeechRelated.HS.pointStabilizer_map Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow
  exact ho.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective


private theorem rank_ge_two_of_noncyclic_three {G : Type*} [Group G] [Finite G]
    (h : ∃ P : Subgroup G, IsPGroup 3 P ∧ ¬ IsCyclic P) : 2 ≤ primeRank 3 G := by
  by_contra! hr
  obtain ⟨P, hp, hn⟩ := h
  exact hn (pgroup_cyclic_of_rank_one (by omega) P hp)

/-- Two commuting cubic ATLAS words generate a noncyclic subgroup of He. -/
theorem held_rank_ge_two : 2 ≤ primeRank 3 Held.He :=
  rank_ge_two_of_noncyclic_three
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.held_noncyclic_three_subgroup

/-- The checked subgroup of order nine in J₂ excludes three-rank one. -/
theorem j2_rank_ge_two : 2 ≤ primeRank 3 Sporadic.LeechRelated.J2.Carrier :=
  rank_ge_two_of_noncyclic_three
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.j2_noncyclic_three_subgroup

/-- The certified nonabelian subgroup of order 27 excludes three-rank one in Ru. -/
theorem ru_rank_ge_two : 2 ≤ primeRank 3 Rudvalis.Model := by
  by_contra! hr
  obtain ⟨P, hp, hn⟩ := CFSG.Quasithin.MainConverse.SporadicLocal.RuRank.three_subgroup
  let := pgroup_cyclic_of_rank_one (by omega) P (IsPGroup.of_card hp)
  exact hn inferInstance

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.FiniteModels
