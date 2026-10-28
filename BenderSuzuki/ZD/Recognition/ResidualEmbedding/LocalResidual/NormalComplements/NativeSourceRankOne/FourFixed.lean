module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Nonsolvable

/-!
# Unique fixed points when the two-point stabilizer has rank one

Double transitivity carries every two-point stabilizer to the original D.
Consequently an elementary subgroup of order at least four contained in M
cannot also fix a different coset. Its ambient centralizer therefore lies
in M. This is the fixed-point step in the first branch of Lemma 16.3.

Source: GLS4, Chapter 2, proof of Lemma 16.3(a), first paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Every two-point stabilizer has the same four-group obstruction. -/
public theorem residualPair_not_twoRank_all
    (ha : ResidualAction Z M) {t : G} (htM : t ∉ M)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    {g : G} (hgM : g ∉ M) :
    ¬ TwoRankAtLeastTwo (residualPairStabilizer M g) := by
  let a : G ⧸ M := QuotientGroup.mk 1
  have hne (x : G) (hx : x ∉ M) : x⁻¹ • a ≠ a := by
    intro he
    exact hx ((baseCoset_stabilizer M) ▸
      (MulAction.mem_stabilizer_iff.mpr (inv_smul_eq_iff.mp he).symm))
  obtain ⟨m, hma, hmt⟩ := MulAction.is_two_pretransitive_iff.mp ha.two_transitive
    (hne g hgM).symm (hne t htM).symm
  have hpair (x : G) : residualPairStabilizer M x =
      MulAction.stabilizer G a ⊓ MulAction.stabilizer G (x⁻¹ • a) := by
    rw [← rightConjugate_stabilizer, baseCoset_stabilizer]
    rfl
  have heq : (residualPairStabilizer M g).map (MulAut.conj m).toMonoidHom =
      residualPairStabilizer M t := by
    rw [hpair g, map_inf _ _ _ (MulAut.conj m).injective,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hma, hmt, ← hpair t]
  intro hrg
  apply hrank
  let f : residualPairStabilizer M g →* residualPairStabilizer M t :=
    (MulAut.conj m).toMonoidHom.restrict
      (fun x hx => heq ▸ mem_map_of_mem (MulAut.conj m).toMonoidHom hx)
  exact hrg.map_of_injective f (fun x y hxy =>
    Subtype.ext ((MulAut.conj m).injective (congrArg Subtype.val hxy)))

omit [Finite G] in
/-- An elementary subgroup of order at least four in M has its whole
ambient centralizer inside M when D has rank one. -/
public theorem elementary_centralizer_le_of_pair_rank_one
    (ha : ResidualAction Z M) {t : G} (htM : t ∉ M)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 4 ≤ Nat.card E) (hEM : E ≤ M) :
    centralizer (E : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  have hED : E ≤ residualPairStabilizer M g := by
    intro x hx
    refine ⟨hEM hx, ?_⟩
    have hx' := rightConjugateElem_mem_rightConjugate (g := g) (hEM hx)
    have hc := mem_centralizer_iff.mp hg x hx
    have he : rightConjugateElem x g = x := by
      rw [rightConjugateElem, mul_assoc, hc, inv_mul_cancel_left]
    exact he ▸ hx'
  have hfour : TwoRankAtLeastTwo E := by
    obtain ⟨A, hAcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two
      (IsElementaryAbelian.isPGroup 2 E) (n := 2) (by simpa using hE)
    refine ⟨A, by simpa using hAcard, ?_⟩
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) (x : E)
  exact residualPair_not_twoRank_all ha htM hrank hgM
    (hfour.map_of_injective (inclusion hED) (inclusion_injective hED))

end BenderSuzuki.ZD
