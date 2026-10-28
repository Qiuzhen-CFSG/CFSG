module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# Recognizing the binary G₂ overgroup by its conjugation action

An embedded G₂(2)′ of index two is normal. If the ambient two-core is
trivial, its centralizer is trivial, so conjugation embeds the ambient
group in Aut(G₂(2)′). The actual binary automorphism equivalence then
identifies this embedding with G₂(2); the two indices make it surjective.
Its restriction is the original inclusion of G₂(2)′, pointwise.
No splitting or choice of involutory lift is required.

Source application: Aschbacher–Smith, F.6.18(11), pp.309–310, and the
comparison in 15.4.18, p.1163. The concrete octonion and automorphism
comparisons are inherited from the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.QuasisimpleComparison.AmbientExtensions
namespace DegreeThreeModels
open Atlas.G2.LieAutomorphismExtensions
universe u
variable {D : Type u} [Group D] [Finite D]

private theorem binaryPerfect : Group.IsPerfect BinaryDerived := by
  rw [binaryDerived_eq]
  exact Atlas.G2.BinaryException.H_isPerfect

/-- The actual binary derived model is quasisimple. -/
theorem binaryDerived_quasisimple : IsQuasisimple BinaryDerived := by
  let : IsSimpleGroup BinaryDerived := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect BinaryDerived := binaryPerfect
  have hz : center BinaryDerived = ⊥ := by
    rcases (inferInstance : (center BinaryDerived).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup }

omit [Finite D] in
/-- Conjugation recognizes an index-two overgroup with trivial two-core,
retaining the original embedding of the actual binary derived group. -/
theorem binary_extension_equiv
    (i : BinaryDerived →* D) (hi : Function.Injective i)
    (hindex : i.range.index = 2) (hcore : pCore 2 D = ⊥) :
    ∃ e : D ≃* Atlas.G2.Model (ZMod 2), ∀ x : BinaryDerived, e (i x) = x.val := by
  let : IsSimpleGroup BinaryDerived := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect BinaryDerived := binaryPerfect
  let : i.range.Normal := normal_of_index_eq_two hindex
  let ei : BinaryDerived ≃* i.range := MonoidHom.ofInjective hi
  let : IsSimpleGroup i.range := ei.symm.isSimpleGroup
  let : Group.IsPerfect i.range := Group.IsPerfect.ofSurjective (f := ei.toMonoidHom) ei.surjective
  have hq : IsPGroup 2 (D ⧸ i.range) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one, ← index_eq_card] using hindex)
  have hc := centralizer_eq_bot_of_simple_two_quotient i.range
    (Group.IsPerfect.not_isMulCommutative _) hq hcore
  let a : D →* MulAut BinaryDerived :=
    (MulAut.congr ei.symm).toMonoidHom.comp (MulAut.conjNormal (H := i.range))
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro g hg
    have hag : a g = 1 := hg
    have hcg : (MulAut.conjNormal (H := i.range)) g = 1 := by
      apply (MulAut.congr ei.symm).injective
      simpa only [a, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_one] using hag
    have hmem : g ∈ centralizer (i.range : Set D) := by
      intro x hx
      have he := congrArg (fun f : MulAut i.range => (f ⟨x, hx⟩ : D)) hcg
      change g * x * g⁻¹ = x at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    simpa only [hc] using hmem
  let f : D →* Atlas.G2.Model (ZMod 2) := binaryAutomorphismEquiv.symm.toMonoidHom.comp a
  have hf : Function.Injective f := binaryAutomorphismEquiv.symm.injective.comp ha
  have hcard : Nat.card D = 12096 := by
    rw [← i.range.card_mul_index, hindex, ← Nat.card_congr ei.toEquiv, card_binaryDerived]
  have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [card_binaryFull, hcard])
  refine ⟨MulEquiv.ofBijective f hb, ?_⟩
  intro x
  apply binaryAutomorphismEquiv.injective
  change binaryAutomorphismEquiv (binaryAutomorphismEquiv.symm (a (i x))) = _
  rw [binaryAutomorphismEquiv.apply_symm_apply, binaryAutomorphismEquiv_apply,
    binaryConjugation_inner]
  apply MulEquiv.ext
  intro y
  change ei.symm (MulAut.conjNormal (i x) (ei y)) = x * y * x⁻¹
  apply ei.injective
  rw [ei.apply_symm_apply]
  apply Subtype.ext
  change i x * i y * (i x)⁻¹ = i (x * y * x⁻¹)
  rw [i.map_mul, i.map_mul, i.map_inv]

end DegreeThreeModels
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.QuasisimpleComparison.AmbientExtensions
