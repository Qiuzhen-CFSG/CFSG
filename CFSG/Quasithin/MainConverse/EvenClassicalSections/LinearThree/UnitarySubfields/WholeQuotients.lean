module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.StandardAction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.GroupAction.PrimitiveQuotient

/-!
# Simple quotients of the whole even PSU₃ model

The faithful doubly transitive action on isotropic points has a solvable
point stabilizer. Every noninjective quotient of a faithful primitive group
is already a quotient of its point stabilizer. Thus every simple quotient
of PSU₃(2ⁿ), n ≥ 2, is prime cyclic or isomorphic to the original, actual
unitary matrix group. This supplies the whole-group branch of subfield
induction without a separate simplicity or perfectness theorem.

Arbitrary Hermitian forms are transported to the antidiagonal form with
the same involution. The coefficient field has order (2ⁿ)² throughout.
The proof uses Huppert II.10.12 and the elementary normal-orbit theorem for
primitive groups; it does not use the K hypothesis in the shortened proof
of GLS3, Theorem 6.5.3. The section condition is Aschbacher–Smith 0.1.1(K).
-/

open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary
open CFSG.KnownSimple
open scoped LinearAlgebra.Projectivization

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections

private theorem standard_surjective_solvable_or_equiv
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstd : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {S : Type*} [Group S]
    (f : ProjectiveSpecialUnitaryMatrixGroup J →* S) (hf : Function.Surjective f) :
    Group.IsSolvable S ∨ Nonempty (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  classical
  by_cases hi : Function.Injective f
  · exact Or.inr ⟨(MulEquiv.ofBijective f ⟨hi, hf⟩).symm⟩
  left
  obtain ⟨rho, a, P, _hcomp, _hproper, hsolv, hrho, _hnatural, _hP,
    hstab, _hregular, htwo⟩ := standard_psu_borel_data J n hn hcard hconj hstd
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let A : Set (ℙ F (Fin 3 → F)) := {x | ∃ (v : Fin 3 → F) (hv : v ≠ 0),
    x = Projectivization.mk F v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let X := {x : ℙ F (Fin 3 → F) // x ∈ A}
  let : MulAction G X := MulAction.compHom X rho
  let : FaithfulSMul G X := ⟨fun h => hrho (Equiv.ext h)⟩
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.is_two_pretransitive_iff.mpr (by
      intro a b c d hab hcd
      exact htwo a b c d hab hcd)
  let : MulAction.IsPreprimitive G X := MulAction.isPreprimitive_of_is_two_pretransitive h2
  have he : Subgroup.normalizer ((P : Subgroup G) : Set G) =
      MulAction.stabilizer G a := hstab
  let : Group.IsSolvable (MulAction.stabilizer G a) := he ▸ hsolv
  exact Group.isSolvable_of_surjective
    (f.surjective_domRestrict_stabilizer_of_not_injective hf hi a)

/-- Every quotient of the actual model is solvable or isomorphic to that model.
This statement includes the binary endpoint, without assuming simplicity. -/
public theorem psu3_even_surjective_solvable_or_equiv
    {G S : Type*} [Group G] [Group S] {n : ℕ} (hn : 0 < n)
    (hG : ClassicalGroup.IsPSU G 3 (2 ^ n))
    (f : G →* S) (hf : Function.Surjective f) :
    Group.IsSolvable S ∨ Nonempty (S ≃* G) := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hG
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let e' := e.trans (FormTransport.projectiveEquiv J C hC)
  rcases standard_surjective_solvable_or_equiv (FormTransport.standardForm J) n hn
      hcard hconj rfl (f.comp e'.symm.toMonoidHom) (hf.comp e'.symm.surjective) with hs | he
  · exact Or.inl hs
  · exact Or.inr (he.map fun a => a.trans e'.symm)

/-- Every simple quotient of the whole model in the catalogue's unitary
parameter range has an actual constructed carrier. -/
public theorem psu3_even_simple_quotient_constructed
    {G S : Type*} [Group G] [Group S] [IsSimpleGroup S] {n : ℕ} (hn : 2 ≤ n)
    (hG : ClassicalGroup.IsPSU G 3 (2 ^ n))
    (f : G →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  rcases psu3_even_surjective_solvable_or_equiv (by omega) hG f hf with hs | he
  · let := hs
    exact .cyclic (primeCyclic_of_solvable_simple S)
  · obtain ⟨e⟩ := he
    have hpow : IsPrimePow (2 ^ n) := ⟨2, n, Nat.prime_iff.mp Nat.prime_two, by omega, rfl⟩
    have htwo : 2 ^ n ≠ 2 := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) hn
      norm_num at h
      omega
    exact .classical (.unitary 3 (2 ^ n)
      ⟨hpow, by decide, by omega, fun _ => htwo⟩ (hG.of_mulEquiv e))

/-- Proper-subgroup sections and the independently proved whole-group
quotient argument together give all simple sections. -/
public theorem psu3_even_isKGroup_of_properK
    {G : Type*} [Group G] {n : ℕ} (hn : 2 ≤ n)
    (hG : ClassicalGroup.IsPSU G 3 (2 ^ n))
    (hproper : HasProperKSubgroups IsConstructedCarrier G) :
    IsKGroup IsConstructedCarrier G := by
  intro S _ hS U f hf
  let := hS
  by_cases hU : U = ⊤
  · subst U
    let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    exact psu3_even_simple_quotient_constructed hn hG
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)
  · let e : (⊤ : Subgroup U) ≃* U := Subgroup.topEquiv
    exact hproper U hU S hS ⊤ (f.comp e.toMonoidHom) (hf.comp e.surjective)

end CFSG.Quasithin.MainConverse.UnitaryThreeSections
