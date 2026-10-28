module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.Inverter
public import Theory.GroupTheory.CentralCoprimeTorusAction
public import Theory.Representation.SpecialLinearAbelianAutomizer
public import Theory.Representation.NoncyclicDegreeThree
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.LinearCoefficientEquiv

/-!
# The linear Cartan action of a normalizing two-subgroup

Noncyclicity makes the left cyclic factor nontrivial, so its order divisibility
gives p ∣ q - 1 and hence p ≠ q. Transport the arbitrary finite-field witness
through an actual field equivalence and lift B through the genuine SL₃-to-PSL₃
scalar kernel. Since p > 3, the lift is isomorphic to B and has exactly the
inverse images of B's normalizer and centralizer.

The faithful determinant-one action has three distinct character lines, making
its centralizer abelian; its automizer embeds in S₃. Descent through the central
quotient and restriction to the normalizing two-subgroup S ∩ D gives an abelian
relative centralizer of index dividing two. Normalization remains the explicit
hypothesis supplied independently to this contract.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51; A.3.21(c), pp.55–56;
and the proof of 1.3.4, pp.510–511 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J]

/-- The nontrivial left factor supplies cross characteristic. -/
theorem CaseThree.linear_prime_dvd_characteristic_sub_one
    {D B S K : Subgroup J} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hC : CaseThree D B S K q .linear .linear)
    (hB : IsPGroup p B) (hn : ¬ IsCyclic B) : p ∣ q - 1 := by
  have hP : IsPGroup p (B ⊓ K : Subgroup J) :=
    hB.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  rcases hP.card_eq_or_dvd with h | h
  · exact (hC.toCyclicDecomposition.left_ne_bot hn (Subgroup.card_eq_one.mp h)).elim
  · exact h.trans hC.sl2_dvd

/-- The prime of B differs from the defining characteristic. -/
theorem CaseThree.linear_prime_ne_characteristic
    {D B S K : Subgroup J} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hC : CaseThree D B S K q .linear .linear)
    (hB : IsPGroup p B) (hn : ¬ IsCyclic B) : p ≠ q := by
  intro he
  have hd := hC.linear_prime_dvd_characteristic_sub_one hB hn
  have hq := (Fact.out : q.Prime).one_lt
  have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd
  omega

private theorem centralizer_restriction {G : Type*} [Group G]
    (B D : Subgroup G) (hB : B ≤ D) :
    (centralizer (B : Set G)).subgroupOf D = centralizer (B.subgroupOf D : Set D) := by
  ext d
  constructor
  · intro hd b hb
    exact Subtype.ext (hd b hb)
  · intro hd b hb
    exact congrArg Subtype.val (hd ⟨b, hB hb⟩ hb)

/-- The relative torus centralizer is abelian and has index dividing two. -/
theorem CaseThree.linear_torus_action [Finite J]
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .linear .linear)
    (hn : ¬ IsCyclic B) (_hlarge : 3 < q)
    (hnorm : (S : Subgroup J) ⊓ D ≤ normalizer (B : Set J)) :
    IsMulCommutative ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)) ∧
      ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)).index ∣ 2 := by
  let _ : Fact p.Prime := ⟨hA.prime⟩
  let _ : IsMulCommutative B := hC.toCyclicDecomposition.isMulCommutative
  have hpq := hC.linear_prime_ne_characteristic hA.p_group hn
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hC.model
  let _ : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hF)
  let eD : D ≃* PSL(3, ZMod q) := e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)
  let f : SL(3, ZMod q) →* D := eD.symm.toMonoidHom.comp (Matrix.PSL3.projection (ZMod q))
  have hf : Function.Surjective f := eD.symm.surjective.comp (Matrix.PSL3.projection_surjective _)
  have hfker : f.ker = center SL(3, ZMod q) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eD.symm.injective, Matrix.PSL3.projection_ker]
  have hp3 : Nat.Coprime p 3 := by
    apply (Nat.Prime.coprime_iff_not_dvd hA.prime).mpr
    intro hd
    have hp := Nat.le_of_dvd (by decide : 0 < 3) hd
    have := hA.large
    omega
  have hkerp : Nat.Coprime p (Nat.card f.ker) := by
    rw [hfker]
    exact hp3.coprime_dvd_right (Matrix.SL3.card_center_dvd_three _)
  have hker2 : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfker]
    exact (by decide : Nat.Coprime 2 3).coprime_dvd_right (Matrix.SL3.card_center_dvd_three _)
  have hBD : IsPGroup p (B.subgroupOf D) :=
    hA.p_group.of_equiv (subgroupOfEquivOfLe hA.inside).symm
  obtain ⟨L, hL, hLm, hLN, hLC, hLi⟩ := exists_prime_lift_of_central_coprime
    f hf (hfker ▸ le_refl _) hkerp (B.subgroupOf D) hBD
  let eL : L ≃* B.subgroupOf D :=
    (MulEquiv.ofBijective (f.subgroupMap L) ⟨fun x y h => hLi (congrArg Subtype.val h),
      f.subgroupMap_surjective L⟩).trans (MulEquiv.subgroupCongr hLm)
  let _ : IsMulCommutative L := ⟨⟨fun x y => eL.injective (by
    simp only [map_mul]
    exact mul_comm' _ _)⟩⟩
  have hnL : ¬ IsCyclic L := fun h =>
    hn ((subgroupOfEquivOfLe hA.inside).isCyclic.mp (eL.isCyclic.mp h))
  have horder : (Nat.card L : ZMod q) ≠ 0 := by
    obtain ⟨a, ha⟩ := hL.exists_card_eq
    rw [ha, Nat.cast_pow]
    apply pow_ne_zero
    rw [Ne, CharP.cast_eq_zero_iff]
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hA.prime).mp hd).symm
  let _ := Representation.specialLinear_centralizer_isMulCommutative_of_noncyclic L hnL horder
  obtain ⟨j, hj⟩ := Representation.specialLinear_abelian_automizer_embeds_perm 3 L horder
  let T : Subgroup J := (S : Subgroup J) ⊓ D
  have hT : IsPGroup 2 T :=
    S.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hTD : IsPGroup 2 (T.subgroupOf D) := hT.of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  have hTDn : T.subgroupOf D ≤ normalizer (B.subgroupOf D : Set D) := by
    rw [← subgroupOf_normalizer_eq hA.inside]
    exact fun t ht => hnorm ht
  obtain ⟨hcomm, hi⟩ := centralizer_two_action_of_central_coprime_lift f hf
    (hfker ▸ le_refl _) hker2 L (B.subgroupOf D) (T.subgroupOf D) hLN hLC j hj hTD hTDn
  let u : T.subgroupOf D ≃* T := subgroupOfEquivOfLe inf_le_right
  have he : ((centralizer (B : Set J)).subgroupOf T).comap u.toMonoidHom =
      (centralizer (B.subgroupOf D : Set D)).subgroupOf (T.subgroupOf D) := by
    rw [← centralizer_restriction B D hA.inside]
    rfl
  have hi' : ((centralizer (B : Set J)).subgroupOf T).index ∣ 2 := by
    rwa [← he, index_comap_of_surjective _ u.surjective] at hi
  have hmap : ((centralizer (B.subgroupOf D : Set D)).subgroupOf
      (T.subgroupOf D)).map u.toMonoidHom = (centralizer (B : Set J)).subgroupOf T := by
    rw [← he, map_comap_eq_self_of_surjective u.surjective]
  let _ := hcomm
  refine ⟨?_, hi'⟩
  rw [← hmap]
  exact map_isMulCommutative _ _

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
