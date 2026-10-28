module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.SmallPrime
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.LargePrime
public import Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank.Components

/-!
# Component action of a positioned outer four-group

Let L = F*(G) be simple PSU₃(p), G = LT, and let the outer elementary
four-group A lie in T with its inner involution z central in T. Set
K = C_G(z)^∞T, using the actual embedded solvable residual.

For p > 3 the established inner-centralizer calculation identifies K^∞ with
SL₂(p). If A lay in the radical of K, its outer involution t would centralize
this component. Since G/L is a two-group, the component lies in L and would
embed in the full fixed group C_L(t), identified with SO₃(p) over the original
Hermitian fixed field. The equal orders force surjectivity. But every
orthogonal component is PSL₂(p), of half that order, a contradiction.
This uses the public orthogonal component theorem and no private matrix API.

Thus A survives the radical quotient. The existing quasisimple two-extension
constructor proves every literal E₂ clause, including the singleton orbit
under tau(K,T∩K,A) and the full component commutator. At p = 3, the full
centralizer is solvable. The final theorem applies the four-actor containment
reduction to the actual member of the obstruction family. No auxiliary inner
actor or assumption about its membership in that family is required.

Source: Aschbacher--Smith, E.1.1--2, E.1.5 and E.1.14(7), printed pp.209--210,
214; A.3.21(a), printed p.55. E.1.14(7) refers to Aschbacher,
GF(2)-representations of finite groups (1982), Lemma 4.11. The outer fixed-group
and orthogonal component calculations retain their GLS3 source references.
-/

open Subgroup Theory.GroupTheory Matrix
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors

private theorem quasisimple_of_sl2_equiv {D : Type*} [Group D]
    {p : ℕ} [Fact p.Prime] (hl : 3 < p)
    (e : D ≃* SpecialLinearGroup (Fin 2) (ZMod p)) : IsQuasisimple D := by
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) (ZMod p)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hl)
  let : IsQuasisimple (SpecialLinearGroup (Fin 2) (ZMod p)) :=
    ⟨ProjectiveSpecialLinearGroup.rank_two_simple (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using Nat.succ_le_of_lt hl)⟩
  exact IsQuasisimple.of_mulEquiv e.symm


private theorem no_sl2_embedding_in_orthogonal
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (f : SpecialLinearGroup (Fin 2) (ZMod p) →* (splitOrthogonalForm F).specialSubgroup)
    (hf : Function.Injective f) : False := by
  let := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    intro he
    have hh := FiniteField.even_card_of_char_two he
    rw [← Nat.card_eq_fintype_card, hF] at hh
    obtain ⟨k, hk⟩ := ho
    omega
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
    rw [GorensteinWalter.sl2_card_formula, Nat.card_eq_fintype_card, ZMod.card]
  have hcardSO : Nat.card (splitOrthogonalForm F).specialSubgroup = p * (p ^ 2 - 1) := by
    rw [card_splitOrthogonal_specialSubgroup h2, hF]
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcardSL.trans hcardSO.symm⟩).2
  let e := MulEquiv.ofBijective f ⟨hf, hsurj⟩
  let : IsQuasisimple (SpecialLinearGroup (Fin 2) (ZMod p)) :=
    quasisimple_of_sl2_equiv hl (MulEquiv.refl _)
  let : IsQuasisimple (splitOrthogonalForm F).specialSubgroup := IsQuasisimple.of_mulEquiv e
  let H : Subgroup (splitOrthogonalForm F).specialSubgroup := ⊤
  let : IsQuasisimple H := IsQuasisimple.of_mulEquiv topEquiv.symm
  obtain ⟨ec⟩ := TernaryOrthogonal.component_equiv_psl2 (Fact.out : p.Prime) ho hF
    (show IsComponent _ H from ⟨(inferInstance : H.Normal).isSubnormal, inferInstance⟩)
  have he : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F) = p * (p ^ 2 - 1) := by
    rw [← Nat.card_congr ec.toEquiv, show H = ⊤ from rfl, card_top, hcardSO]
  have hc := ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
  rw [he, hF] at hc
  have hpos : 0 < p * (p ^ 2 - 1) := by
    simpa only [hcardSL] using (Nat.card_pos (α := SpecialLinearGroup (Fin 2) (ZMod p)))
  omega

variable {G : Type*} [Group G] [Finite G]

/-- The outer four-group has nontrivial image modulo the radical of the actual
residual supplement. Otherwise its outer involution would fix the entire
SL₂ residual, which cannot embed in its orthogonal fixed group. -/
public theorem outer_four_not_le_centralizerResidual_radical [IsSimpleGroup (generalizedFitting G)]
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hl : 3 < p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hfour : Nat.card A = 4) (hinter : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 2)
    (hAT : A ≤ (T : Subgroup G)) (z : G) (hzL : z ∈ generalizedFitting G)
    (hz : orderOf z = 2) (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ¬ A.subgroupOf (centralizerResidualOvergroup T z) ≤
      solvableRadical (centralizerResidualOvergroup T z) := by
  let : Fact p.Prime := ⟨hp⟩
  let L := generalizedFitting G
  let K := centralizerResidualOvergroup T z
  let D := solvableResidual K
  have hq := isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hLT
  let : Group.IsNilpotent (G ⧸ L) := hq.isNilpotent
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv L T hLT hp ho hl hmodel z hzL hz
  let e := (centralizerResidualOvergroup_residualEquiv hTz).trans ec
  let : IsQuasisimple D := quasisimple_of_sl2_equiv hl e
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hcomp : IsComponent K D := ⟨(inferInstance : D.Normal).isSubnormal, inferInstance⟩
  have hDR : ⁅D, solvableRadical K⁆ = ⊥ := by
    rcases hcomp.normal_dichotomy (solvableRadical K) with hle | hc
    · let : Group.IsSolvable D :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
      exact (Group.IsPerfect.not_isSolvable D inferInstance).elim
    · exact hc
  intro hA
  have hDA : ⁅D, A.subgroupOf K⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono le_rfl hA).trans hDR.le)
  let : Group.IsPerfect (D.map K.subtype) := Group.IsPerfect.map K.subtype
  have hDL : D.map K.subtype ≤ L := le_of_isPerfect_of_solvable_quotient _ L
  have hout : ¬ A ≤ L := by
    intro h
    have he : A ⊓ generalizedFitting G = A := inf_eq_left.mpr h
    rw [he, hfour] at hinter
    omega
  obtain ⟨t, htA, htL⟩ : ∃ t : G, t ∈ A ∧ t ∉ L := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hout
  let j : D →* (centralizer ({t} : Set G)).subgroupOf L :=
    { toFun := fun x => ⟨⟨x.val.val, hDL (mem_map_of_mem K.subtype x.property)⟩,
        mem_centralizer_singleton_iff.mpr (congrArg (fun y : K => (y : G))
          ((commutator_eq_bot_iff_le_centralizer.mp hDA) x.property
            (⟨t, (hAT.trans le_sup_right) htA⟩ : K) htA)).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h))
  obtain ⟨F, _, _, J, hcard, hc, ⟨em⟩⟩ := hmodel
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hc))
  obtain ⟨ef⟩ := outer_fixed_equiv hp ho ⟨F, inferInstance, inferInstance, J, hcard, hc, ⟨em⟩⟩
    J hcard hc em t htL (elemPow_eq_one_of_isElementaryAbelian t htA)
  exact no_sl2_embedding_in_orthogonal (F := FixedBy.subfield F J.conj) ho hl hfixed
    (ef.toMonoidHom.comp (j.comp e.symm.toMonoidHom))
    (ef.injective.comp (hj.comp e.symm.injective))

/-- The source local alternative for the positioned outer four-group. The
small-prime centralizer is solvable; at larger primes the actor acts nontrivially
on the unique component, whose orbit under the literal local tau is a singleton. -/
public theorem positioned_four_centralizer_local_structure
    {κ : GroupClass} (_hG : IsSQTK κ G) [IsSimpleGroup (generalizedFitting G)]
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hfour : Nat.card A = 4)
    (hinter : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 2)
    (z : G) (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (_hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Group.IsSolvable (centralizer ({z} : Set G)) ∨
      ECaseOdd A (centralizerResidualOvergroup T z) ∨
      ECaseComponent (T : Subgroup G) A (centralizerResidualOvergroup T z) := by
  by_cases hthree : p = 3
  · subst p
    exact Or.inl (inner_centralizer_solvable_of_prime_three
      (generalizedFitting G) T hLT hmodel z hzL hz)
  · have hl : 3 < p := by
      have hp2 := hp.two_le
      have hn2 : p ≠ 2 := by intro h; subst p; norm_num at ho
      omega
    let := hA
    exact Or.inr (Or.inr (inner_centralizer_component_of_not_le_radical
      (generalizedFitting G) T hLT hp ho hl hmodel A z hzL hz hTz
      (outer_four_not_le_centralizerResidual_radical T hLT hp ho hl hmodel A hfour hinter hAT z hzL hz hTz)))

/-- The actual E.1.5 obstruction consumer: the full centralizer of the
positioned inner involution lies in the obstruction overgroup. -/
public theorem positioned_four_centralizer_le
    {κ : GroupClass} (hG : IsSQTK κ G) [IsSimpleGroup (generalizedFitting G)]
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (d : LargeFamilyObstruction T) {A : Subgroup G} (hA : A ∈ d.family)
    (hAT : A ≤ (T : Subgroup G)) (hfour : Nat.card A = 4)
    (hinter : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 2)
    (z : G) (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  exact centralizer_le_of_local_structure d hA hAT hfour hzA hz1 hTz
    (positioned_four_centralizer_local_structure hG T hLT hp ho hmodel A
      (d.elementary.1 A hA) hAT hfour hinter z hz hzL hzA hTz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors
