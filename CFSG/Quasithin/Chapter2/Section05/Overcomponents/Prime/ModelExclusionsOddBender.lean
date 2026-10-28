module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.OddLinear
public import Theory.SpecificGroups.SU3.SixSubgroupExclusion
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRanks

/-!
The odd and Bender branches of the actual marked 1.1.5 catalogue. The odd linear actor has solvable fixed subgroup over its prime field. The original Sylow involutions cannot embed in binary linear or unitary Sylow subgroups, while Suzuki order excludes three. Source: Aschbacher–Smith 2.5.19, pp.560–563.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private noncomputable def primeFieldLinearEquiv
    {E : Type*} [Group E] {p : ℕ} [Fact p.Prime]
    (hm : ClassicalGroup.IsPSL E 2 p) : E ≃* PSL(2,ZMod p) := Classical.choice <| by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod p) := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hcard
  exact ⟨e.trans (Atlas.fieldEquivPSL 2 (FiniteField.ringEquivOfCardEq hc))⟩

/-- The catalogue's Fermat–Mersenne field is a prime field. Thus its arbitrary
involutory actor has solvable fixed subgroup, including the outer actor. -/
theorem odd_prime_model_fixed_no_component
    {E : Type*} [Group E] [Group.IsPerfect E] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL E 2 p)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) : False := by
  have hp5 := Chapter16.OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hm
  let : Fact p.Prime := ⟨hp.1⟩
  exact prime_linear_model_fixed_no_component (p := p) (by omega)
    (primeFieldLinearEquiv hm) a ha B hB


/-- Both odd families in the literal 1.1.5 catalogue are excluded. The
PSL₃(3) carrier has exact order5616, and the PSL₂ family is over a prime field. -/
theorem source_odd_model_exclusion_of_prime
    {E : Type*} [Group E] [Group.IsPerfect E]
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL E 3 3 ∨
      ∃ q : ℕ,IsFermatOrMersennePrime q ∧ ClassicalGroup.IsPSL E 2 q)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : PSL(2,ZMod p) ≃* B) : False := by
  rcases hm with hm | ⟨q,hq,hm⟩
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hcard] at hc
    norm_num [Fin.prod_univ_succ] at hc
    have horder : Nat.card E = 5616 := by rw [Nat.card_congr e.toEquiv]; omega
    exact fermat_mersenne_pslTwo_no_injective_small_order hp hp7 (Or.inr (Or.inr horder))
      (a.fixedSubgroup.subtype.comp (B.subtype.comp eB.toMonoidHom))
      (a.fixedSubgroup.subtype_injective.comp (B.subtype_injective.comp eB.injective))
  · exact odd_prime_model_fixed_no_component hq hm a ha B hB

/-- The genuine Sylow two shape in source 2.5.8 excludes any embedding in a
group whose Sylow involutions commute. -/
theorem source_no_injective_commuting_sylow
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {D : Type*} [Group D] [Finite D] (P : Sylow 2 D)
    (hP : ∀ a b : P,a ^ 2 = 1 → b ^ 2 = 1 → Commute a b)
    (f : K →* D) (hf : Function.Injective f) : False := by
  let R : Sylow 2 K := default
  have hR := ((ComponentSelection.MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).sylowTwoShape R).rank_and_involutions.2
  obtain ⟨Q,hQ⟩ := (R.isPGroup'.map f).exists_le_sylow
  let e : Q ≃* P := Q.equiv P
  let r : R →* P := e.toMonoidHom.comp
    ((f.comp (R : Subgroup K).subtype).codRestrict Q
      (by intro x; exact hQ ⟨x,x.property,rfl⟩))
  have hr : Function.Injective r := by
    intro x y h
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val (e.injective h)
  apply hR
  intro x y hx hy
  apply hr
  simpa only [map_mul] using (hP (r x) (r y)
    (by rw [← map_pow,hx,map_one]) (by rw [← map_pow,hy,map_one])).eq

/-- The binary linear and unitary Bender carriers cannot contain the source
component; the Suzuki carrier is excluded by divisibility by three. -/
theorem source_bender_no_injective_of_prime
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : p.Prime) (eK : K ≃* PSL(2,ZMod p))
    {D : Type*} [Group D] [Finite D]
    (hm : ClassificationModels.IsBenderModel D)
    (f : K →* D) (hf : Function.Injective f) : False := by
  cases hm with
  | linear n hn iso =>
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := iso
    let P : Sylow 2 PSL(2,F) := default
    obtain ⟨v⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hcard P
    apply source_no_injective_commuting_sylow c hG hempty hgen hb P
      (fun a b _ _ => ?_) (e.toMonoidHom.comp f) (e.injective.comp hf)
    exact v.symm.injective (by simp only [map_mul]; exact mul_comm _ _)
  | unitary n hn iso =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := iso
    have impossible : False := by
      have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
        FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
      obtain ⟨v⟩ := exists_projectiveEquiv J (2 ^ n) hcard hfixed
      let J' := standardForm J
      let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J') :=
        Finite.of_injective Subtype.val Subtype.val_injective
      exact source_no_injective_commuting_sylow c hG hempty hgen hb
        (rootSylow J' rfl (by omega) hcard hfixed)
        (rootSylow_involutions_commute J' rfl (by omega) hcard hfixed)
        (v.toMonoidHom.comp (e.toMonoidHom.comp f)) (v.injective.comp (e.injective.comp hf))
    exact impossible
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    let : Fact p.Prime := ⟨hp⟩
    exact pslTwo_no_injective_three_free
      (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega))
      (e.toMonoidHom.comp (f.comp eK.symm.toMonoidHom))
      (e.injective.comp (hf.comp eK.symm.injective))

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
