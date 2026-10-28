module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.Assembly
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# The actual Theorem C list has no C4 times C4 Sylow

The order sieve leaves the small linear, alternating and sporadic models.
Odd PSL2 has dihedral Sylow; odd PSL3 and PSU3 have cyclic Sylow center.
Binary PSL2 has elementary Sylow. Alternating degrees at most seven and
J1 have smaller two-part, whereas M11 has an order-eight rotation.
All contradictions use the actual carrier maps of the source catalogue.

This excludes the exceptional proper-residual Sylow in the wreathed
branch of Aschbacher--Smith F.6.18(10), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.AbelianSixteen
variable {G : Type*} [Group G] [Finite G]
private abbrev Model := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
private theorem model_card : Nat.card Model = 16 := by norm_num [Model, Nat.card_prod]

private theorem commutative_of_model {P : Type*} [Group P] (e : P ≃* Model) :
    IsMulCommutative P := by
  apply IsMulCommutative.of_comm
  intro x y
  apply e.injective
  simp only [map_mul, mul_comm]

private theorem not_cyclic_model : ¬ IsCyclic Model := by
  intro h
  let := h
  have he : Monoid.exponent Model ∣ 4 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)
  rw [IsCyclic.exponent_eq_card, model_card] at he
  norm_num at he

private theorem not_cyclic_center {P : Type*} [Group P] (e : P ≃* Model) :
    ¬ IsCyclic (center P) := by
  intro h
  let := h
  let := commutative_of_model e
  let a : center P ≃* Model := ((MulEquiv.subgroupCongr (center_eq_top (G := P))).trans topEquiv).trans e
  exact not_cyclic_model (isCyclic_of_surjective a.toMonoidHom a.surjective)

private theorem no_thirty_two (P : Sylow 2 G) (eP : P ≃* Model) : ¬32 ∣ Nat.card G := by
  intro hd
  have hc := (Nat.card_congr eP.toEquiv).trans model_card
  have hb := Nat.le_of_dvd (Nat.card_pos (α := P))
    (P.pow_dvd_card_of_pow_dvd_card (n := 5) hd)
  omega

private theorem not_odd_psl (P : Sylow 2 G) (eP : P ≃* Model)
    {q : ℕ} (hq : GorensteinWalter.IsOddPrimePower q)
    (hm : ClassicalGroup.IsPSL G 2 q) : False := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  let S := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let a : P ≃* S := j.subgroupMap (P : Subgroup G)
  obtain ⟨m, _, ⟨b⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F (hF ▸ hq) S
  let c := (a.trans b).symm.trans eP
  have hc := Nat.card_congr c.toEquiv
  rw [DihedralGroup.nat_card, model_card] at hc
  have hm : 2 ^ m = 8 := by omega
  exact DihedralGroup.not_commutative (by omega) (by omega) (commutative_of_model c)

private theorem not_even_psl (P : Sylow 2 G) (eP : P ≃* Model)
    {f : ℕ} (hm : ClassicalGroup.IsPSL G 2 (2 ^ f)) : False := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let S := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F
  let a : Multiplicative F ≃* S :=
    (MonoidHom.ofInjective
      (Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom_injective F)).trans
      (MulEquiv.subgroupCongr
        (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.coe_standardSylow F).symm)
  let : IsElementaryAbelian 2 (Multiplicative F) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      simp [pow_two, CharTwo.add_self_eq_zero]) }
  let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_surjective a.toMonoidHom a.surjective
  let U := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let b : P ≃* S := (j.subgroupMap (P : Subgroup G)).trans (U.equiv S)
  let : IsElementaryAbelian 2 Model :=
    IsElementaryAbelian.of_surjective (b.symm.trans eP).toMonoidHom (b.symm.trans eP).surjective
  have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 Model) ((Multiplicative.ofAdd 1), 1)
  exact (by decide : (((Multiplicative.ofAdd 1), 1) : Model) ^ 2 ≠ 1) hh

private theorem not_alternating (P : Sylow 2 G) (eP : P ≃* Model)
    {n : ℕ} (hn : n ≤ 8) (j : G ≃* alternatingGroup (Fin n)) : False := by
  by_cases hn8 : n = 8
  · subst n
    apply no_thirty_two P eP
    rw [Nat.card_congr j.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  · have hdiv : 16 ∣ Nat.card G := by
      rw [← model_card, ← Nat.card_congr eP.toEquiv]
      exact P.card_subgroup_dvd_card
    rw [Nat.card_congr j.toEquiv] at hdiv
    by_cases h2 : 2 ≤ n
    · let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h2
      rw [nat_card_alternatingGroup, Nat.card_fin] at hdiv
      have h7 : n ≤ 7 := by omega
      interval_cases n <;> norm_num [Nat.factorial] at hdiv
    · have hh := hdiv.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hh
      have hn1 : n ≤ 1 := by omega
      interval_cases n <;> norm_num [Nat.factorial] at hh


private theorem not_sporadic (P : Sylow 2 G) (eP : P ≃* Model)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel G) : False := by
  rcases hm with ⟨name,hne,⟨e⟩⟩ | hJ
  · by_cases h11 : name = .m11
    · subst name
      obtain ⟨S,a,b,ha,_,_,_⟩ := Sporadic.Mathieu.m11_exists_semidihedral_sylow
      let U := P.mapSurjective (f := e.toMonoidHom) e.surjective
      let j : S ≃* Model := (S.equiv U).trans ((e.subgroupMap (P : Subgroup G)).symm.trans eP)
      have hp : (j a) ^ 4 = 1 := by
        have hall : ∀ x : Model, x ^ 4 = 1 := by decide +kernel
        exact hall _
      have hd := orderOf_dvd_of_pow_eq_one hp
      rw [j.orderOf_eq, ha] at hd
      norm_num at hd
    · apply no_thirty_two P eP
      rw [Nat.card_congr e.toEquiv]
      exact SplitSixteen.thirty_two_dvd_sporadic_name name hne h11
  · obtain ⟨e⟩ := hJ
    have hd : 16 ∣ Nat.card G := by
      rw [← model_card, ← Nat.card_congr eP.toEquiv]
      exact P.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv, Janko1.card_model] at hd
    norm_num at hd

/-- The complete actual source catalogue excludes the abelian Sylow C4×C4. -/
theorem not_theoremC_model (P : Sylow 2 G)
    (eP : P ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hm : ChapterA.Section02.IsTheoremCModel G) : False := by
  have hP : Nat.card P ≤ 16 := ((Nat.card_congr eP.toEquiv).trans model_card).le
  have prime_case (p : ℕ) (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL G 2 p) : False :=
    not_odd_psl P eP ⟨p,1,hp,ho,by decide,by simp⟩ hm
  cases hm with
  | alternating n hn iso => exact not_alternating P eP hn iso.some
  | odd model =>
    cases model with
    | linear_two p f hp ho _ iso =>
      have hfpos : 0 < f := by
        obtain ⟨F, _, _, hc, _⟩ := iso
        have hcard : 1 < Nat.card F := Finite.one_lt_card
        by_contra! hh
        have hz : f = 0 := by omega
        simp [hz] at hc
        omega
      exact not_odd_psl P eP ⟨p,f,hp,ho,hfpos,rfl⟩ iso
    | linear_three p hp ho iso =>
      let : Fact p.Prime := ⟨hp⟩
      exact not_cyclic_center eP
        (Chapter1.XiEmbedding.InvariantLarge.OddCartan.isPSL_sylow_center_cyclic ho iso P)
    | unitary_three p hp ho iso =>
      let : Fact p.Prime := ⟨hp⟩
      exact not_cyclic_center eP
        (Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition.isPSU_sylow_center_cyclic p ho iso P)
  | bender model =>
    cases model with
    | linear f _ iso => exact not_even_psl P eP iso
    | unitary f hf iso => exact SplitSixteen.not_unitary_three_binary_of_sylow_le_sixteen P hP hf iso
    | suzuki m hm iso => exact SplitSixteen.not_suzuki_of_sylow_le_sixteen P hP hm iso
  | rank_two f model =>
    rcases SplitSixteen.rankTwo_models_of_sylow_le_sixteen P hP model with hm | hm
    · exact prime_case 7 (by decide) (by decide) hm
    · exact not_alternating P eP (by decide : 6 ≤ 8) hm.some
  | linear_binary n hn model =>
    exact SplitSixteen.not_binary_four_or_five_of_sylow_le_sixteen P hP hn model
  | sporadic model => exact not_sporadic P eP model

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.AbelianSixteen
