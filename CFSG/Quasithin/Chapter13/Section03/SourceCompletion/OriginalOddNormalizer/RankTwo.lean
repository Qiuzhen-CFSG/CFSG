module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.RankTwoResidualExclusions
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLocal
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeLocal
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SylowExponent
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank

/-!
# The characteristic-two component inspection for the unitary residual

The actual residual representation normalizes the nontrivial image of its
two-core. The linear-Levi and unitary-four parabolics cannot contain its
simple quotient with an element of order eight. The small derived endpoints
are excluded by the order of the whole residual. The only remaining rows
are PSU₅(4) and Ree; their literal local normalizers are excluded by seven
divisibility and the three-divisibility/two-exponent obstruction respectively.

Source: Aschbacher--Smith 4.4.12, printed pp.621--622.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4.Section04.NormalizedRankOneOddControl
open ClassificationModels BenderSuzuki.MatrixGroups
open scoped MatrixGroups

theorem unitary_original_rankTwo_remaining
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    (F K W : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (hd : 387072 ∣ Nat.card (K ⧸ center K))
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) :
    UnitaryFiveOrReeModel (K ⧸ center K) := by
  cases hm with
  | linear hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hn2 : 2 ≤ n := by
      by_contra h
      have he : n = 1 := by omega
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hcard,he] at hd
      norm_num at hd
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_linear_three_local hS hexp π hπ hn2 hcard _ hp hpne r hnorm
  | unitary_four hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.charP_two
      n (by omega) hcard
    obtain ⟨a⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
      J n (by omega) hcard hconj
    let t := e.trans a
    let r := residualQuotientMap hFK t
    let := residualQuotientMap_kernel_solvable hFK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm t
    exact no_unitary_four_local hS hexp π hπ J.conj J.conj_involutive
      n (by omega) hcard hconj _ hp hpne r hnorm
  | unitary_five hn hm => exact Or.inl (by simpa only [hn,show 2 ^ 2 = 4 from rfl] using hm)
  | symplectic hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := E)).symm
    let r := residualQuotientMap hFK a
    let := residualQuotientMap_kernel_solvable hFK a
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm a
    exact no_symplectic_four_local hS hexp π hπ _ hp hpne r hnorm
  | g2 hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hbig : 2 < Nat.card E := by
      rw [hcard]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_g2_local hS hexp π hπ hbig _ hp hpne r hnorm
  | triality hn hm =>
    exfalso
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hm
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hWF hne hcomm e
    exact no_triality_local hS hexp π hπ n (show 0 < n from hn) _ hp hpne r hnorm
  | ree_f4 m hm _ he => exact Or.inr ⟨m,hm,he⟩
  | symplectic_derived _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (ClassicalGroup.PSp 2 (ZMod 2))).card_subgroup_dvd_card
    rw [← Nat.card_congr
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2)).toEquiv,
      Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hd'
    norm_num at hd'
  | g2_derived _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,Nat.card_zmod] at hd'
    norm_num at hd'
  | tits _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd


/-- Neither full PSU₅(4) parabolic has an order divisible by seven. -/
theorem unitary_original_no_five_local
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (π : A →* S) (hπ : Function.Surjective π)
    (h7 : 7 ∣ Nat.card S)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Theory.SpecificGroups.UnitaryFive.finite_projective J
  obtain ⟨W,hn,hi,_,hNW⟩ :=
    Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
      J hJ (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  obtain ⟨b,g,hg⟩ := Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.transitive
    J hcard hconj hJ W hn hi
  have he : Theory.SpecificGroups.UnitaryFive.parabolic J W =
      (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
        else Theory.SpecificGroups.UnitaryFive.lineParabolic J).map
          (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)).toMonoidHom := by
    rw [hg, Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hNW
  let j := (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).toMonoidHom.comp r
  have hj : j.range ≤ (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
      else Theory.SpecificGroups.UnitaryFive.lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hNW (hr ⟨x,rfl⟩)
    change (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹ * r x *
      ((Theory.SpecificGroups.UnitaryFive.project J g)⁻¹)⁻¹ ∈ _
    rw [← he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
      have he : j x = 1 := congrArg Subtype.val hx
      exact (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).injective
        (he.trans (map_one _).symm))) (inclusion_injective _)
  have hd := h7.trans (SimpleSection.card_dvd_of_solvable_representation hS π hπ k)
  cases b
  · rw [if_neg Bool.false_ne_true,
      Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ] at hd
    norm_num at hd
  · rw [if_pos rfl,
      Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ] at hd
    norm_num at hd

/-- The actual binary derived group has a two-element with nontrivial square. -/
theorem unitary_original_not_two_exponent :
    ¬ ∀ P : Subgroup (commutator (Atlas.G2.Model (ZMod 2))),
      IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro h
  obtain ⟨x,hx⟩ := Atlas.G2.BinaryParabolicPair.derivedSylow_order_eight
  have hh := orderOf_dvd_of_pow_eq_one (h _ Atlas.G2.BinaryParabolicPair.derivedSylow.isPGroup' x)
  rw [hx] at hh
  norm_num at hh

/-- The original U₃(3) fixed residual excludes every rank-two B-model,
including the full general Ree family and the PSU₅(4) row. -/
theorem unitary_original_no_rankTwo_component
    {G : Type*} [Group G] [Finite G]
    (R K W : Subgroup G) [Group.IsPerfect R]
    (hRK : R ≤ K) (hWR : W ≤ R.pCoreIn 2) (hne : W ≠ ⊥) (hcomm : W = ⁅W,R⁆)
    (a : R ⧸ pCore 2 R ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hd : 387072 ∣ Nat.card (K ⧸ center K))
    {n : ℕ} (hm : IsRankTwoModel (K ⧸ center K) n) : False := by
  let S := commutator (Atlas.G2.Model (ZMod 2))
  let : IsSimpleGroup S := Atlas.G2.isSimple_commutator_binary
  let π : R →* S := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hπ : Function.Surjective π := a.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := π) hπ
  have hS := Group.IsPerfect.not_isSolvable S
  have h3 : 3 ∣ Nat.card S := by
    change 3 ∣ Nat.card Atlas.G2.LieAutomorphismExtensions.BinaryDerived
    rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]; norm_num
  have h7 : 7 ∣ Nat.card S := by
    change 7 ∣ Nat.card Atlas.G2.LieAutomorphismExtensions.BinaryDerived
    rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]; norm_num
  rcases unitary_original_rankTwo_remaining R K W hRK hWR hne hcomm hS
    unitary_original_not_two_exponent π hπ hd hm with h5 | ⟨m,hm,⟨e⟩⟩
  · obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := h5
    have hc : Nat.card E = 16 := hcard
    let := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hc
    obtain ⟨b⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hc hconj
    let t := e.trans b
    let r := residualQuotientMap hRK t
    let := residualQuotientMap_kernel_solvable hRK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hRK hWR hne hcomm t
    exact unitary_original_no_five_local hS π hπ h7
      (HermitianForm.IdentityGram.identityGram J) hc hconj rfl _ hp hpne r hnorm
  · let r := residualQuotientMap hRK e
    let := residualQuotientMap_kernel_solvable hRK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hRK hWR hne hcomm e
    exact no_ree_local_of_three_dvd hS unitary_original_not_two_exponent h3 π hπ
      hm _ hp hpne r hnorm

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion

