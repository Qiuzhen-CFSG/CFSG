module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.SourceLists
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.OddSubgroups
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.JankoTwo
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.Rudvalis
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Suzuki.OddSubgroups

/-!
# Intersection with the nonsimple-cover quotients

The A.3.8(3) orbit list and the eight quotients of 16.1.2(1) intersect only
in Sz(8). The other linear, exceptional and Mathieu/HS models have orders
incompatible with every PSL₂, with the three-free Suzuki groups, and with
J₁. The actual J₂ and Ru carriers contain noncyclic three- and five-subgroups.
Such subgroups cannot occur in any source model: their Sylow subgroups are
cyclic in the linear and Suzuki cases, while the prime squares do not divide
J₁'s certified order. The binary linear comparison allows every exponent
at least two, as required by A.3.8(3).

This proves the model comparison used in the nontrivial-two-core branch of
16.2.5. The central-quotient identification and the nontriviality of that core
remain with the counterexample assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.8(3), pp.45–46; 16.1.2(1), p.1170; and 16.2.5, p.1174.
The imported matrix-order and sporadic-subgroup certificates retain their
source attribution in their owning modules.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
open ClassificationModels BenderSuzuki.MatrixGroups
open Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
universe u
variable {S : Type u} [Group S]

private theorem not_source_of_card {c a b : ℕ} (hc : Nat.card S = c)
    (hthree : 3 ∣ c) (hj : c ≠ 175560)
    (ha : a * (a ^ 2 - 1) < c) (ha' : c < (a+1)*((a+1)^2-1))
    (hb : b * (b ^ 2 - 1) < 2*c) (hb' : 2*c < (b+1)*((b+1)^2-1)) :
    ¬ SourceOrbitModel S := by
  intro hs
  cases hs with
  | linear_even n hn iso =>
    exact psl_two_card_ne_of_gaps iso ha ha' hb hb' hc
  | linear_odd p hp hlarge iso =>
    exact psl_two_card_ne_of_gaps iso ha ha' hb hb' hc
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    apply suzukiMatrixGroup_three_free m (by omega)
    rwa [← Nat.card_congr e.toEquiv, hc]
  | janko_one iso =>
    obtain ⟨e⟩ := iso
    exact hj (hc.symm.trans ((Nat.card_congr e.toEquiv).trans Janko1.card_model))

/-- The binary branch retains every exponent at least two. -/
private theorem binary_odd_subgroup_cyclic [Finite S] {r n : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hn : 2 ≤ n) (P : Subgroup S) (hP : IsPGroup r P)
    (hm : ClassicalGroup.IsPSL S 2 (2 ^ n)) : IsCyclic P := by
  by_cases hn2 : n = 2
  · exact ordinary_rank_one_odd_subgroup_cyclic hr P hP
      (Or.inl ⟨n, hn2 ▸ (by decide : Even 2), rfl⟩) hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨R, hR⟩ := (hP.map e.toMonoidHom).exists_le_sylow
  have hseven : 7 ≤ Nat.card F := by
    rw [hF]
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ n by omega)
    norm_num at hpow ⊢
    omega
  let : IsCyclic R := GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
    F hF hseven r hr (by
      rw [hF]
      exact ((Nat.coprime_primes (Fact.out : r.Prime) Nat.prime_two).mpr hr).pow_right n) R
  exact (MulEquiv.subgroupMap e P).isCyclic.mpr (Subgroup.isCyclic_of_le hR)

/-- The two primes used by the sporadic witnesses have cyclic subgroups
in every source model, including J₁ because their squares do not divide its order. -/
private theorem source_odd_subgroup_cyclic [Finite S] {r : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hsq : ¬ r ^ 2 ∣ 175560) (hs : SourceOrbitModel S)
    (P : Subgroup S) (hP : IsPGroup r P) : IsCyclic P := by
  cases hs with
  | linear_even n hn iso => exact binary_odd_subgroup_cyclic hr hn P hP iso
  | linear_odd p hp hlarge iso =>
    exact ordinary_rank_one_odd_subgroup_cyclic hr P hP
      (Or.inr ⟨hp, hp.odd_of_ne_two (by omega)⟩) iso
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    obtain ⟨R, hR⟩ := (hP.map e.toMonoidHom).exists_le_sylow
    let : IsCyclic R := suzukiSylow_isCyclic_of_ne_two (by omega) hr R
    exact (MulEquiv.subgroupMap e P).isCyclic.mpr (Subgroup.isCyclic_of_le hR)
  | janko_one iso =>
    obtain ⟨e⟩ := iso
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    have hk1 : k ≤ 1 := by
      by_contra hn
      apply hsq
      rw [← Janko1.card_model, ← Nat.card_congr e.toEquiv]
      exact (hk ▸ pow_dvd_pow r (show 2 ≤ k by omega)).trans P.card_subgroup_dvd_card
    apply isCyclic_of_card_dvd_prime (p := r)
    rw [hk]
    simpa using pow_dvd_pow r hk1

private theorem not_source_psl_three_four (hs : SourceOrbitModel S)
    (hm : ClassicalGroup.IsPSL S 3 4) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact not_source_of_card (c := 20160) (a := 27) (b := 34) (by omega)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hs

private theorem not_source_g2_four (hs : SourceOrbitModel S)
    (hm : IsG2At S 4) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, hF] at hc
  norm_num at hc
  exact not_source_of_card (c := 251596800) (a := 631) (b := 795) hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hs

private theorem not_source_sporadic (name : SporadicName) [Finite name.Carrier]
    (hn : name = .m12 ∨ name = .m22 ∨ name = .j2 ∨ name = .hs ∨ name = .ru)
    (hs : SourceOrbitModel name.Carrier) : False := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact not_source_of_card (a := 45) (b := 57) Sporadic.Mathieu.m12_order
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hs
  · exact not_source_of_card (a := 76) (b := 96) Sporadic.Mathieu.m22_order
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hs
  · obtain ⟨P, hP, hnc⟩ := j2_noncyclic_three_subgroup
    exact hnc (source_odd_subgroup_cyclic (r := 3) (by decide) (by norm_num) hs P hP)
  · exact not_source_of_card (a := 353) (b := 445)
      Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hs
  · obtain ⟨P, hP, hnc⟩ := rudvalis_noncyclic_five_subgroup
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact hnc (source_odd_subgroup_cyclic (r := 5) (by decide) (by norm_num) hs P hP)

/-- The intersection of the A.3.8(3) models with the nonsimple-cover
quotients of 16.1.2(1) consists only of the actual Sz(8) model. -/
theorem covered_model_intersection [Finite S] (hs : SourceOrbitModel S) (hc : NonsimpleSourceModel S) :
    Nonempty (S ≃* SuzukiMatrixGroup 1) := by
  rcases hc with iso | iso | iso | ⟨name, hn, ⟨e⟩⟩
  · exact iso
  · exact (not_source_psl_three_four hs iso).elim
  · exact (not_source_g2_four hs iso).elim
  · let : Finite name.Carrier := Finite.of_equiv S e.toEquiv
    exact (not_source_sporadic name hn (hs.of_mulEquiv e.symm)).elim

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
end
