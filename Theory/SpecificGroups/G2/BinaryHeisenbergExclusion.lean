module
public import Theory.AtlasPort.LinearGroups.G2.BinaryLocalResidual
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.PResidual.TwoCoreOddDivisors
public import Theory.GroupAction.SimpleCosets
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# No odd-index Heisenberg residual in a binary derived G₂ automorphism overgroup

For Q ≅ G₂(2)′ and Inn(Q) ≤ A ≤ Aut(Q), the order of A is 6048 or 12096.
If M ≤ A has odd index and O²(M/O₂(M)) ≅ 3¹⁺², then |M| = 27 · 2ⁿ,
so its index is seven. The pullback of M under inner conjugation is proper:
otherwise seven would divide |M|. Its index is at most seven. Simplicity
would therefore embed Q in a symmetric group of degree at most seven,
contradicting 6048 ∤ 7!.

This excludes the small derived G₂ row in Aschbacher–Smith 14.7.26,
printed p.1053 of refs/quasithin.pdf. The concrete octonion model and its
order, simplicity and automorphism results retain their imported ATLAS
attribution; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryLocalResidual
variable {Q : Type*} [Group Q] [Finite Q]

private theorem residual_card (M : Type*) [Group M] [Finite M]
    (hr : Nat.card (pResidual 2 (M ⧸ pCore 2 M)) = 27) :
    ∃ n : ℕ, Nat.card M = 27 * 2^n := by
  obtain ⟨a,ha⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
  obtain ⟨b,hb⟩ := (isPGroup_quotient_pResidual (G := M ⧸ pCore 2 M) 2).exists_card_eq
  have hq : Nat.card (M ⧸ pCore 2 M) = 27 * 2^b := by
    simpa only [hr,index_eq_card,hb] using (pResidual 2 (M ⧸ pCore 2 M)).card_mul_index.symm
  refine ⟨a+b,?_⟩
  have hh := (pCore 2 M).card_mul_index
  rw [ha,index_eq_card,hq] at hh
  rw [←hh,pow_add]
  ring

/-- The literal odd-index local subgroup cannot have the marked Heisenberg residual. -/
theorem no_odd_index_heisenberg
    (e : Q ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (M : Subgroup A) (ho : Odd M.index)
    (he : Nonempty (pResidual 2 (M ⧸ pCore 2 M) ≃* HeisenbergPrime 3)) : False := by
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup Q := e.isSimpleGroup
  have hQ : Nat.card Q = 6048 := (Nat.card_congr e.toEquiv).trans
    LieAutomorphismExtensions.card_binaryDerived
  have hz : center Q = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (commutator (Atlas.G2.Model (ZMod 2))) at hh
    rw [center_eq_bot,mem_bot] at hh
    exact mem_bot.mpr (e.map_eq_one_iff.mp hh)
  have hi : (MulAut.innerSubgroup Q).index ∣ 2 := by
    change Nat.card (MulAut.Outer Q) ∣ 2
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact outer_card_dvd_two
  let I := (MulAut.innerSubgroup Q).subgroupOf A
  have hI : Nat.card I = 6048 :=
    (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans
      ((Nat.card_congr (MonoidHom.ofInjective
        (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)).toEquiv).symm.trans hQ)
  have hiI : I.index ∣ 2 := (relIndex_dvd_index_of_normal (MulAut.innerSubgroup Q) A).trans hi
  have hAc : Nat.card A = 6048 ∨ Nat.card A = 12096 := by
    have hh := I.card_mul_index
    rw [hI] at hh
    rcases (Nat.dvd_prime Nat.prime_two).mp hiI with hc | hc
    · left; rw [hc,mul_one] at hh; exact hh.symm
    · right; rw [hc] at hh; exact hh.symm
  obtain ⟨r⟩ := he
  have hr : Nat.card (pResidual 2 (M ⧸ pCore 2 M)) = 27 :=
    (Nat.card_congr r.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hseven : ¬ 7 ∣ Nat.card M := by
    intro hd
    have hh := odd_prime_dvd_twoCore_quotient_residual (by decide : Nat.Prime 7) (by decide) hd
    rw [hr] at hh
    norm_num at hh
  obtain ⟨n,hn⟩ := residual_card M hr
  have hi7 : M.index = 7 := by
    have hh := M.card_mul_index
    rw [hn] at hh
    have heq : ∃ k : ℕ, 2^n * M.index = 2^k * 7 := by
      rcases hAc with hc | hc
      · refine ⟨5,?_⟩; rw [hc] at hh; nlinarith
      · refine ⟨6,?_⟩; rw [hc] at hh; nlinarith
    obtain ⟨k,hk⟩ := heq
    have hcop : Nat.Coprime M.index (2^k) :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr ho.not_two_dvd_nat).symm.pow_right k
    have hcop7 : Nat.Coprime 7 (2^n) := (by decide : Nat.Coprime 7 2).pow_right n
    exact Nat.dvd_antisymm
      (hcop.dvd_of_dvd_mul_left (hk ▸ dvd_mul_left M.index (2^n)))
      (hcop7.dvd_of_dvd_mul_left (hk.symm ▸ dvd_mul_left 7 (2^k)))
  let f : Q →* A := (MulAut.conj : Q →* MulAut Q).codRestrict A
    (fun q => hA ⟨q,rfl⟩)
  have hf : Function.Injective f := fun _ _ hh =>
    (Theory.GroupTheory.conj_injective_of_center_eq_bot hz) (congrArg Subtype.val hh)
  let J := M.comap f
  have hJ : J ≠ ⊤ := by
    intro htop
    let fM : Q →* M := f.codRestrict M (fun q => show f q ∈ M from
      (show q ∈ J from htop ▸ mem_top q))
    have hinj : Function.Injective fM := fun _ _ hh => hf (congrArg Subtype.val hh)
    have hd := card_dvd_of_injective fM hinj
    rw [hQ] at hd
    exact hseven ((by decide : 7 ∣ 6048).trans hd)
  have hindex : J.index ≤ 7 := by
    rw [show J.index = M.relIndex f.range from index_comap M f]
    have hh := relIndex_le_of_le_right (H := M) (show f.range ≤ ⊤ from le_top)
      (show M.relIndex ⊤ ≠ 0 by simpa using (index_ne_zero_of_finite (H := M)))
    simpa only [relIndex_top_right,hi7] using hh
  have hd := (J.card_dvd_factorial_index_of_simple hJ).trans (Nat.factorial_dvd_factorial hindex)
  rw [hQ] at hd
  norm_num [Nat.factorial] at hd
end Atlas.G2.BinaryLocalResidual
