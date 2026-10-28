module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive.PrimaryCoordinates
public import Theory.GroupTheory.Fitting.InnerRestrictions

/-!
# The full outer group in the nilpotent SL₂(5) alternative

Combine the primary coordinates over the prime support of F(B). The original
B-action has the same Fitting kernel in every coordinate, hence its full image
is the actual SL₂(5) quotient, with compatible projections. Its centralizer in
the matrix product is central. Its normalizer quotient is therefore nilpotent,
since Out(SL₂(5)) is a two-group.

The kernel of the automorphism coordinate map is inner: its prime restrictions
are inner in their respective cores, these conjugators assemble on F(B), and
the proved Fitting-restriction theorem disposes of the remaining kernel.
Thus Out(B) embeds in that nilpotent normalizer quotient. All allowed primes,
extraspecial cores and positive homocyclic exponents remain, and no splitting
of the extension is assumed.

Source: Aschbacher--Smith A.3.6(4), pp.43--45; 11.4.3, p.778.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive

/-- The complete mixed-prime calculation under the original intrinsic hypotheses. -/
theorem outer_nilpotent
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    {𝒦 : GroupClass} (hQ : IsSQTK 𝒦 B)
    (h : A36Nilpotent B) (hc : A36Common B) :
    Group.IsNilpotent (MulAut.Outer B) := by
  classical
  by_cases hcard : Nat.card (fittingSubgroup B) = 1
  · have hbot : fittingSubgroup B = ⊥ := eq_bot_of_card_eq _ hcard
    have hall : (⊤ : Subgroup B) ≤ ⊥ := by
      rw [← hbot]
      intro b _
      apply fitting_selfCentralizing h
      intro x hx
      rw [show x = 1 from mem_bot.mp (hbot ▸ hx), one_mul, mul_one]
    let : Subsingleton B := ⟨fun x y =>
      (mem_bot.mp (hall (mem_top x))).trans (mem_bot.mp (hall (mem_top y))).symm⟩
    let : Subsingleton (MulAut B) := ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    infer_instance
  let I := {p : ℕ // p ∈ (Nat.card (fittingSubgroup B)).primeFactors}
  have prime (p : I) : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
  let (p : I) : Fact p.val.Prime := ⟨prime p⟩
  have divides (p : I) : p.val ∣ Nat.card (fittingSubgroup B) :=
    Nat.dvd_of_mem_primeFactors p.property
  let C (p : I) : PrimaryCoordinates B p.val :=
    Classical.choice (exists_primaryCoordinates h hc (divides p))
  let (p : I) : NeZero (C p).modulus := ⟨(C p).positive.ne'⟩
  let D (p : I) := GL (Fin 2) (ZMod (C p).modulus)
  let f : MulAut B →* ∀ p : I, D p :=
    MonoidHom.pi (fun p => (C p).action.comp (MulAut.characteristic (pCore p.val B)))
  let ρ := f.comp (MulAut.conj : B →* MulAut B)
  have heval (p : I) (b : B) : ρ b p = (C p).action (MulAut.conjNormal b) := by
    change (C p).action (MulAut.characteristic (pCore p.val B) (MulAut.conj b)) = _
    rw [characteristic_conj_eq_conjNormal]
  obtain ⟨p₀, hp₀, hd₀⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hcard
  let i₀ : I := ⟨p₀, Nat.mem_primeFactors.mpr ⟨hp₀, hd₀, Nat.card_pos.ne'⟩⟩
  have hk : ρ.ker = fittingSubgroup B := by
    apply le_antisymm
    · intro b hb
      rw [← (C i₀).action_kernel]
      change (C i₀).action (MulAut.conjNormal b) = 1
      rw [← heval]
      exact congrFun hb i₀
    · intro b hb
      change ρ b = 1
      funext p
      rw [heval]
      exact show b ∈ ((C p).action.comp MulAut.conjNormal).ker from
        (C p).action_kernel.symm ▸ hb
  have hfk : f.ker ≤ MulAut.innerSubgroup B := by
    intro α hα
    have hcores : ∀ p : ℕ, p.Prime → ∃ c : pCore p B,
        MulAut.characteristic (pCore p B) α = MulAut.conj c := by
      intro p hp
      let : Fact p.Prime := ⟨hp⟩
      by_cases hd : p ∣ Nat.card (fittingSubgroup B)
      · let i : I := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.card_pos.ne'⟩⟩
        have hh : MulAut.characteristic (pCore p B) α ∈ (C i).action.ker :=
          congrFun hα i
        obtain ⟨c, hc⟩ := (C i).inner_kernel hh
        exact ⟨c, hc.symm⟩
      · have hcb : pCore p B = ⊥ := by
          rcases (pCore_isPGroup (p := p) (G := B)).card_eq_or_dvd with hh | hh
          · exact eq_bot_of_card_eq _ hh
          · exact (hd (hh.trans (card_dvd_of_le (pCore_le_fitting B p)))).elim
        let : Subsingleton (pCore p B) := ⟨fun x y => Subtype.ext
          ((mem_bot.mp (hcb ▸ x.property)).trans (mem_bot.mp (hcb ▸ y.property)).symm)⟩
        exact ⟨1, MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    obtain ⟨b, hb⟩ := inner_on_fitting_of_inner_on_cores α hcores
    have hcorr : MulAut.conj b⁻¹ * α ∈ (MulAut.characteristic (fittingSubgroup B)).ker := by
      change MulAut.characteristic (fittingSubgroup B) (MulAut.conj b⁻¹ * α) = 1
      rw [map_mul, characteristic_conj_eq_conjNormal, hb, map_inv, inv_mul_cancel]
    have hi := fitting_restriction_kernel hQ h hc hcorr
    have hαeq : α = MulAut.conj b * (MulAut.conj b⁻¹ * α) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [hαeq]
    exact (MulAut.innerSubgroup B).mul_mem ⟨b, rfl⟩ hi
  have hcentral : centralizer (ρ.range : Set (∀ p : I, D p)) ≤ center (∀ p : I, D p) := by
    intro c hc
    apply mem_center_iff.mpr
    intro y
    funext p
    have hpcentral : c p ∈ centralizer
        (((C p).action.comp (MulAut.conjNormal : B →* MulAut (pCore p.val B))).range : Set (D p)) := by
      rintro _ ⟨b, rfl⟩
      have hh := congrFun (hc (ρ b) ⟨b, rfl⟩) p
      simpa only [Pi.mul_apply, heval, MonoidHom.comp_apply] using hh
    exact mem_center_iff.mp ((C p).centralizer hpcentral) (y p)
  have hpodd : Odd p₀ := hp₀.odd_of_ne_two (by
    intro he
    have hp := (h.2.2.2 p₀ hp₀ (h.1.symm ▸ hd₀)).1
    norm_num [he] at hp)
  let : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨E, _⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient h hpodd hd₀
  let ER : ρ.range ≃* SL(2, ZMod 5) :=
    (QuotientGroup.quotientKerEquivRange ρ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk.trans h.1.symm)).trans E)
  apply NormalizerOuterQuotient.nilpotent_quotient_of_map (MulAut.innerSubgroup B) f hfk
  change Group.IsNilpotent (NormalizerOuterQuotient.Quotient
    (((MulAut.conj : B →* MulAut B).range).map f))
  rw [← MonoidHom.range_comp]
  exact NormalizerOuterQuotient.nilpotent_of_centralizer_le_center ρ.range hcentral
    (slFive_outer_two.of_equiv (MulAut.outerCongr ER).symm)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive
