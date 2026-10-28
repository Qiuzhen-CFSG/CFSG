module
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.QuotientHyperplane

/-!
# Inverted odd rotations and quotient hyperplanes

If the image of an elementary TI subgroup V under a homomorphism has
order two, every image element is either identity or the image of a chosen
inverter. A nontrivial odd rotation inverted by that element therefore
satisfies the quotient sign condition, giving a literal index-two pair.
Source: Aschbacher–Smith, the construction after 12.2.21, printed p.802.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G K : Type*} [Group G] [Finite G] [Group K]

/-- Once the quotient image of V has order two, each nontrivial odd rotation
inverted by a member of V supplies a hyperplane pair. -/
theorem pair_normalizer_index_two_of_inverted_quotient_card_two
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hTI : IsTISubgroup V)
    (q : G →* K) (hk : q.ker ≤ normalizer (V : Set G))
    (hc : Nat.card (V.map q) = 2)
    (g v : G) (hv : v ∈ V) (ho : Odd (orderOf (q g))) (hg : q g ≠ 1)
    (hinv : v * g * v⁻¹ = g⁻¹) :
    (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2 := by
  have hi : q v * q g * (q v)⁻¹ = (q g)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg q hinv
  have hvq : q v ≠ 1 := by
    intro he
    have heq : q g = (q g)⁻¹ := by simpa only [he, one_mul, inv_one, mul_one] using hi
    have hsq : (q g)^2 = 1 := by
      rw [pow_two]
      calc
        q g * q g = (q g)⁻¹ * q g := congrArg (fun a => a * q g) heq
        _ = 1 := inv_mul_cancel _
    exact hg (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes ho.coprime_two_right
      dvd_rfl (orderOf_dvd_of_pow_eq_one hsq)))
  apply pair_normalizer_index_two_of_quotient_inverted_line V hTI q hk g v hv ho hg hi
  intro w hw
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : V.map q)).mp hc
  by_cases hwq : q w = 1
  · left
    simp only [hwq, one_mul, inv_one, mul_one]
  · have hwv : q w = q v := congrArg Subtype.val
      ((hz ⟨q w, mem_map_of_mem q hw⟩ (fun he => hwq (congrArg Subtype.val he))).trans
        (hz ⟨q v, mem_map_of_mem q hv⟩ (fun he => hvq (congrArg Subtype.val he))).symm)
    exact Or.inr (hwv ▸ hi)
end CFSG.Quasithin.ChapterI.Section06To08
