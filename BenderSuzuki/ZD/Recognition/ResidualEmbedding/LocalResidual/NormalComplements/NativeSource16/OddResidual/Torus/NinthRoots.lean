module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Torus
public import Theory.GroupAction.OddInvariantSylowConjugacy.AmbientChosen

/-!
# Order-nine witnesses in the chosen source residual

A cyclic marked torus with order divisible by nine supplies an order-nine
element in its three-core. Coprime invariant Sylow conjugacy embeds that
core into the exact Sylow already chosen for the Frattini argument. The
conjugator centralizes the full eight-group, preserving both fixed and
inverted actions. Thus the concrete witnesses survive the source's passage
from its two tori to Rᵤ and Rᵥ; the Sylow is not replaced.

Source: GLS IV, Chapter 2, Proposition 16.5, the R₀-embedding paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.NativeSource16
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Beyond the smallest square field, the source may choose a prime
other than three, or its three-core has an order-nine witness. -/
public theorem prime_ne_three_or_nine_dvd_binary_succ {m : ℕ} (hm : 1<m) :
    (∃ p : ℕ, p.Prime ∧ p≠3 ∧ p∣2^m+1) ∨ 9∣2^m+1 := by
  by_cases h9 : 9∣2^m+1
  · exact Or.inr h9
  apply Or.inl
  have hlarge : 3<2^m+1 := by
    have hh := Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) (show 2≤m by omega)
    norm_num at hh
    omega
  by_cases h3 : 3∣2^m+1
  · have he : (2^m+1)/3*3=2^m+1 := Nat.div_mul_cancel h3
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd
      (show (2^m+1)/3≠1 by intro hh; rw [hh] at he; omega)
    refine ⟨p,hp,?_,hd.trans (by exact ⟨3,he.symm⟩)⟩
    intro hp3
    subst p
    apply h9
    rw [← he]
    exact mul_dvd_mul hd (dvd_refl 3)
  · obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show 2^m+1≠1 by omega)
    exact ⟨p,hp,fun he => h3 (he ▸ hd),hd⟩

private theorem exists_order_nine_in_torus_threeCore (T : Subgroup G)
    (hT : IsCyclic T) (h9 : 9 ∣ Nat.card T) :
    ∃ x ∈ T.pCoreIn 3, orderOf x=9 := by
  let : IsCyclic T := hT
  let : CommGroup T := IsCyclic.commGroup
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hT
  let x : T := g ^ (orderOf g / 9)
  have hx : orderOf x=9 := orderOf_pow_orderOf_div
    (hg.symm ▸ Nat.card_pos.ne') (hg.symm ▸ h9)
  have hxp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers,hx]
    norm_num)
  have hle : zpowers x ≤ pCore 3 T := le_sSup ⟨inferInstance,hxp⟩
  exact ⟨x,⟨x,hle (mem_zpowers x),rfl⟩,(Subgroup.orderOf_coe x).trans hx⟩

/-- A marked source torus supplies an actual order-nine witness inside
the fixed commutator of any specified invariant Sylow of the odd core. -/
public theorem torus_order_nine_in_chosen_residual
    {Z : Set G} {M : Subgroup G} {t u v : G}
    (h : IsProductDisconnected Z M) (ht : t∈Z) (htM : t∉M)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWD : W≤residualPairStabilizer M t) (hWt : W≤centralizer ({t}:Set G))
    (hu : u∈W) (hv : v∈W) (hWgen : W=zpowers u⊔zpowers v)
    (T : Subgroup G) {m : ℕ} (hm : 0<m) (h9 : 9∣2^m+1)
    (hTcyc : IsCyclic T) (hTcard : Nat.card T=2^(2*m)-1)
    (hTD : T≤residualPairStabilizer M t) (hTu : T≤centralizer ({u}:Set G))
    (hTv : ∀x∈T,v*x*v⁻¹=x^(2^m)) (hTt : ∀x∈T,t*x*t⁻¹=x⁻¹)
    (P : Sylow 3 (residualOddCore M t))
    (hAP : W⊔zpowers t ≤ normalizer
      ((P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype)) :
    ∃ x ∈ OddInvolutionFrattini.Rw
        ((P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype) t u,
      orderOf x=9 ∧ Commute u x ∧ v*x*v⁻¹=x⁻¹ ∧ t*x*t⁻¹=x⁻¹ := by
  let A := W⊔zpowers t
  let Q := T.pCoreIn 3
  let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
  have htA : t∈A := mem_sup_right (mem_zpowers t)
  have huA : u∈A := mem_sup_left hu
  have hvA : v∈A := mem_sup_left hv
  let := residualFourActor_elementary (h.involutions t ht) W hWt
  have hAT := torus_fourActor_normalizes W T t u v hWgen hTu hTv hTt
  have hpdiv : 3∣2^m+1 := (by norm_num : 3∣9).trans h9
  obtain ⟨_,hQp,hQD,hAQ,hQu,hQv,hQt⟩ := torus_pCore_profile
    (residualPairStabilizer M t) A T t u v hm Nat.prime_three hpdiv
    hTcyc hTcard hTD hAT hTu hTv hTt
  have hQH := residualPair_full_commutator_le_oddCore h ht htM Q hQD hQt
  have hAH : A≤normalizer (residualOddCore M t) :=
    (sup_le_sup_right hWD _).trans
      (pair_sup_zpowers_le_normalizer_residualOddCore (h.involutions t ht))
  obtain ⟨c,hc,hQP⟩ := Theory.GroupAction.exists_ambient_fixed_conjugator_le_chosen_sylow
    (residualOddCore M t) A residualOddCore_odd (IsElementaryAbelian.isPGroup 2 A)
    hAH P hAP Q hQH hQp hAQ
  have hfix (a : G) (ha : a∈A) : MulAut.conj (c : G) a=a := by
    change (c : G)*a*(c : G)⁻¹=a
    rw [← hc a ha,mul_inv_cancel_right]
  have hQR := map_le_fixed_commutator_of_full_commutator P₁ Q t u (MulAut.conj (c : G))
    (hfix t htA) (hfix u huA) hQP hQu hQt
  have h9T : 9∣Nat.card T := by
    have hf : 2^(2*m)-1=(2^m-1)*(2^m+1) := by
      rw [mul_comm 2 m,pow_mul]
      have hn : 1≤2^m := Nat.one_le_pow m 2 (by decide)
      have hs := Nat.sub_add_cancel hn
      have hs2 := Nat.sub_add_cancel (show 1≤(2^m)^2 by nlinarith)
      nlinarith
    rw [hTcard,hf]
    exact dvd_mul_of_dvd_right h9 _
  obtain ⟨x,hx,hxo⟩ := exists_order_nine_in_torus_threeCore T hTcyc h9T
  let f := MulAut.conj (c : G)
  refine ⟨f x,hQR (mem_map_of_mem f.toMonoidHom hx),(f.orderOf_eq x).trans hxo,?_,?_,?_⟩
  · have he := congrArg f (mem_centralizer_singleton_iff.mp (hQu hx)).symm
    change u*f x=f x*u
    simpa only [map_mul,show f u=u from hfix u huA] using he
  · have he := congrArg f (hQv x hx)
    simpa only [map_mul,map_inv,show f v=v from hfix v hvA] using he
  · have he := congrArg f (hTt x (pCoreIn_le 3 T hx))
    simpa only [map_mul,map_inv,show f t=t from hfix t htA] using he

end BenderSuzuki.ZD.NativeSource16
