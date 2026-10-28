module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.Involution
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.QuasithinBasic
public import Theory.PGroupCore

/-!
# Odd prime cores and involution centralizers of rank two

In a finite group of odd p-rank at most two, an involution fixing an
elementary plane centralizes every normal p-subgroup. Join the plane to
the normal subgroup. A nontrivial involutive action on that p-group would
have cyclic fixed subgroup, contradicting the fixed plane. Extracting an
elementary plane in the involution centralizer gives the intrinsic p-core
criterion, without a solvability assumption on the ambient group.

Source: Aschbacher--Smith, the O₃(H*) step of 12.6.26, printed p.832;
the cyclic-fixed-subgroup argument is A.1.31(1), printed pp.27--28.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- An involution fixing an elementary plane centralizes every normal p-subgroup
when the ambient odd-prime rank is at most two. -/
theorem fixed_plane_centralizes_normal_pSubgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hr : primeRank p G ≤ 2)
    (t : G) (ht : t ^ 2 = 1)
    (E R : Subgroup G) [IsElementaryAbelian p E] [R.Normal]
    (hE : Nat.card E = p ^ 2) (hR : IsPGroup p R)
    (hfix : E ≤ centralizer ({t} : Set G)) : t ∈ centralizer (R : Set G) := by
  let J := E ⊔ R
  have hJ : IsPGroup p J := (IsElementaryAbelian.isPGroup p E).to_sup_of_normal_right hR
  have htE : t ∈ normalizer (E : Set G) := centralizer_le_normalizer _
    (fun x hx => mem_centralizer_singleton_iff.mp (hfix hx))
  have htJ : t ∈ normalizer (J : Set G) :=
    normalizer_le_normalizer_sup_normal htE
  let a : MulAut J := J.normalizerMonoidHom ⟨t,htJ⟩
  have ha : Function.Involutive a := by
    intro x
    apply Subtype.ext
    change t * (t * x.val * t⁻¹) * t⁻¹ = x.val
    have h : t * t = 1 := by simpa only [pow_two] using ht
    calc
      _ = (t*t) * x.val * (t*t)⁻¹ := by group
      _ = x.val := by rw [h]; group
  have he : a = 1 := by
    by_contra hn
    let : IsCyclic a.fixedSubgroup := cyclic_fixedSubgroup_of_involution_rank_le_two
      hJ hp ((primeRank_le_of_injective p J.subtype J.subtype_injective).trans hr) a ha hn
    let f : E →* a.fixedSubgroup := {
      toFun x := ⟨⟨x.val,mem_sup_left x.property⟩,by
        apply (MulAut.mem_fixedSubgroup _ _).mpr
        apply Subtype.ext
        change t * x.val * t⁻¹ = x.val
        rw [(mem_centralizer_singleton_iff.mp (hfix x.property)).symm,mul_inv_cancel_right]⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hi : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun v : a.fixedSubgroup => ((v : J) : G)) h)
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hE (isCyclic_of_injective f hi)
  intro x hx
  have hh := congrArg (fun b : MulAut J => ((b ⟨x,mem_sup_right hx⟩ : J) : G)) he
  change t * x * t⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- A rank-two involution centralizer forces centralization of the odd p-core. -/
theorem involution_centralizes_pCore_of_centralizer_rank
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hr : primeRank p G ≤ 2)
    (t : G) (ht : t ^ 2 = 1)
    (hc : 2 ≤ primeRank p (centralizer ({t} : Set G))) :
    t ∈ centralizer (pCore p G : Set G) := by
  let C := centralizer ({t} : Set G)
  have he : primeRank p C = 2 := le_antisymm
    ((primeRank_le_of_injective p C.subtype C.subtype_injective).trans hr) hc
  obtain ⟨A,hA,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := p)
  let := hA
  let E := A.map C.subtype
  let : IsElementaryAbelian p E := IsElementaryAbelian.map_subtype
  have hE : Nat.card E = p ^ 2 := by
    rw [card_map_of_injective C.subtype_injective,hcard,he]
  exact fixed_plane_centralizes_normal_pSubgroup hp hr t ht E (pCore p G) hE
    pCore_isPGroup (map_subtype_le A)

end Theory.GroupTheory
