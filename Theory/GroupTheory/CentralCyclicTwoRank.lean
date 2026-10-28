module
public import Theory.GroupTheory.PGroup.BinaryCommutatorIndex
public import Theory.GroupTheory.PGroup.NormalAbelian
public import Theory.Frattini.SubgroupIndexBound
public import Theory.Frattini.SquareImage
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Quasithin.Rank

/-!
# Two-rank through central cyclic quotients

Lifting an elementary two-subgroup to a Sylow subgroup makes every commutator
central of order at most two. A maximal abelian self-centralizer has index
bounded by its first omega order. Its omega order and the Frattini index then
bound the elementary quotient by the square of the cover's elementary-rank
bound. This supplies the central-quotient step for odd classical Theorem B
models in Aschbacher–Smith 4.4.3, printed p.622.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CentralCyclicRank

variable {P E : Type*} [Group P] [Finite P] [Group E]
  [IsElementaryAbelian 2 E]

/-- A central cyclic elementary quotient of a two-group has bounded order. -/
theorem elementary_quotient_card_le {n : ℕ} (hP : IsPGroup 2 P)
    (f : P →* E) (hf : Function.Surjective f) (hc : f.ker ≤ center P)
    [IsCyclic f.ker] (hr : primeRank 2 P ≤ n) : Nat.card E ≤ 2 ^ (2 * n) := by
  classical
  let : CommGroup f.ker := IsMulCommutative.instCommGroup
  have hcomm (x y : P) : ⁅x, y⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have hsq (x : P) : x ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) _
  have hcomm2 (x y : P) : ⁅x, y⁆ ^ 2 = 1 := by
    have hs : ⁅x ^ 2, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp (hc (hsq x)) y).symm
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp (hc (hcomm x y)) x, mul_inv_cancel_right, ← pow_two] at hs
    exact hs
  let sq : f.ker →* f.ker := powMonoidHom 2
  let Z : Subgroup P := sq.ker.map f.ker.subtype
  have hZker : Z ≤ f.ker := map_subtype_le _
  have hZcentral : Z ≤ center P := hZker.trans hc
  have hDZ : _root_.commutator P ≤ Z := by
    apply commutator_le.mpr
    intro x _ y _
    exact ⟨⟨⁅x,y⁆, hcomm x y⟩, Subtype.ext (hcomm2 x y), rfl⟩
  let : IsCyclic Z := isCyclic_of_injective (inclusion hZker) (inclusion_injective hZker)
  have hZexp : Monoid.exponent Z ∣ 2 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨x, z, hz, rfl⟩
    apply Subtype.ext
    exact congrArg (fun a : f.ker => (a : P)) (show z ^ 2 = 1 from hz)
  have hZcard : Nat.card Z = 1 ∨ Nat.card Z = 2 := by
    rw [IsCyclic.exponent_eq_card] at hZexp
    exact (Nat.dvd_prime Nat.prime_two).mp hZexp
  obtain ⟨A, hAn, hAc, hCA⟩ := exists_normal_abelian_selfCentralizing hP
  let : IsMulCommutative A := hAc
  let : IsElementaryAbelian 2 (omega₁ A (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hO : Nat.card (omega₁ A (p := 2)) ≤ 2 ^ n :=
    (primeRank_le_iff_elementary_card_le A).mp
      ((_root_.primeRank_le_of_injective 2 A.subtype A.subtype_injective).trans hr)
      (omega₁ A (p := 2)) inferInstance
  have hi : A.index ≤ Nat.card (omega₁ A (p := 2)) := by
    rcases hZcard with hZ | hZ
    · have hDbot : _root_.commutator P = ⊥ := le_bot_iff.mp (hDZ.trans (card_eq_one.mp hZ).le)
      have hcenter : center P = ⊤ := (commutator_eq_bot_iff_center_eq_top P).mp hDbot
      have hAtop : A = ⊤ := top_unique (by
        rw [← hcenter]
        exact (center_le_centralizer (A : Set P)).trans hCA)
      rw [hAtop, index_top]
      exact Nat.card_pos
    · exact index_le_omega_one_of_binary_commutators A Z (hP.to_subgroup A)
        hZcentral hZ ((commutator_mono le_rfl le_top).trans hDZ) hCA
  have hPhi : Nat.card (P ⧸ frattini P) ≤ 2 ^ (2 * n) := by
    calc
      _ ≤ A.index * Nat.card (omega₁ A (p := 2)) :=
        hP.card_frattini_quotient_le_index_mul_omega_one A
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul (hi.trans hO) hO
      _ = _ := by rw [← pow_add, two_mul]
  let fbar := QuotientGroup.lift (frattini P) f
    (Theory.GroupTheory.frattini_le_ker_of_square_image f (fun a => by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) _))
  have hfbar : Function.Surjective fbar := by
    intro x
    obtain ⟨a, rfl⟩ := hf x
    exact ⟨QuotientGroup.mk' (frattini P) a, rfl⟩
  exact (Nat.card_le_card_of_surjective fbar hfbar).trans hPhi

/-- A central cyclic quotient has at most twice the two-rank of its cover. -/
theorem twoRank_le_double {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    [IsCyclic f.ker] {n : ℕ} (hr : primeRank 2 G ≤ n) :
    primeRank 2 H ≤ 2 * n := by
  apply (primeRank_le_iff_elementary_card_le H).mpr
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  let L := E.comap f
  let q : L →* E := f.subgroupComap E
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective E hf
  let P : Sylow 2 L := Sylow.nonempty.some
  have hPtop : (P : Subgroup L).map q = ⊤ := by
    change (P.mapSurjective hq : Subgroup E) = ⊤
    apply top_unique
    exact ((IsElementaryAbelian.isPGroup 2 E).to_subgroup ⊤).le_sylow_of_normal _
  let g : P →* E := q.comp (P : Subgroup L).subtype
  have hg : Function.Surjective g := by
    intro e
    have he : e ∈ (P : Subgroup L).map q := hPtop.symm ▸ mem_top e
    obtain ⟨x, hx, he⟩ := he
    exact ⟨⟨x, hx⟩, he⟩
  let j : P →* G := L.subtype.comp (P : Subgroup L).subtype
  have hj : Function.Injective j := L.subtype_injective.comp (P : Subgroup L).subtype_injective
  have hker (x : g.ker) : j x.val ∈ f.ker :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  let jk : g.ker →* f.ker := (j.comp g.ker.subtype).codRestrict f.ker hker
  have hjk : Function.Injective jk := by
    intro a b hab
    exact Subtype.ext (hj (congrArg (fun z : f.ker => (z : G)) hab))
  let : IsCyclic g.ker := isCyclic_of_injective jk hjk
  have hgc : g.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply hj
    exact mem_center_iff.mp (hc (hker ⟨x, hx⟩)) (j y)
  exact elementary_quotient_card_le P.isPGroup' g hg hgc
    ((_root_.primeRank_le_of_injective 2 j hj).trans hr)
end CentralCyclicRank
