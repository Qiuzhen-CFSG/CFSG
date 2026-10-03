module
public import Theory.GroupTheory.Commutator.PTimesQ
public import Theory.PPrimeCore
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Odd cores detected by characteristic-two Klein-four centralizers

Suppose an involution a commutes with an elementary four-subgroup Z of a
finite group. If each nonidentity v in Z has a characteristic-two full
centralizer, then the full centralizer of a has trivial odd core. The
hypotheses concern the actual ambient centralizers; no solvability assumption
on the ambient group or on C(a) is needed.

Let K be the ambient image of the odd core of C(a). For v in Z, set
D=C_K(v) and R=O2(C(v)). Since K is normal in C(a), coprime orders force
D to centralize C_R(a). The general P × Q theorem then makes D centralize R.
Characteristic two puts D in R, and oddness makes D trivial. Thus every
nonidentity element of Z acts fixed-point freely on K. Two distinct such
involutions both act by inversion; their nonidentity product fixes K,
forcing K=1. This is the usual three-fixed-subgroup generation conclusion
in a form requiring only the fixed-point-free involution theorem.

Source: Stellmacher (10.1)(a3), printed p.62, paragraph preceding assertion
(10). The P × Q step is the promoted Kurzweil–Stellmacher 8.2.8 theorem;
the inversion step uses Mathlib's finite fixed-point-free automorphism API.
-/

open scoped Pointwise
namespace Subgroup

private theorem normalizes_mapped_normal
    {G : Type*} [Group G] (C : Subgroup G) (D : Subgroup C) [D.Normal] :
    C ≤ normalizer (D.map C.subtype : Set G) := by
  have hsub : (D.map C.subtype).subgroupOf C = D := by
    change (D.map C.subtype).comap C.subtype = D
    rw [comap_map_eq]
    simp
  let _ : ((D.map C.subtype).subgroupOf C).Normal := hsub.symm ▸ inferInstance
  exact le_normalizer_of_normal_subgroupOf (map_subtype_le D)

public theorem pPrimeCore_centralizer_eq_bot_of_klein_four
    {G : Type*} [Group G] [Finite G]
    (a : G) (ha : orderOf a = 2) (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZcard : Nat.card Z = 4) (hZa : Z ≤ centralizer ({a} : Set G))
    (hchar : ∀ v ∈ Z, v ≠ 1 →
      centralizer (pCore 2 (centralizer ({v} : Set G)) :
        Set (centralizer ({v} : Set G))) ≤ pCore 2 (centralizer ({v} : Set G))) :
    pPrimeCore 2 (centralizer ({a} : Set G)) = ⊥ := by
  classical
  let C := centralizer ({a} : Set G)
  let K := (pPrimeCore 2 C).map C.subtype
  have hKC : K ≤ C := map_subtype_le _
  have hKN : C ≤ normalizer (K : Set G) := normalizes_mapped_normal C _
  have hKcop : Nat.Coprime 2 (Nat.card K) := by
    rw [show Nat.card K = Nat.card (pPrimeCore 2 C) from card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  let P := zpowers a
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by
    simpa only [P,Nat.card_zpowers,pow_one] using ha)
  have hPC : centralizer (P : Set G) = C := by
    dsimp only [P,C]
    rw [zpowers_eq_closure,centralizer_closure]
  have hfixed (v : G) (hvZ : v ∈ Z) (hvne : v ≠ 1) :
      K ⊓ centralizer ({v} : Set G) = ⊥ := by
    let V := centralizer ({v} : Set G)
    let D := K ⊓ V
    let R := (pCore 2 V).map V.subtype
    have hRV : R ≤ V := map_subtype_le _
    have hVN : V ≤ normalizer (R : Set G) := normalizes_mapped_normal V _
    have hR2 : IsPGroup 2 R := (pCore_isPGroup (p := 2) (G := V)).map _
    have hKR : K ⊓ R = ⊥ := by
      obtain ⟨n,hn⟩ := hR2.exists_card_eq
      exact (disjoint_of_coprime_natCard (by rw [hn]; exact hKcop.symm.pow_right n)).eq_bot
    have haV : a ∈ V := by
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (hZa hvZ)).symm
    have hPV : P ≤ V := zpowers_le.mpr haV
    have hfix : R ⊓ centralizer (P : Set G) ≤ centralizer (D : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      apply bot_unique
      rw [← hKR]
      apply le_inf
      · rw [commutator_comm]
        exact (commutator_mono inf_le_left le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp
            ((inf_le_right.trans_eq hPC).trans hKN))
      · exact (commutator_mono inf_le_left le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hVN))
    have hPQ : ⁅P,D⁆ = ⊥ := by
      rw [commutator_comm]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      rw [hPC]
      exact inf_le_left.trans hKC
    have hDcop : Nat.Coprime 2 (Nat.card D) :=
      hKcop.of_dvd_right (card_dvd_of_le inf_le_left)
    have hcomm := p_times_q_centralizer P D R hP2 hR2 hDcop
      (hPV.trans hVN) (inf_le_right.trans hVN) hPQ hfix
    have hDR : D ≤ R := by
      intro d hd
      have hdV : d ∈ V := hd.2
      have hdcent : (⟨d,hdV⟩ : V) ∈ centralizer (pCore 2 V : Set V) := by
        rw [mem_centralizer_iff]
        intro r hr
        apply Subtype.ext
        exact mem_centralizer_iff.mp
          ((commutator_eq_bot_iff_le_centralizer.mp hcomm)
            (mem_map_of_mem V.subtype hr)) d hd |>.symm
      exact mem_map_of_mem V.subtype (hchar v hvZ hvne hdcent)
    apply bot_unique
    rw [← hKR]
    exact le_inf inf_le_left hDR
  have hZN : Z ≤ normalizer (K : Set G) := hZa.trans hKN
  let _ := conjMulDistribMulActionOfLeNormalizer Z K hZN
  let action : Z →* MulAut K := MulDistribMulAction.toMulAut Z K
  have hpow (z : Z) : z^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Z) z
  have hff (z : Z) (hz : z ≠ 1) : MonoidHom.FixedPointFree (action z) := by
    intro k hk
    apply Subtype.ext
    have hkcent : (k:G) ∈ centralizer ({(z:G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hh := congrArg Subtype.val hk
      change (z:G)*(k:G)*(z:G)⁻¹=(k:G) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hmem : (k:G) ∈ K ⊓ centralizer ({(z:G)} : Set G) := ⟨k.property,hkcent⟩
    rw [hfixed z z.property (fun heq => hz (Subtype.ext heq))] at hmem
    exact hmem
  have hinv (z : Z) (hz : z ≠ 1) (k : K) : action z k = k⁻¹ := by
    have hinvol : Function.Involutive (action z) := by
      intro k
      change ((action z)*(action z)) k=k
      rw [← map_mul,← pow_two,hpow,map_one]
      rfl
    exact congrFun ((hff z hz).coe_eq_inv_of_involutive hinvol) k
  let _ : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.mp (by rw [hZcard]; decide)
  obtain ⟨x,hx⟩ := exists_ne (1:Z)
  have hpair : ({1,x} : Set Z).ncard < (Set.univ : Set Z).ncard := by
    rw [Set.ncard_univ,hZcard]
    rw [Set.ncard_pair (Ne.symm hx)]
    decide
  obtain ⟨y,_,hy⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hpair
  have hy1 : y ≠ 1 := by intro h; exact hy (by simp [h])
  have hyx : y ≠ x := by intro h; exact hy (by simp [h])
  have hxy : x*y ≠ 1 := by
    intro hh
    apply hyx
    have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hpow x)
    exact (eq_inv_of_mul_eq_one_right hh).trans hxi
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff_forall]
    intro k hk
    have heq : action (x*y) (⟨k,hk⟩ : K) = ⟨k,hk⟩ := by
      rw [map_mul,MulAut.mul_apply,hinv y hy1,hinv x hx,inv_inv]
    exact congrArg Subtype.val (hff (x*y) hxy _ heq)
  apply bot_unique
  have hle := (map_eq_bot_iff (pPrimeCore 2 C)).mp hKbot
  simpa using hle

end Subgroup