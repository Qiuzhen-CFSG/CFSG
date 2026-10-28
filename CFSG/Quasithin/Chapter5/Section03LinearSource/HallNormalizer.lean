module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
public import Theory.GroupTheory.ConjugationFamily

/-!
# Odd intersections of full Sylow normalizers

A subgroup of a Sylow-two normalizer disjoint from its Sylow has odd order.
Thus full normalizers of disjoint Sylows intersect in a common odd Hall
subgroup whenever one is supplied. All groups and intersections are literal
subgroups of the original finite ambient group. This is the intersection
calculation in Suzuki's argument, Aschbacher–Smith F.4.49, printed p.299
of `refs/quasithin.pdf`; the prepared linear row supplies its Hall subgroup.
-/

public noncomputable section
open Subgroup Subgroup.OddHall
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G : Type*} [Group G] [Finite G]

theorem odd_of_disjoint_normalizer_sylow (T : Sylow 2 G) (B : Subgroup G)
    (hBN : B ≤ normalizer (T : Set G)) (hdis : Disjoint (T : Subgroup G) B) :
    Odd (Nat.card B) := by
  let P : Sylow 2 B := Classical.arbitrary _
  let Q := (P : Subgroup B).map B.subtype
  have hQ : IsPGroup 2 Q := P.isPGroup'.map B.subtype
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := hQ.inf_normalizer_sylow T
    rw [inf_eq_left.mpr ((map_subtype_le _).trans hBN)] at hh
    exact hh.le.trans inf_le_right
  have hQbot : Q=⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact disjoint_def.mp hdis (hQT hx) (map_subtype_le _ hx)
  have hPbot : (P : Subgroup B)=⊥ :=
    ((P : Subgroup B).map_eq_bot_iff_of_injective B.subtype_injective).mp hQbot
  have hc : Nat.card (P : Subgroup B)=1 := Subgroup.card_eq_one.mpr hPbot
  have hi : (P : Subgroup B).index=Nat.card B := by
    simpa only [hc,one_mul] using (P : Subgroup B).card_mul_index
  exact Nat.not_even_iff_odd.mp (fun he => P.not_dvd_index (hi ▸ even_iff_two_dvd.mp he))

theorem odd_overgroup_eq_hall (N B J : Subgroup G) (hBN : B≤N)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf N))
    (hBJ : B≤J) (hJN : J≤N) (ho : Odd (Nat.card J)) : J=B := by
  have hj : IsHallSubgroup oddPrimes (J.subgroupOf N) := by
    constructor
    · intro p hp he
      have hc := Nat.card_congr (subgroupOfEquivOfLe hJN).toEquiv
      have hd : 2 ∣ Nat.card J := by rwa [hc,show p.val=2 from he] at hp
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
    · intro p hp
      exact hHall.p_in_pi_of_p_dvd_index p
        (hp.trans (index_dvd_of_le (subgroupOf_mono N hBJ)))
  have he := hHall.eq_of_le hj (subgroupOf_mono N hBJ)
  have hh := congrArg (Subgroup.map N.subtype) he
  simpa only [map_subgroupOf_eq_of_le hBN,map_subgroupOf_eq_of_le hJN] using hh.symm

theorem disjoint_sylow_normalizer_inter_eq_hall (T U : Sylow 2 G) (B : Subgroup G)
    (hBN : B≤normalizer (T : Set G)) (hBU : B≤normalizer (U : Set G))
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (normalizer (T : Set G))))
    (hdis : Disjoint (T : Subgroup G) (U : Subgroup G)) :
    normalizer (T : Set G) ⊓ normalizer (U : Set G)=B := by
  let J := normalizer (T : Set G) ⊓ normalizer (U : Set G)
  apply odd_overgroup_eq_hall _ B J hBN hHall (le_inf hBN hBU) inf_le_left
  apply odd_of_disjoint_normalizer_sylow T J inf_le_left
  apply disjoint_def.mpr
  intro x hx hj
  have hxu : x ∈ (T : Subgroup G) ⊓ (U : Subgroup G) :=
    T.isPGroup'.inf_normalizer_sylow U ▸ (show x ∈ (T : Subgroup G) ⊓ normalizer (U : Set G) from ⟨hx,hj.2⟩)
  exact disjoint_def.mp hdis hx hxu.2
/-- Hall conjugacy reduces the fixed conjugates of a local central line to
the two marked torus-normalizer cosets. -/
theorem invariant_local_conjugate_eq (P Z D : Subgroup G) (s : G)
    (hDP : D≤P) (hDZ : D≤normalizer (Z : Set G))
    (hsolv : Group.IsSolvable (P ⊓ normalizer (Z : Set G) : Subgroup G))
    (hHall : IsHallSubgroup oddPrimes (D.subgroupOf (P ⊓ normalizer (Z : Set G))))
    (hs2 : s^2=1) (hsD : s∈normalizer (D : Set G))
    (hcos : ∀ x∈P, x∈normalizer (D : Set G) → x∈D ∨ x*s∈D)
    (a : G) (ha : a∈P) (hfix : D≤normalizer (Z.conjBy a : Set G)) :
    Z.conjBy a=Z ∨ Z.conjBy a=Z.conjBy s := by
  let C := P ⊓ normalizer (Z : Set G)
  let E := D.conjBy a⁻¹
  have hEC : E≤C := by
    apply le_inf
    · rintro _ ⟨x,hx,rfl⟩
      change a⁻¹*x*(a⁻¹)⁻¹∈P
      simpa only [inv_inv] using P.mul_mem (P.mul_mem (P.inv_mem ha) (hDP hx)) ha
    · have hh := (map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hfix).trans
        ((Z.conjBy a).le_normalizer_map _)
      change E ≤ normalizer ((Z.conjBy a).conjBy a⁻¹ : Set G) at hh
      simpa only [conjBy_conjBy,inv_mul_cancel,conjBy_one] using hh
  have hDC : D≤C := le_inf hDP hDZ
  have hc : Nat.card (E.subgroupOf C)=Nat.card (D.subgroupOf C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv]
    exact card_map_of_injective (MulAut.conj a⁻¹).injective
  have hi : (E.subgroupOf C).index=(D.subgroupOf C).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D.subgroupOf C))
    calc
      _ = Nat.card C := by rw [←hc,Subgroup.card_mul_index]
      _ = _ := (D.subgroupOf C).card_mul_index.symm
  have hEH : IsHallSubgroup oddPrimes (E.subgroupOf C) :=
    ⟨fun p hp => hHall.p_in_pi_of_p_dvd_card p (hc ▸ hp),
      fun p hp => hHall.p_in_pi_of_p_dvd_index p (hi ▸ hp)⟩
  obtain ⟨b,hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hHall hEH
  have hconj : E=D.conjBy b.val := by
    have hh := congrArg (Subgroup.map C.subtype) hb
    rw [map_subgroupOf_eq_of_le hEC,Subgroup.map_map] at hh
    have hcomp : C.subtype.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj b.val).toMonoidHom.comp C.subtype := rfl
    rw [hcomp,←Subgroup.map_map,map_subgroupOf_eq_of_le hDC] at hh
    exact hh
  have hn : a*b.val∈normalizer (D : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change D.conjBy (a*b.val)=D
    rw [←conjBy_conjBy,←hconj]
    change (D.conjBy a⁻¹).conjBy a=D
    rw [conjBy_conjBy,mul_inv_cancel,conjBy_one]
  have hZa : Z.conjBy (a*b.val)=Z.conjBy a := by
    have hbZ : Z.conjBy b.val=Z := mem_normalizer_iff_map_conj_eq.mp b.property.2
    rw [←conjBy_conjBy,hbZ]
  rcases hcos (a*b.val) (P.mul_mem ha b.property.1) hn with h₀ | h₁
  · exact Or.inl (hZa.symm.trans (mem_normalizer_iff_map_conj_eq.mp (hDZ h₀)))
  · right
    have hs : s⁻¹=s := inv_eq_of_mul_eq_one_right (by simpa only [←pow_two] using hs2)
    have hh := (mem_normalizer_iff.mp hsD ((a*b.val)*s)).mp h₁
    have hss : s*s=1 := by simpa only [←pow_two] using hs2
    have hsp : s*(a*b.val)∈D := by
      simpa only [hs,mul_assoc,hss,mul_one] using hh
    have hz := mem_normalizer_iff_map_conj_eq.mp (hDZ hsp)
    change Z.conjBy (s*(a*b.val))=Z at hz
    have hz' := congrArg (fun U : Subgroup G => U.conjBy s) hz
    rw [conjBy_conjBy,←mul_assoc,hss,one_mul] at hz'
    exact hZa.symm.trans hz'

omit [Finite G] in
/-- An odd-order coset cannot contain an involution unless it is trivial. -/
theorem odd_element_mem_of_involution_coset (B : Subgroup G) (g w : G)
    (hg : g∈normalizer (B : Set G)) (ho : Odd (orderOf g))
    (hw : orderOf w=2) (hcos : w*g⁻¹∈B) : g∈B := by
  have hw2 : w*w=1 := by rw [←pow_two,←hw,pow_orderOf_eq_one]
  have hh := B.mul_mem hcos ((mem_normalizer_iff.mp hg (w*g⁻¹)).mp hcos)
  have he : (w*g⁻¹)*(g*(w*g⁻¹)*g⁻¹)=(g^2)⁻¹ := by
    calc
      _ = (w*w)*(g*g)⁻¹ := by group
      _ = _ := by rw [hw2,one_mul,pow_two]
  have hsq : g^2∈B := B.inv_mem_iff.mp (he ▸ hh)
  exact (zpowers_le.mpr hsq) (mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr ho))
end CFSG.Quasithin.Chapter5.Section03LinearSource
