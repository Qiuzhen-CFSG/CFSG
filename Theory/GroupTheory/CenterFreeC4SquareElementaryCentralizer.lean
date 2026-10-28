module
public import Theory.GroupTheory.CenterFreeC4SquareCoreBound
public import Theory.GroupTheory.CenterSmallIndex
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary centralizers in a center-free C4-square residual group

Let normal E supplement a Sylow two-subgroup of a finite center-free group P.
Suppose normal Q is a two-group, the E-image modulo Q has order three, and
R=E∩Q is C₄×C₄. If a normal elementary subgroup U≤Q has order eight and
contains a central elementary four-subgroup Z≤R, then C_Q(U) is elementary
of order eight or sixteen. Its intersection with R is exactly Z, and its
commutator with E lies in Z. The elementary property of Z follows from Z≤U.
All groups and normality instances are the supplied native ones.

The subgroup Z comprises every square-one element of R. Choose u∈U outside
R; its action on R is nontrivial because R is self-centralizing in Q. That
action commutes with the order-three E-action, so its fixed points in R lie
in Z. Thus C_Q(U)∩R=Z. The bound |Q|≤64 gives |C_Q(U)|≤16, while U is central
in C_Q(U) and has index at most two, making the centralizer abelian.
Its E-commutators lie in Z, so all its squares centralize E. Center-freeness
and the Sylow supplement make that normal square subgroup trivial.

This isolates the W*=C_Q(W₀) calculation in Stellmacher (10.1)(a3),
printed p.61 of `refs/files/stellmacher-n-group.pdf`, independently of the
graph-specific normalizer and involution-fusion arguments which follow it.
-/

open Subgroup
open scoped commutatorElement

namespace Subgroup

public theorem elementary_centralizer_of_centerfree_c4_square_residual
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q U Z : Subgroup P)
    [E.Normal] [Q.Normal] [U.Normal]
    (hcover : E ⊔ (S : Subgroup P) = ⊤) (hQ : IsPGroup 2 Q)
    (hcenter : center P = ⊥)
    (model : Nonempty ((E ⊓ Q : Subgroup P) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (himage : Nat.card (E.map (QuotientGroup.mk' Q)) = 3)
    (hUQ : U ≤ Q) [IsElementaryAbelian 2 U] (hUcard : Nat.card U = 8)
    (hZR : Z ≤ E ⊓ Q) (hZU : Z ≤ U) (hZcard : Nat.card Z = 4)
    (hZcentral : Z ≤ centralizer (Q : Set P)) :
    let C := Q ⊓ centralizer (U : Set P)
    IsElementaryAbelian 2 C ∧ (Nat.card C = 8 ∨ Nat.card C = 16) ∧
      C ⊓ (E ⊓ Q) = Z ∧ ⁅C,E⁆ ≤ Z := by
  classical
  let R := E ⊓ Q
  let C := Q ⊓ centralizer (U : Set P)
  have hRQ : R ≤ Q := inf_le_right
  have hCQ : C ≤ Q := inf_le_left
  have hRp : IsPGroup 2 R := hQ.to_le hRQ
  obtain ⟨equiv⟩ := model
  let _ : CommGroup R := equiv.toMonoidHom.commGroupOfInjective equiv.injective
  have hRcard : Nat.card R = 16 := by
    rw [Nat.card_congr equiv.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card]
  let squareR : R →* R := powMonoidHom 2
  have hZker : Z.subgroupOf R ≤ squareR.ker := by
    intro z hz
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=U) z (hZU hz)
  have hkerCard : Nat.card squareR.ker ≤ 4 := by
    let f : squareR.ker → {v : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // v^2=1} :=
      fun x => ⟨equiv x,by rw [← map_pow]; exact (congrArg equiv x.property).trans equiv.map_one⟩
    have hfinj : Function.Injective f := by
      intro x y hh
      exact Subtype.ext (equiv.injective (congrArg Subtype.val hh))
    have hcard : Nat.card {v : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // v^2=1} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    exact hcard ▸ Nat.card_le_card_of_injective f hfinj
  have hZkerEq : Z.subgroupOf R = squareR.ker := by
    apply Subgroup.eq_of_le_of_card_ge hZker
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv,hZcard]
    exact hkerCard
  have hfull (r : R) (hr : r^2=1) : (r:P) ∈ Z := by
    have hh : r ∈ squareR.ker := hr
    rwa [← hZkerEq] at hh
  have hUC : U ≤ C := le_inf hUQ (le_centralizer U)
  have hZC : Z ≤ C := le_inf (hZR.trans hRQ)
    (hZcentral.trans (centralizer_le hUQ))
  have hK : Q ⊓ centralizer (R : Set P) = R :=
    inf_centralizer_inf_eq_of_centerfree_odd_image S E Q hcover hQ hcenter
      (by rw [himage]; decide)
  let action : P →* MulAut R := MulAut.conjNormal
  have hker : action.ker = centralizer (R : Set P) := by
    ext g
    rw [MonoidHom.mem_ker,mem_centralizer_iff]
    constructor
    · intro h r hr
      have hh := congrArg (fun f : MulAut R => (f ⟨r,hr⟩ : P)) h
      change g*r*g⁻¹=r at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro h
      ext r
      change g*(r:P)*g⁻¹=(r:P)
      rw [← h r r.property,mul_inv_cancel_right]
  have hRker : R ≤ action.ker := hker ▸ le_centralizer R
  have hRcentralE : R ⊓ centralizer (E : Set P) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S E R hcover hRp hcenter
  have himageNe : E.map action ≠ ⊥ := by
    intro hz
    have hEk : E ≤ action.ker := (map_eq_bot_iff _).mp hz
    have hRC : R ≤ centralizer (E : Set P) := le_centralizer_iff.mp (hker ▸ hEk)
    have hbot : R = ⊥ := by simpa only [inf_eq_left.mpr hRC] using hRcentralE
    rw [hbot,card_bot] at hRcard
    omega
  have himageDvd : Nat.card (E.map action) ∣ 3 := by
    have hindex : R.relIndex E = 3 := by
      dsimp [R]
      rw [inf_relIndex_left,← QuotientGroup.ker_mk' Q,relIndex_ker]
      exact himage
    rw [← relIndex_ker,← hindex]
    exact relIndex_dvd_of_le_left E hRker
  have himageThree : Nat.card (E.map action) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp himageDvd with hone | hthree
    · exact False.elim (himageNe (card_eq_one.mp hone))
    · exact hthree
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G:=E.map action) 3 (by rw [himageThree])
  have ha3 : (a:MulAut R)^3=1 := congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
  have hane : (a:MulAut R) ≠ 1 := by
    intro heq
    have haa : a=1 := Subtype.ext heq
    rw [haa,orderOf_one] at ha
    omega
  have hcentral : Q.map action ≤ centralizer (E.map action : Set (MulAut R)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    apply (map_eq_bot_iff _).mpr
    exact (commutator_le_inf Q E).trans ((inf_comm Q E).le.trans hRker)
  have hUnot : ¬ U ≤ R := by
    intro hle
    have hUZ : U ≤ Z := by
      intro u hu
      exact hfull ⟨u,hle hu⟩ (Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=U) u hu))
    have hh := card_le_of_le hUZ
    omega
  obtain ⟨u,hu,huR⟩ := SetLike.not_le_iff_exists.mp hUnot
  have hcu : action u ≠ 1 := by
    intro heq
    apply huR
    rw [← hK]
    exact ⟨hUQ hu,hker ▸ heq⟩
  have hCa : Commute (action u) (a:MulAut R) := by
    exact (mem_centralizer_iff.mp (hcentral (mem_map_of_mem action (hUQ hu))) a a.property).symm
  have hCR : C ⊓ R = Z := by
    apply le_antisymm
    · intro r hr
      apply hfull ⟨r,hr.2⟩
      apply c4_square_fixed_point_square_eq_one_of_commuting_three ⟨equiv⟩
        a ha3 hane (action u) hcu hCa
      apply Subtype.ext
      change u*r*u⁻¹=r
      have hh := mem_centralizer_iff.mp hr.1.2 u hu
      rw [hh,mul_inv_cancel_right]
    · exact le_inf hZC hZR
  have hCE : ⁅C,E⁆ ≤ Z := by
    rw [← hCR]
    refine le_inf (commutator_le_left C E) ?_
    exact le_inf (commutator_le_right C E)
      ((commutator_mono hCQ le_rfl).trans (commutator_le_left Q E))
  have hCbound : Nat.card C ≤ 16 := by
    have hQbound : Nat.card Q ≤ 64 := card_le_sixtyfour_of_centerfree_c4_square_residual
      S E Q hcover hQ hcenter ⟨equiv⟩ himage
    have hjoinBound := (card_le_of_le (sup_le hCQ hRQ)).trans hQbound
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes C R le_normalizer_of_normal
    rw [hCR,hRcard,hZcard] at hprod
    omega
  have hUcenter : U.subgroupOf C ≤ center C := by
    intro u hu
    rw [mem_center_iff]
    intro c
    apply Subtype.ext
    exact (mem_centralizer_iff.mp c.property.2 u hu).symm
  have hUindex : (U.subgroupOf C).index ≤ 2 := by
    have hh := (U.subgroupOf C).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv,hUcard] at hh
    omega
  have hcomm : IsMulCommutative C := by
    apply (commutator_eq_bot_iff C).mp
    by_contra hne
    have hfour := (center_eq_and_index_four_of_central_small_index
      (U.subgroupOf C) hUcenter (by omega) hne).2
    omega
  let _ := hcomm
  let _ : CommGroup C := IsMulCommutative.instCommGroup
  let square : C →* P := C.subtype.comp (powMonoidHom 2)
  have hsquareQ : square.range ≤ Q := by
    rintro _ ⟨c,rfl⟩
    exact Q.pow_mem (hCQ c.property) 2
  have hsquareNormal : square.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨c,rfl⟩ g
    refine ⟨⟨g*(c:P)*g⁻¹,(inferInstance : C.Normal).conj_mem _ c.property g⟩,?_⟩
    change (g*(c:P)*g⁻¹)^2=g*(c:P)^2*g⁻¹
    simp only [pow_two]
    group
  let _ := hsquareNormal
  have hsquareCentral : square.range ≤ centralizer (E : Set P) := by
    rintro _ ⟨c,rfl⟩
    rw [mem_centralizer_iff]
    intro e he
    let ec : C := ⟨e*(c:P)*e⁻¹,(inferInstance : C.Normal).conj_mem _ c.property e⟩
    let d : C := ec * c⁻¹
    have hdZ : (d:P) ∈ Z := by
      apply hCE
      rw [commutator_comm]
      exact commutator_mem_commutator he c.property
    have hd2 : d^2=1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=U) d (hZU hdZ))
    have hsame : ec^2=c^2 := by
      have hdelta : ec=d*c := by simp [d]
      rw [hdelta,mul_pow,hd2,one_mul]
    have heq := congrArg Subtype.val hsame
    change (e*(c:P)*e⁻¹)^2=(c:P)^2 at heq
    have hconj : e*(c:P)^2*e⁻¹=(c:P)^2 := by
      calc
        e*(c:P)^2*e⁻¹ = (e*(c:P)*e⁻¹)^2 := by simp only [pow_two]; group
        _ = (c:P)^2 := heq
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hsquareBot : square.range = ⊥ := by
    have hh := inf_centralizer_eq_bot_of_centerfree_sylow_supplement S E square.range
      hcover (hQ.to_le hsquareQ) hcenter
    simpa only [inf_eq_left.mpr hsquareCentral] using hh
  have hel : IsElementaryAbelian 2 C := by
    refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
    intro c
    apply Subtype.ext
    have hh : square c ∈ square.range := ⟨c,rfl⟩
    rw [hsquareBot] at hh
    exact hh
  have hCcard : Nat.card C = 8 ∨ Nat.card C = 16 := by
    have hdiv : 8 ∣ Nat.card C := hUcard ▸ card_dvd_of_le hUC
    have hpositive := Nat.card_pos (α:=C)
    obtain ⟨k,hk⟩ := hdiv
    have hkrange : k=1 ∨ k=2 := by omega
    rcases hkrange with rfl | rfl <;> omega
  exact ⟨hel,hCcard,hCR,hCE⟩

end Subgroup
