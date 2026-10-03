module
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Theory.GroupAction.Quotient

/-!
# A center-free chief preimage collapses when equivariant maps vanish

Let E be a normal Sylow-two supplement in a finite center-free group P,
with odd image modulo a normal two-subgroup Q. Suppose normal Z≤C≤Q
have C abelian, Z centralizing Q, [C,Q]≤Z and [C,E]≤Z. If every
P-equivariant homomorphism Q→Z killing C is trivial, then C=Z.
All normal subgroup conjugation actions use the supplied instances.

First let K=C∩C_P(Q). E acts trivially on C/K. If this quotient is
nontrivial, the Sylow two-subgroup fixes a nonidentity coset, which is
therefore fixed by all of P. A lift c defines the central commutator
homomorphism [c,-]:Q→Z killing C. The fixed-coset condition makes this
homomorphism P-equivariant, since conjugation changes c by an element
centralizing Q. Vanishing contradicts the chosen nonidentity coset.
Thus C centralizes Q.

The center-free normal-two-subgroup lemma makes C_C(E) trivial. An odd
Schur–Zassenhaus complement inside E acts coprimely on C and has the
same fixed subgroup as E, because C centralizes Q. Coprime decomposition
now gives C=[C,E]≤Z.

This supplies the nonisomorphic-chief-module transfer in Stellmacher
(9.1), Journal of Algebra190 (1997), p.48. The concrete no-hom theorem
and the preceding abelian/central-layer reductions are separate inputs.
No choice of an odd complement normalized by a Sylow subgroup is needed.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

private theorem centralizes_of_no_equivariant_hom
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q C Z : Subgroup P)
    [Q.Normal] [C.Normal] [Z.Normal] [IsMulCommutative C]
    (hcover : E ⊔ (S : Subgroup P) = ⊤) (hCp : IsPGroup 2 C)
    (_hZC : Z ≤ C) (hCQ : C ≤ Q) (hZcentral : Z ≤ centralizer (Q : Set P))
    (hCQcomm : ⁅C,Q⁆ ≤ Z) (hCE : ⁅C,E⁆ ≤ Z)
    (hno : ∀ f : Q →* Z, C.subgroupOf Q ≤ f.ker →
      (∀ (g : P) (q : Q), f (MulAut.conjNormal g q) = MulAut.conjNormal g (f q)) → f = 1) :
    C ≤ centralizer (Q : Set P) := by
  classical
  let K := C ⊓ centralizer (Q : Set P)
  let K0 := K.subgroupOf C
  let _ : K.Normal := inferInstance
  let _ : K0.Normal := inferInstance
  let _ : MulDistribMulAction P C := MulDistribMulAction.compHom C
    (MulAut.conjNormal : P →* MulAut C)
  have hKinv : IsInvariant P C K0 := by
    constructor
    intro g c
    change (c : P) ∈ K ↔ g * (c : P) * g⁻¹ ∈ K
    have hg : g ∈ normalizer (K : Set P) := by rw [normalizer_eq_top]; trivial
    exact mem_normalizer_iff.mp hg c
  let _ : MulDistribMulAction P (C ⧸ K0) := quotientMulDistribMulAction K0 hKinv
  have hKE : ⁅C,E⁆ ≤ K := le_inf (commutator_le_left C E) (hCE.trans hZcentral)
  have hEfixed (e : E) (point : C ⧸ K0) : e • point = point := by
    induction point using QuotientGroup.induction_on with
    | H representative =>
      change ((MulAut.conjNormal (e : P) representative : C) : C ⧸ K0) = representative
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (e : P) * (representative : P) * (e : P)⁻¹ / (representative : P) ∈ K
      have hc : ⁅(e : P), (representative : P)⁆ ∈ ⁅C,E⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator e.property representative.property
      simpa only [commutatorElement_def, div_eq_mul_inv] using hKE hc
  by_contra hnot
  have hquotient : Nat.card (C ⧸ K0) ≠ 1 := by
    intro hone
    have htop : K0 = ⊤ := by
      apply index_eq_one.mp
      rw [index_eq_card]
      exact hone
    apply hnot
    intro c hc
    have hm : (⟨c,hc⟩ : C) ∈ K0 := by rw [htop]; trivial
    exact hm.2
  have hdiv : 2 ∣ Nat.card (C ⧸ K0) := (hCp.to_quotient K0).card_eq_or_dvd.resolve_left hquotient
  have hone : (1 : C ⧸ K0) ∈ MulAction.fixedPoints S (C ⧸ K0) := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨point, hpoint, hpointne⟩ := S.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := C ⧸ K0) hdiv hone
  have hpointP (g : P) : g • point = point := by
    let L := fixingSubgroup P ({point} : Set (C ⧸ K0))
    have hEL : E ≤ L := by
      intro e he
      rw [mem_fixingSubgroup_iff]
      rintro p (rfl : p = point)
      exact hEfixed ⟨e,he⟩ _
    have hSL : (S : Subgroup P) ≤ L := by
      intro s hs
      rw [mem_fixingSubgroup_iff]
      rintro p (rfl : p = point)
      exact (MulAction.mem_fixedPoints.mp hpoint) ⟨s,hs⟩
    have htop : (⊤ : Subgroup P) ≤ L := by rw [← hcover]; exact sup_le hEL hSL
    have hh := htop (mem_top g)
    rw [mem_fixingSubgroup_iff] at hh
    exact hh point (Set.mem_singleton _)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective K0 point
  have hcQ : (c : P) ∈ Q := hCQ c.property
  have hdelta (g : P) : g * (c : P) * g⁻¹ * (c : P)⁻¹ ∈ K := by
    have hh := hpointP g
    change ((MulAut.conjNormal g c : C) : C ⧸ K0) = (c : C ⧸ K0) at hh
    have hm := QuotientGroup.eq_iff_div_mem.mp hh
    change g * (c : P) * g⁻¹ / (c : P) ∈ K at hm
    simpa only [div_eq_mul_inv] using hm
  have hvalue (q : Q) : ⁅(c : P), (q : P)⁆ ∈ Z :=
    hCQcomm (commutator_mem_commutator c.property q.property)
  let f : Q →* Z :=
    { toFun := fun q => ⟨⁅(c : P), (q : P)⁆, hvalue q⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro first second
        apply Subtype.ext
        change ⁅(c : P), (first : P) * (second : P)⁆ =
          ⁅(c : P), (first : P)⁆ * ⁅(c : P), (second : P)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hh := mem_centralizer_iff.mp (hZcentral (hvalue second)) first first.property
        calc
          _ = ⁅(c : P), (first : P)⁆ * ((first : P) * ⁅(c : P), (second : P)⁆) * (first : P)⁻¹ := by group
          _ = _ := by rw [hh]; group }
  have hkernel : C.subgroupOf Q ≤ f.ker := by
    intro q hq
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change ⁅(c : P), (q : P)⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (setLike_mul_comm (s := C) c.property hq)
  have hequiv (g : P) (q : Q) : f (MulAut.conjNormal g q) = MulAut.conjNormal g (f q) := by
    apply Subtype.ext
    change ⁅(c : P), g * (q : P) * g⁻¹⁆ = g * ⁅(c : P), (q : P)⁆ * g⁻¹
    rw [conjugate_commutatorElement]
    let d := g * (c : P) * g⁻¹ * (c : P)⁻¹
    have hd : d ∈ centralizer (Q : Set P) := (hdelta g).2
    have hx : g * (c : P) * g⁻¹ = d * (c : P) := by dsimp [d]; group
    have hq : g * (q : P) * g⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem q q.property g
    rw [hx, commutatorElement_mul_left_eq_conj_mul]
    have hdq : ⁅d,g * (q : P) * g⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_iff.mp hd _ hq).symm
    have hcommQ : ⁅(c : P),g * (q : P) * g⁻¹⁆ ∈ Q :=
      commutator_le_left Q Q (commutator_mem_commutator hcQ hq)
    have hdc := mem_centralizer_iff.mp hd _ hcommQ
    rw [hdq, mul_one, ← hdc, mul_inv_cancel_right]
  have hf := hno f hkernel hequiv
  have hcK : c ∈ K0 := by
    refine ⟨c.property, ?_⟩
    change (c : P) ∈ centralizer (Q : Set P)
    rw [mem_centralizer_iff]
    intro q hq
    have hh := congrArg (fun φ : Q →* Z => ((φ ⟨q,hq⟩ : Z) : P)) hf
    change ⁅(c : P),q⁆ = 1 at hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  exact hpointne ((QuotientGroup.eq_one_iff _).mpr hcK).symm

public theorem eq_of_centerfree_odd_residual_no_equivariant_hom
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q C Z : Subgroup P)
    [E.Normal] [Q.Normal] [C.Normal] [Z.Normal] [IsMulCommutative C]
    (hcover : E ⊔ (S : Subgroup P) = ⊤) (hQp : IsPGroup 2 Q)
    (hodd : Odd (Nat.card (E.map (QuotientGroup.mk' Q)))) (hcenter : center P = ⊥)
    (hZC : Z ≤ C) (hCQ : C ≤ Q) (hZcentral : Z ≤ centralizer (Q : Set P))
    (hCQcomm : ⁅C,Q⁆ ≤ Z) (hCE : ⁅C,E⁆ ≤ Z)
    (hno : ∀ f : Q →* Z, C.subgroupOf Q ≤ f.ker →
      (∀ (g : P) (q : Q), f (MulAut.conjNormal g q) = MulAut.conjNormal g (f q)) → f = 1) :
    C = Z := by
  have hCp := hQp.to_le hCQ
  have hCQcentral := centralizes_of_no_equivariant_hom S E Q C Z hcover hCp hZC hCQ
    hZcentral hCQcomm hCE hno
  have hCfixed : C ⊓ centralizer (E : Set P) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S E C hcover hCp hcenter
  let K := Q.subgroupOf E
  have hKp : IsPGroup 2 K := hQp.comap_of_injective E.subtype E.subtype_injective
  have hKodd : Odd K.index := by
    change Odd (Q.subgroupOf E).index
    rw [index_eq_card, ← natCard_map_mk'_eq E Q]
    exact hodd
  have hKcop : Nat.Coprime (Nat.card K) K.index := by
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    rw [hn]
    exact hKodd.coprime_two_left.pow_left n
  obtain ⟨R0, hR0⟩ := exists_right_complement'_of_coprime hKcop
  let R := R0.map E.subtype
  have hRE : R ≤ E := map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [card_map_of_injective E.subtype_injective, ← hR0.symm.index_eq_card]
    exact hKodd
  have hEfactor : E = (Q ⊓ E) ⊔ R := by
    have hm := congrArg (fun H : Subgroup E => H.map E.subtype) hR0.sup_eq_top
    change (Q.subgroupOf E ⊔ R0).map E.subtype = (⊤ : Subgroup E).map E.subtype at hm
    rw [map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm.symm
  have hRcop : Nat.Coprime (Nat.card R) (Nat.card C) := by
    obtain ⟨n, hn⟩ := hCp.exists_card_eq
    rw [hn]
    exact hRodd.coprime_two_right.pow_right n
  have hRfix : C ⊓ centralizer (R : Set P) = ⊥ := by
    apply bot_unique
    rw [← hCfixed]
    refine le_inf inf_le_left ?_
    apply le_centralizer_iff.mp
    rw [hEfactor]
    exact sup_le
      (inf_le_left.trans ((le_centralizer_iff.mp hCQcentral).trans (centralizer_le inf_le_left)))
      (le_centralizer_iff.mp inf_le_right)
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime C R
    le_normalizer_of_normal
    (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := C)).comm x y) hRcop
  rw [hRfix, sup_bot_eq] at hsplit
  exact le_antisymm (hsplit.le.trans ((commutator_mono le_rfl hRE).trans hCE)) hZC
end Subgroup
