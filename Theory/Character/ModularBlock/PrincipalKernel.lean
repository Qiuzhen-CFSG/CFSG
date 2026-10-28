module

public import Theory.Character.ModularBlock.Kernel
public import Theory.Character.ModularBlock.Congruence
public import Theory.PPrimeCore

/-!
# The odd core is in the kernel of the principal congruence block

This file proves the ordinary-character part of Feit IV.4.12(ii), specialized
to the congruence definition of the principal `2`-block used by the Z*-proof.
The proof sums central-character congruences over the ambient conjugacy classes
contained in `O_{2'}(G)`. For the principal character that sum is the odd core's
order, hence it reduces to one modulo the chosen prime above two. The sum for
any character in the same block is therefore nonzero. Its complex value is
the character sum over the odd core divided by the degree, so that character
sum cannot vanish. The normal-subgroup norm dichotomy forces the odd core
into the representation kernel. Character-value and weighted-sum invariance
under multiplication by the odd core follow immediately.

Ported from `Submission/ZStar/PrincipalBlockKernel.lean` at historical commit
`c3503435`. The existing principal congruence block, cyclotomic integer ring,
and `pPrimeCore` definitions are used directly. All prerequisites lie in
`Theory`, including the normal-subgroup norm theorem.
-/

noncomputable section

open scoped BigOperators

namespace ModularBlock

namespace PrincipalBlockKernel

open BlockPreliminaries PrincipalBlockConstruction ModularKernel

attribute [local instance] Fintype.ofFinite

universe u v

/-- An ambient conjugacy class meets a subgroup. -/
private def ClassMeets
    {G : Type u} [Group G] (H : Subgroup G) (c : ConjClasses G) : Prop :=
  ∃ h : H, ConjClasses.mk (h : G) = c

private noncomputable def classContribution
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (f : ConjClassFunction G)
    (c : ConjClasses G) : ℂ := by
  classical
  exact if ClassMeets H c then (Nat.card c.carrier : ℂ) * f c else 0

private def carrierEquivFiber
    {G : Type u} [Group G] (c : ConjClasses G) :
    c.carrier ≃ {g : G // ConjClasses.mk g = c} where
  toFun x := ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mp x.2⟩
  invFun x := ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem mem_normal_of_classMeets
    {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal] {c : ConjClasses G} {g : G}
    (hgc : g ∈ c.carrier) (hcH : ClassMeets H c) :
    g ∈ H := by
  rcases hcH with ⟨h, hh⟩
  have hmk : ConjClasses.mk (h : G) = ConjClasses.mk g := by
    exact hh.trans (ConjClasses.mem_carrier_iff_mk_eq.mp hgc).symm
  have hconj : IsConj (h : G) g :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hmk
  rcases isConj_iff.mp hconj with ⟨x, hx⟩
  rw [← hx]
  exact (inferInstance : H.Normal).conj_mem (h : G) h.2 x

private theorem classMeets_of_mem
    {G : Type u} [Group G]
    (H : Subgroup G) {c : ConjClasses G} {g : G}
    (hgH : g ∈ H) (hgc : g ∈ c.carrier) :
    ClassMeets H c := by
  exact ⟨⟨g, hgH⟩, ConjClasses.mem_carrier_iff_mk_eq.mp hgc⟩

/-- Sum a class function over a normal subgroup by ambient conjugacy classes. -/
private theorem sum_normalSubgroup_eq_sum_classes
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (f : ConjClassFunction G) :
    ∑ h : H, f (ConjClasses.mk (h : G)) =
      ∑ c : ConjClasses G, classContribution H f c := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let supported : G → ℂ := fun g => if g ∈ H then f (ConjClasses.mk g) else 0
  have hsubgroup : ∑ g : G, supported g =
      ∑ h : H, f (ConjClasses.mk (h : G)) := by
    let s : Finset G := Finset.univ.filter fun g : G => g ∈ H
    have hs : ∀ g : G, g ∈ s ↔ g ∈ H := by
      intro g
      simp [s]
    have hfilter : ∑ g ∈ s, f (ConjClasses.mk g) =
        ∑ x : {g : G // g ∈ H}, f (ConjClasses.mk (x : G)) :=
      Finset.sum_subtype (s := s) (p := fun g : G => g ∈ H) hs
        (fun g => f (ConjClasses.mk g))
    let eH : H ≃ {g : G // g ∈ H} :=
      { toFun := fun h => ⟨h, h.2⟩
        invFun := fun g => ⟨g, g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have heq := Equiv.sum_comp eH
      (fun x : {g : G // g ∈ H} => f (ConjClasses.mk (x : G)))
    have hsum : ∑ g ∈ s, f (ConjClasses.mk g) =
        ∑ h : H, f (ConjClasses.mk (h : G)) := by
      calc
        ∑ g ∈ s, f (ConjClasses.mk g) =
            ∑ x : {g : G // g ∈ H}, f (ConjClasses.mk (x : G)) := hfilter
        _ = ∑ h : H, f (ConjClasses.mk (h : G)) := by
          simp
    calc
      ∑ g : G, supported g =
          ∑ g ∈ s, f (ConjClasses.mk g) := by
            change (∑ g : G, if g ∈ H then f (ConjClasses.mk g) else 0) = _
            simpa [s] using
              (Finset.sum_filter (s := (Finset.univ : Finset G))
                (p := fun g : G => g ∈ H) (f := fun g => f (ConjClasses.mk g))).symm
      _ = ∑ h : H, f (ConjClasses.mk (h : G)) := hsum
  have hclasses : ∑ g : G, supported g =
      ∑ c : ConjClasses G, ∑ x : c.carrier, supported (x : G) := by
    let e : (Σ c : ConjClasses G, c.carrier) ≃ G :=
      (Equiv.sigmaCongrRight fun c => carrierEquivFiber c).trans
        (Equiv.sigmaFiberEquiv (ConjClasses.mk : G → ConjClasses G))
    have hsum := Equiv.sum_comp e supported
    simpa [e, carrierEquivFiber, Fintype.sum_sigma] using hsum.symm
  calc
    ∑ h : H, f (ConjClasses.mk (h : G)) = ∑ g : G, supported g := hsubgroup.symm
    _ = ∑ c : ConjClasses G, ∑ x : c.carrier, supported (x : G) := hclasses
    _ = ∑ c : ConjClasses G, classContribution H f c := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hcH : ClassMeets H c
      · rw [classContribution, if_pos hcH]
        calc
          ∑ x : c.carrier, supported (x : G) =
              ∑ _x : c.carrier, f c := by
                apply Finset.sum_congr rfl
                intro x _hx
                have hxH : (x : G) ∈ H :=
                  mem_normal_of_classMeets H x.2 hcH
                simp [supported, hxH,
                  ConjClasses.mem_carrier_iff_mk_eq.mp x.2]
          _ = (Nat.card c.carrier : ℂ) * f c := by simp
      · rw [classContribution, if_neg hcH]
        apply Finset.sum_eq_zero
        intro x _hx
        have hxNotH : (x : G) ∉ H := by
          intro hxH
          exact hcH (classMeets_of_mem H hxH x.2)
        simp [supported, hxNotH]

private noncomputable def centralCharacterContribution
    {G : Type u} [Group G] [Finite G]
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (H : Subgroup G)
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi)
    (c : ConjClasses G) : cyclotomicOrder eta := by
  classical
  exact if ClassMeets H c then
    centralCharacterInCyclotomicOrder heta chi hchi c else 0

/-- The sum of the ordinary central character over all ambient conjugacy
classes contained in a normal subgroup. -/
private noncomputable def centralCharacterSum
    {G : Type u} [Group G] [Finite G]
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (H : Subgroup G)
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi) :
    cyclotomicOrder eta :=
  ∑ c : ConjClasses G, centralCharacterContribution heta H chi hchi c

private theorem coe_centralCharacterSum
    {G : Type u} [Group G] [Finite G]
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (H : Subgroup G) [H.Normal]
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi) :
    (centralCharacterSum heta H chi hchi : ℂ) =
      (∑ h : H, chi (ConjClasses.mk (h : G))) /
        chi (ConjClasses.mk (1 : G)) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  rw [sum_normalSubgroup_eq_sum_classes H chi]
  rw [centralCharacterSum]
  change (Subring.subtype (cyclotomicOrder eta))
      (∑ c : ConjClasses G,
        centralCharacterContribution heta H chi hchi c) = _
  rw [map_sum]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hcH : ClassMeets H c
  · simp [centralCharacterContribution,
      classContribution, hcH, centralCharacterInCyclotomicOrder,
      ordinaryCentralCharacterValue, div_eq_mul_inv]
  · simp [centralCharacterContribution,
      classContribution, hcH]

/-- Summing the defining central-character congruences over the conjugacy
classes contained in a normal subgroup preserves the congruence. -/
private theorem centralCharacterSum_sub_mem_of_sameTwoBlock
    {G : Type u} [Group G] [Finite G]
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (P : Ideal (cyclotomicOrder eta))
    (H : Subgroup G)
    (chi psi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi)
    (hpsi : IsIrreducibleConjCharacter psi)
    (hsame : SameTwoBlock heta P chi psi hchi hpsi) :
    centralCharacterSum heta H chi hchi -
        centralCharacterSum heta H psi hpsi ∈ P := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  rw [centralCharacterSum, centralCharacterSum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun c _hc => ?_
  by_cases hcH : ClassMeets H c
  · simpa [centralCharacterContribution, hcH] using
      (sameTwoBlock_iff heta P chi psi hchi hpsi).mp hsame c
  · simp [centralCharacterContribution, hcH]

/-- The summed central character of the principal character is the cardinality
of the normal subgroup. -/
private theorem centralCharacterSum_principal_eq_card
    {G : Type u} [Group G] [Finite G]
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (H : Subgroup G) [H.Normal] :
    centralCharacterSum heta H (ordinaryPrincipalCharacter G)
        ordinaryPrincipalCharacter_irreducible =
      (Nat.card H : cyclotomicOrder eta) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  apply Subtype.ext
  rw [coe_centralCharacterSum]
  simp [ordinaryPrincipalCharacter]

/-- In a quotient in which `2` vanishes, every odd natural number reduces to
`1`. -/
private theorem odd_natCast_eq_one_mod_two
    {eta : ℂ} (P : Ideal (cyclotomicOrder eta))
    (htwo : Ideal.Quotient.mk P
      (2 : cyclotomicOrder eta) = 0)
    {n : ℕ} (hn : Odd n) :
    Ideal.Quotient.mk P
      (n : cyclotomicOrder eta) = 1 := by
  rcases hn with ⟨k, rfl⟩
  push_cast
  simp [htwo]

/-- A character congruent to the principal character has nonzero summed
central character on every normal subgroup of odd order. -/
private theorem centralCharacterSum_ne_zero_of_samePrincipal
    {G : Type u} [Group G] [Finite G]
    {eta : ℂ} (heta : IsPrimitiveRoot eta (Nat.card G))
    (P : Ideal (cyclotomicOrder eta))
    (hPmax : P.IsMaximal)
    (htwo : Ideal.Quotient.mk P
      (2 : cyclotomicOrder eta) = 0)
    (H : Subgroup G) [H.Normal]
    (hHodd : Odd (Nat.card H))
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi)
    (hsame : SameTwoBlock heta P chi
      (ordinaryPrincipalCharacter G) hchi
      ordinaryPrincipalCharacter_irreducible) :
    centralCharacterSum heta H chi hchi ≠ 0 := by
  let : Nontrivial
      ((cyclotomicOrder eta) ⧸ P) :=
    Ideal.Quotient.nontrivial_iff.mpr hPmax.ne_top
  have hcongr := centralCharacterSum_sub_mem_of_sameTwoBlock
    heta P H chi (ordinaryPrincipalCharacter G)
      hchi ordinaryPrincipalCharacter_irreducible hsame
  have hquot : Ideal.Quotient.mk P (centralCharacterSum heta H chi hchi) = 1 := by
    calc
      Ideal.Quotient.mk P (centralCharacterSum heta H chi hchi) =
          Ideal.Quotient.mk P
            (centralCharacterSum heta H
              (ordinaryPrincipalCharacter G)
              ordinaryPrincipalCharacter_irreducible) :=
        Ideal.Quotient.eq.mpr hcongr
      _ = Ideal.Quotient.mk P
          (Nat.card H : cyclotomicOrder eta) := by
        rw [centralCharacterSum_principal_eq_card]
      _ = 1 := odd_natCast_eq_one_mod_two P htwo hHodd
  intro hzero
  rw [hzero, map_zero] at hquot
  exact zero_ne_one hquot

/-- Feit IV.4.12(ii), in the form needed here: the odd core is contained in
the kernel of every representation affording a character in the principal
congruence `2`-block. -/
public theorem pPrimeCore_le_representation_ker_of_mem_block
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    {i : d.I} (hi : i ∈ d.block)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ))
    (hchar : d.chi i = characterClassFunction rho) :
    pPrimeCore 2 G ≤ rho.ker := by
  classical
  let H : Subgroup G := pPrimeCore 2 G
  let : H.Normal := pPrimeCore_normal (p := 2) (G := G)
  let : Fintype H := Fintype.ofFinite H
  have hHodd : Odd (Nat.card H) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Nat.coprime_two_left]
    simpa [H] using pPrimeCore_coprime_card (p := 2) (G := G)
  have hsamePrincipal : SameTwoBlock d.eta_spec d.primeIdeal
      (d.chi i) (ordinaryPrincipalCharacter G)
      (d.complete.1 i) ordinaryPrincipalCharacter_irreducible := by
    simpa [d.principal_eq] using (d.mem_block_iff i).mp hi
  have hcentralNe :
      centralCharacterSum d.eta_spec H (d.chi i) (d.complete.1 i) ≠ 0 :=
    centralCharacterSum_ne_zero_of_samePrincipal d.eta_spec d.primeIdeal
      d.primeIdeal_maximal d.two_eq_zero_mod_primeIdeal H hHodd
      (d.chi i) (d.complete.1 i) hsamePrincipal
  have hcentralCoeNe :
      (centralCharacterSum d.eta_spec H (d.chi i) (d.complete.1 i) : ℂ) ≠ 0 := by
    intro hzero
    apply hcentralNe
    apply Subtype.ext
    exact hzero
  rw [coe_centralCharacterSum] at hcentralCoeNe
  have hsumChi :
      (∑ h : H, d.chi i (ConjClasses.mk (h : G))) ≠ 0 := by
    intro hzero
    apply hcentralCoeNe
    simp [hzero]
  have hsumEq :
      (∑ h : H, d.chi i (ConjClasses.mk (h : G))) =
        ∑ h : H, rho.character (h : G) := by
    apply Finset.sum_congr rfl
    intro h _hh
    rw [hchar]
    rfl
  have hsumRho : (∑ h : H, rho.character (h : G)) ≠ 0 := by
    rwa [hsumEq] at hsumChi
  have hrhoIrr : Representation.IsIrreducible rho :=
    (irreducible_iff_character_norm_one (ρ := rho)).2 (by
      rw [← hchar]
      exact (d.complete.1 i).2)
  let : Representation.IsIrreducible rho := hrhoIrr
  rcases normalSubgroup_norm_eq_zero_or_le_ker rho H with hnorm | hker
  · exact (hsumRho
      (sum_character_eq_zero_of_normalSubgroup_norm_eq_zero rho H hnorm)).elim
  · exact hker

/-- Character-value form of the odd-core kernel theorem. -/
public theorem character_mul_right_eq_of_mem_block
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    {i : d.I} (hi : i ∈ d.block)
    (g v : G) (hv : v ∈ pPrimeCore 2 G) :
    d.chi i (ConjClasses.mk (g * v)) =
      d.chi i (ConjClasses.mk g) := by
  rcases (d.complete.1 i).1 with ⟨n, rho, hchar⟩
  have hvker : v ∈ rho.ker :=
    pPrimeCore_le_representation_ker_of_mem_block d hi rho hchar hv
  rw [MonoidHom.mem_ker] at hvker
  rw [hchar]
  change rho.character (g * v) = rho.character g
  simp [Representation.character, map_mul, hvker]

/-- Any weighted sum of characters from the principal congruence block is
unchanged by right multiplication by an element of the odd core. -/
public theorem weighted_block_sum_mul_right_eq
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    (a : d.I → ℂ) (g v : G) (hv : v ∈ pPrimeCore 2 G) :
    ∑ i ∈ d.block, a i * d.chi i (ConjClasses.mk (g * v)) =
      ∑ i ∈ d.block, a i * d.chi i (ConjClasses.mk g) := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [character_mul_right_eq_of_mem_block d hi g v hv]

end PrincipalBlockKernel

end ModularBlock

