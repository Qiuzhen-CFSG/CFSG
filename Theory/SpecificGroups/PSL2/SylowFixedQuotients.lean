module

public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.OddCenters
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# Sylow centers and fixed quotient actions in odd-prime PSL₂

For primes p ≥ 7 adjacent to a power of two, the dihedral Sylow calculation
gives centers of order at most two. The remaining parameter five requires
the pointwise-fixer and quotient calculations below.

The genuine projective matrix group is transported to A₅ through the proved
icosahedral isomorphism. Its Sylow two-subgroups have order four, and their
pointwise fixing automorphisms are conjugations by elements of the Sylow
subgroup.

If a Sylow subgroup P normalizes D and D/O₂(D) is a three-group, then D has
no element of order five. The A₅ permutation calculation makes D normalize
P. Thus P ∩ D is a normal two-subgroup of D and all conjugation displacements
lie in O₂(D). This proves identity on the literal quotient, including D = 1.
The argument does not need the additional two-perfect hypothesis supplied
by the source consumer.

These are the characteristic-five model calculations in the component
branch of Aschbacher–Smith 15.4.20, printed p.1164, using 1.1.5(3)(e).
They do not assert the final component-case elimination.
-/

open scoped MatrixGroups
open Subgroup
namespace Theory.PSL2.SylowFixedQuotients

private theorem no_five {G : Type*} [Group G]
    (hG : IsPGroup 3 (G ⧸ pCore 2 G)) (x : G) (hx : x ^ 5 = 1) : x = 1 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hqx : q x = 1 := (hG.powEquiv (by decide : Nat.Coprime 3 5)).injective (by
    simp only [IsPGroup.powEquiv_apply, ← map_pow, hx, map_one, one_pow])
  have hxmem : x ∈ pCore 2 G := (QuotientGroup.eq_one_iff x).mp hqx
  let h := (pCore_isPGroup (p := 2) (G := G)).powEquiv (by decide : Nat.Coprime 2 5)
  have hh : (⟨x, hxmem⟩ : pCore 2 G) = 1 := h.injective (by
    simp only [h, IsPGroup.powEquiv_apply, one_pow]
    exact Subtype.ext hx)
  exact congrArg Subtype.val hh

variable {G : Type*} [Group G] [Finite G]

private theorem mutual_normalizes_of_equiv_five (e : G ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 G) (D : Subgroup G)
    (hD : ∀ d ∈ D, d ^ 5 = 1 → d = 1)
    (hn : (P : Subgroup G) ≤ normalizer (D : Set G)) :
    D ≤ normalizer (P : Set G) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn' : (Q : Subgroup (alternatingGroup (Fin 5))) ≤
      normalizer (D.map e.toMonoidHom : Set (alternatingGroup (Fin 5))) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hn
  have hD' : ∀ d ∈ D.map e.toMonoidHom, d ^ 5 = 1 → d = 1 := by
    rintro _ ⟨d, hd, rfl⟩ hpow
    change (e d) ^ 5 = 1 at hpow
    have hd5 : d ^ 5 = 1 := e.injective (by simpa only [map_pow, map_one] using hpow)
    rw [hD d hd hd5, map_one]
  have hh := alternating_mutual_normalizes_of_no_five Q (D.map e.toMonoidHom) hD' hn'
  change D.map e.toMonoidHom ≤ normalizer ((P : Subgroup G).map e.toMonoidHom : Set _) at hh
  rw [← Subgroup.map_equiv_normalizer_eq] at hh
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp hh

omit [Finite G] in
private theorem conj_quotient_of_mutual_normalizes (P : Subgroup G) (D : Subgroup G)
    (hp : IsPGroup 2 P) (hn : P ≤ normalizer (D : Set G))
    (hm : D ≤ normalizer (P : Set G)) (p : P) :
    quotientAut (pCore 2 D) (D.normalizerMonoidHom ⟨p, hn p.property⟩) = 1 := by
  have hnorm : D ≤ normalizer ((P ⊓ D : Subgroup G) : Set G) :=
    (le_inf hm D.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hcore : P ⊓ D ≤ D.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hp.to_le inf_le_left) inf_le_right hnorm
  have hdisp (x : D) :
      x⁻¹ * D.normalizerMonoidHom ⟨p, hn p.property⟩ x ∈ pCore 2 D := by
    have hxP : (x : G)⁻¹ * (p : G) * (x : G) ∈ P :=
      by
        have hh := (hm (D.inv_mem x.property) p).mp p.property
        rw [inv_inv] at hh
        exact hh
    have hxP' : (x : G)⁻¹ * ((p : G) * (x : G) * (p : G)⁻¹) ∈ P := by
      simpa only [mul_assoc] using P.mul_mem hxP (P.inv_mem p.property)
    have hxD : (x : G)⁻¹ * ((p : G) * (x : G) * (p : G)⁻¹) ∈ D :=
      D.mul_mem (D.inv_mem x.property) ((hn p.property x).mp x.property)
    obtain ⟨y, hy, he⟩ := hcore ⟨hxP', hxD⟩
    have he' : y = x⁻¹ * D.normalizerMonoidHom ⟨p, hn p.property⟩ x :=
      Subtype.ext he
    exact he' ▸ hy
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) x
  rw [quotientAut_apply_mk]
  exact (QuotientGroup.eq.mpr (hdisp y)).symm

/-- Sylow order transported through an actual isomorphism with A₅. -/
public theorem sylow_card_of_equiv_five (e : G ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 G) : Nat.card P = 4 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (Nat.card_congr ((P : Subgroup G).equivMapOfInjective e.toMonoidHom
    e.injective).toEquiv).trans (alternating_sylow_card Q)

/-- Pointwise Sylow fixers transported through an actual isomorphism with A₅. -/
public theorem sylow_fixed_inner_of_equiv_five (e : G ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 G) (β : MulAut G) (hβ : ∀ x ∈ P, β x = x) :
    ∃ x ∈ P, β = MulAut.conj x := by
  exact fixed_inner_transport e (P : Subgroup G)
    (alternating_sylow_fixed_inner (P.mapSurjective (f := e.toMonoidHom) e.surjective)) β hβ

/-- Conjugation by the Sylow subgroup is the identity on the actual
three-group quotient by the intrinsic two-core. -/
public theorem sylow_conj_quotient_of_equiv_five (e : G ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 G) (D : Subgroup G)
    (hn : (P : Subgroup G) ≤ normalizer (D : Set G))
    (hq : IsPGroup 3 (D ⧸ pCore 2 D)) (p : P) :
    quotientAut (pCore 2 D) (D.normalizerMonoidHom ⟨p, hn p.property⟩) = 1 := by
  have hm := mutual_normalizes_of_equiv_five e P D (fun d hd hpow =>
    congrArg Subtype.val (no_five hq ⟨d, hd⟩ (Subtype.ext hpow))) hn
  exact conj_quotient_of_mutual_normalizes (P : Subgroup G) D P.isPGroup' hn hm p

/-- A pointwise Sylow fixer preserves D and acts trivially on D/O₂(D). -/
public theorem sylow_fixed_quotient_of_equiv_five (e : G ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 G) (D : Subgroup G)
    (hn : (P : Subgroup G) ≤ normalizer (D : Set G))
    (hq : IsPGroup 3 (D ⧸ pCore 2 D))
    (β : MulAut G) (hβ : ∀ x ∈ P, β x = x) :
    ∃ hD : D.map β.toMonoidHom = D,
      quotientAut (pCore 2 D) ((β.subgroupMap D).trans (MulEquiv.subgroupCongr hD)) = 1 := by
  obtain ⟨p, hp, rfl⟩ := sylow_fixed_inner_of_equiv_five e P β hβ
  refine ⟨mem_normalizer_iff_map_conj_eq.mp (hn hp), ?_⟩
  have he : ((MulAut.conj p).subgroupMap D).trans
      (MulEquiv.subgroupCongr (mem_normalizer_iff_map_conj_eq.mp (hn hp))) =
      D.normalizerMonoidHom ⟨p, hn hp⟩ := by
    ext x
    rfl
  rw [he]
  exact sylow_conj_quotient_of_equiv_five e P D hn hq ⟨p, hp⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Every Sylow two-subgroup of the actual PSL₂(5) has order four. -/
public theorem sylow_five_card (P : Sylow 2 PSL(2, ZMod 5)) : Nat.card P = 4 := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact sylow_card_of_equiv_five e P

/-- Every pointwise Sylow fixer of the actual PSL₂(5) is conjugation by an
 element of that Sylow subgroup. -/
public theorem sylow_five_fixed_inner (P : Sylow 2 PSL(2, ZMod 5))
    (β : MulAut PSL(2, ZMod 5)) (hβ : ∀ x ∈ P, β x = x) :
    ∃ x ∈ P, β = MulAut.conj x := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact sylow_fixed_inner_of_equiv_five e P β hβ

/-- The Sylow subgroup of PSL₂(5) acts trivially on the literal quotient
D/O₂(D) whenever it normalizes D and that quotient is a three-group. -/
public theorem sylow_five_conj_quotient (P : Sylow 2 PSL(2, ZMod 5))
    (D : Subgroup PSL(2, ZMod 5))
    (hn : (P : Subgroup PSL(2, ZMod 5)) ≤ normalizer (D : Set PSL(2, ZMod 5)))
    (hq : IsPGroup 3 (D ⧸ pCore 2 D)) (p : P) :
    quotientAut (pCore 2 D) (D.normalizerMonoidHom ⟨p, hn p.property⟩) = 1 := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact sylow_conj_quotient_of_equiv_five e P D hn hq p

/-- Every pointwise Sylow fixer of PSL₂(5) preserves the normalized subgroup
D and acts trivially on its three-group quotient by O₂(D). -/
public theorem sylow_five_fixed_quotient (P : Sylow 2 PSL(2, ZMod 5))
    (D : Subgroup PSL(2, ZMod 5))
    (hn : (P : Subgroup PSL(2, ZMod 5)) ≤ normalizer (D : Set PSL(2, ZMod 5)))
    (hq : IsPGroup 3 (D ⧸ pCore 2 D))
    (β : MulAut PSL(2, ZMod 5)) (hβ : ∀ x ∈ P, β x = x) :
    ∃ hD : D.map β.toMonoidHom = D,
      quotientAut (pCore 2 D) ((β.subgroupMap D).trans (MulEquiv.subgroupCongr hD)) = 1 := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact sylow_fixed_quotient_of_equiv_five e P D hn hq β hβ

end Theory.PSL2.SylowFixedQuotients
