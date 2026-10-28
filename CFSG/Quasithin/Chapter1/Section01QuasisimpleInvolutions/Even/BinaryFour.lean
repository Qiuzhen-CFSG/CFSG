module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Inner
public import Theory.Alternating.OddCentralCovers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The binary degree-four cover in 1.1.5

The actual PSL₄(2) quotient is A₈, whose universal central kernel bounds the
center of the original quasisimple group by two. If that center is nontrivial,
the original inner involutory automorphism is the prescribed lift of an
involution in S₈. Schur's double-cover calculation gives index two for the
image of its fixed subgroup. Pointwise fixation of the original Sylow
two-subgroup instead makes that same fixed-subgroup map surjective.

The contradiction removes the double cover and gives canonical source row
(a) with the original automorphism. No involutory representative upstairs is
assumed. All field, quotient and finite-universe transports are explicit.

Source: Aschbacher--Smith, 1.1.5(3), printed pp.501--502; GLS3, Theorem
5.2.3 and Proposition 5.2.8(b).
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory
open GLS3.Chapter5 GLS3.Chapter5.SchurPresentation

namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure

private theorem doubleCover_no_fixed_sylow_small
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 8)))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (a : MulAut G) (ha : a ^ 2 = 1) (P : Sylow 2 G)
    (hP : ∀ x ∈ P, a x = x)
    (σ : Equiv.Perm (Fin 8)) (hσ : orderOf σ = 2)
    (heq : ∀ x, f (a x) =
      MulAut.conjNormal (H := alternatingGroup (Fin 8)) σ (f x)) : False := by
  let b : MulAut (alternatingGroup (Fin 8)) := MulAut.conjNormal σ
  have hfac : f.comp (Covering.ofMulEquiv a) =
      (Covering.ofMulEquiv b).comp f := by
    apply Covering.ext
    exact heq
  have hlift : a = doubleCoverLiftMulAut 3 f hcard b :=
    doubleCoverLiftMulAut_unique 3 f hcard b hfac
  have hsurj := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed
    a b f.toMonoidHom f.surjective f.ker_le_center heq ha P hP
  have hmap : (automorphismFixedSubgroup a).map f.toMonoidHom =
      automorphismFixedSubgroup b := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change b (f x) = f x
      rw [← heq x]
      change a x = x at hx
      rw [hx]
    · intro y hy
      have hy' : y ∈ b.fixedSubgroup := by
        rw [MulAut.mem_fixedSubgroup]
        exact hy
      obtain ⟨x, hx⟩ := hsurj ⟨y, hy'⟩
      refine ⟨x, ?_, congrArg Subtype.val hx⟩
      change a x = x
      exact (MulAut.mem_fixedSubgroup _ _).mp x.property
  obtain ⟨_, hindex, _⟩ := proposition_5_2_8_b 3 f hcard σ hσ
  change (((automorphismFixedSubgroup (doubleCoverLiftMulAut 3 f hcard b)).map
    f.toMonoidHom).subgroupOf (automorphismFixedSubgroup b)).index = 2 at hindex
  rw [← hlift, hmap, subgroupOf_self, index_top] at hindex
  omega

private theorem doubleCover_no_fixed_sylow
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 8)))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (a : MulAut G) (ha : a ^ 2 = 1) (P : Sylow 2 G)
    (hP : ∀ x ∈ P, a x = x)
    (σ : Equiv.Perm (Fin 8)) (hσ : orderOf σ = 2)
    (heq : ∀ x, f (a x) =
      MulAut.conjNormal (H := alternatingGroup (Fin 8)) σ (f x)) : False := by
  obtain ⟨E, iE, finE, ⟨s⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} G
  let := iE
  let := finE
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv s
  let fE := f.comp (Covering.ofMulEquiv s.symm)
  have hcardE : Nat.card fE.toMonoidHom.ker = 2 := by
    rw [← hcard]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨s.symm x, x.property⟩
      invFun := fun x => ⟨s x, by
        change f (s.symm (s x)) = 1
        rw [s.symm_apply_apply]
        exact x.property⟩
      left_inv := fun x => Subtype.ext (s.apply_symm_apply x)
      right_inv := fun x => Subtype.ext (s.symm_apply_apply x) }
  let aE := MulAut.congr s a
  let PE := P.mapSurjective (f := s.toMonoidHom) s.surjective
  have haE : aE ^ 2 = 1 := by
    change (MulAut.congr s a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have hPE : ∀ x ∈ PE, aE x = x := by
    rintro x ⟨y, hy, rfl⟩
    change s (a (s.symm (s y))) = s y
    rw [s.symm_apply_apply, hP y hy]
  apply doubleCover_no_fixed_sylow_small fE hcardE aE haE PE hPE σ hσ
  intro x
  change f (s.symm (s (a (s.symm x)))) =
    MulAut.conjNormal (H := alternatingGroup (Fin 8)) σ (f (s.symm x))
  rw [s.symm_apply_apply]
  exact heq (s.symm x)

private noncomputable def binaryFourAlternatingEquiv {H : Type*} [Group H]
    (h : ClassicalGroup.IsPSL H 4 2) : H ≃* alternatingGroup (Fin 8) :=
  Classical.choice <| by
    obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
    let : Fintype F := Fintype.ofFinite F
    have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
    exact ⟨(e.trans (Atlas.fieldEquivPSL 4 (FiniteField.ringEquivOfCardEq hcard'))).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The marked PSL₄(2) source group has trivial center. The only possible
nontrivial cover contradicts fixed-point surjectivity on the original Sylow. -/
theorem MarkedInvolution.binaryFour_center_eq_bot
    (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 4 2) : center L = ⊥ := by
  let e := binaryFourAlternatingEquiv h
  have hd := OddCentralCovers.center_card_dvd_two_of_nonexceptional
    8 (by decide) (by decide) (by decide) e
  by_contra hz
  have htwo : Nat.card (center L) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (fun hc => hz (card_eq_one.mp hc))
  let f : Covering L (alternatingGroup (Fin 8)) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hk : f.toMonoidHom.ker = center L := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ center L
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hcard : Nat.card f.toMonoidHom.ker = 2 := hk ▸ htwo
  obtain ⟨t, ht⟩ := d.binaryLinear_inner (.inl rfl) h
  let σ : Equiv.Perm (Fin 8) := f t
  let b := MulAut.centralQuotientAction e α
  have hb : b = MulAut.conjNormal (H := alternatingGroup (Fin 8)) σ := by
    change MulAut.centralQuotientAction e α = _
    rw [← ht, MulAut.centralQuotientAction_conj]
    ext x
    rfl
  have hσ : orderOf σ = 2 := by
    calc
      orderOf σ = orderOf (MulAut.conjNormal
          (H := alternatingGroup (Fin 8)) σ) :=
        (orderOf_injective _
          (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 8 (by decide))
          σ).symm
      _ = orderOf b := congrArg orderOf hb.symm
      _ = 2 := (MulAut.orderOf_centralQuotientAction e α).trans d.order_two
  apply doubleCover_no_fixed_sylow f hcard α
    (d.order_two ▸ pow_orderOf_eq_one α) P d.fixes σ hσ
  intro x
  rw [← hb]
  exact (MulAut.centralQuotientAction_apply e α x).symm

/-- Canonical source row (a) for the actual binary degree-four quotient,
including exclusion of its nontrivial two-cover and the original action. -/
theorem MarkedInvolution.binaryFour_modelAction
    (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 4 2) : ModelAction115 L α :=
  d.lie_of_center_eq_bot (.inr (.inr ⟨4, .inl rfl, h⟩))
    (d.binaryLinear_inner (.inl rfl) h) (d.binaryFour_center_eq_bot h)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
