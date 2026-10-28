module

public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Sylow normalizers in the binary derived symplectic group

A Sylow two-subgroup of A₆ is dihedral of order eight. Its normalizer fixes
the unique nonidentity element of its center; that involution has centralizer
of order eight. Thus the Sylow subgroup is self-normalizing.

Entrywise field transport and the explicit polar representation identify
Sp₄(F) with S₆ when F has two elements. Restricting this equivalence to
commutators identifies the exact subgroup Sp₄(F)′ with A₆, so its Sylow
two-subgroups are self-normalizing as well. No central quotient is taken.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
`refs/quasithin.pdf`, B.4.2(3),(6), printed p.86; B.5.5(1)(iv), pp.104–105;
and the binary endpoint in the proof of 15.3.49(k),(l), p.1144.
-/

public section

open Subgroup

namespace AlternatingSix.ShadowLocal

/-- The Sylow two-subgroups of the actual six-point alternating group normalize only themselves. -/
theorem sylow_normalizer_eq (P : Sylow 2 A6) :
    normalizer (P : Set A6) = (P : Subgroup A6) := by
  have hc : Nat.card (center P) = 2 := by
    obtain ⟨e⟩ := alternatingSylow_dihedral P
    rw [Nat.card_congr (centerCongr e).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp hc
  let a : A6 := z.val.val
  have ha : orderOf a = 2 := by
    apply orderOf_eq_prime
    · have h := pow_card_eq_one' (x := z)
      rw [hc] at h
      exact congrArg (fun x : center P => x.val.val) h
    · intro h
      exact hz (Subtype.ext (Subtype.ext h))
  have hN : normalizer (P : Set A6) ≤ centralizer ({a} : Set A6) := by
    intro g hg
    let e := centerCongr ((P : Subgroup A6).normalizerMonoidHom ⟨g, hg⟩)
    have hfix : e z = z := huniq (e z) (by
      intro h
      exact hz (e.injective (h.trans (map_one e).symm)))
    have hconj : g * a * g⁻¹ = a := congrArg (fun x : center P => x.val.val) hfix
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj)
  have hC : Nat.card (centralizer ({a} : Set A6)) = 8 := by
    rw [← inner_fixed_eq_centralizer]
    exact inner_involution_fixed_card a ha
  exact (Subgroup.eq_of_le_of_card_ge (P : Subgroup A6).le_normalizer (by
    calc
      Nat.card (normalizer (P : Set A6)) ≤ Nat.card (centralizer ({a} : Set A6)) :=
        Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hN)
      _ = Nat.card P := hC.trans (alternatingSylow_card P).symm)).symm

end AlternatingSix.ShadowLocal

namespace Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F] [Finite F]

namespace Binary

/-- Restrict the explicit binary polar equivalence to commutators before taking any quotient. -/
noncomputable def derivedEquivAlternatingSix (hF : Nat.card F = 2) :
    commutator (Sp F) ≃* alternatingGroup (Fin 6) := by
  let e := (fieldEquivSp (fieldEquivZModTwo F hF)).trans symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

@[simp] theorem derivedEquivAlternatingSix_coe
    (hF : Nat.card F = 2) (g : commutator (Sp F)) :
    (derivedEquivAlternatingSix hF g : Equiv.Perm (Fin 6)) =
      symmetricSixEquiv.symm (fieldEquivSp (fieldEquivZModTwo F hF) (g : Sp F)) := by rfl

end Binary

/-- In the binary derived matrix group every Sylow two-subgroup is self-normalizing. -/
theorem derived_sylow_normalizer_eq_of_card_two (hF : Nat.card F = 2)
    (S : Sylow 2 (commutator (Sp F))) :
    normalizer (S : Set (commutator (Sp F))) = (S : Subgroup (commutator (Sp F))) := by
  let e := Binary.derivedEquivAlternatingSix hF
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Sylow.normalizer_map_surjective S e.toMonoidHom e.surjective]
  exact AlternatingSix.ShadowLocal.sylow_normalizer_eq (S.mapSurjective e.surjective)

end Theory.SpecificGroups.SymplecticFour
