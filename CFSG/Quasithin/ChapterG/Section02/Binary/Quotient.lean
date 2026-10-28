module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Core
public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# The literal elementary quotient of the binary almost-special core

The two-core normalizes both marked factors. Their commutators lie in
their intersection, and the Frattini bound puts their squares there too.
Their product therefore has an elementary abelian quotient. This is the
quotient used for G.2.3(6), not an assumed module or a semisimplicity claim.

Source: Aschbacher–Smith, G.2.3, printed pp.333–334.
-/

open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G]

/-- Elementary abelianness of the actual S/S₂ from the source square
bound and the proved core factorization. -/
public theorem binary_quotient_elementary (D : Setup G) (g : G)
    (hg : g ∈ D.I g) (hgV : g ∈ normalizer (D.V : Set G))
    (hpoint : D.V₁ ≤ D.V) (hVE : D.V ≤ D.S₂ g) (hES : D.S₂ g ≤ D.S g)
    (hEN : D.I g ≤ normalizer (D.S₂ g : Set G))
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hsquare : ∀ u ∈ D.U, u ^ 2 ∈ D.V₁) :
    letI : ((D.S₂ g).subgroupOf (D.S g)).Normal := normal_subgroupOf_of_le_normalizer
      ((pCoreIn_le 2 (D.I g)).trans hEN)
    IsElementaryAbelian 2 ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g)) := by
  let S := D.S g
  let N := (D.S₂ g).subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 (D.I g)).trans hEN)
  change IsElementaryAbelian 2 (S ⧸ N)
  let q := QuotientGroup.mk' N
  have hW : D.U ⊓ S = D.W g := rfl
  have hWS : D.W g ≤ S := le_sup_left.trans hsplit.ge
  have hXS : conjugate (D.W g) g ≤ S := le_sup_right.trans hsplit.ge
  have hSW : S ≤ normalizer (D.W g : Set G) := by
    rw [← hW]
    exact (le_inf hnorm S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hSg : conjugate S g = S :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (S : Set G)).inv_mem (D.binary_core_normalized g hg))
  have hSX : S ≤ normalizer (conjugate (D.W g) g : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hSW).trans
      ((D.W g).le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    change conjugate S g ≤ normalizer (conjugate (D.W g) g : Set G) at hh
    rwa [hSg] at hh
  have hWX : ⁅D.W g, conjugate (D.W g) g⁆ ≤ D.S₂ g := by
    rw [D.binary_marked_intersection g hg hES]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hXS.trans hSW))
      (le_normalizer_iff_commutator_le_right.mp (hWS.trans hSX))
  have hsqW : ∀ w ∈ D.W g, w ^ 2 ∈ D.S₂ g :=
    fun w hw => hVE (hpoint (hsquare w hw.1))
  have hsqX : ∀ x ∈ conjugate (D.W g) g, x ^ 2 ∈ D.S₂ g := by
    rintro x ⟨w, hw, rfl⟩
    apply hVE
    have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom
      (hpoint (hsquare w (show w ∈ D.U from hw.1)))
    have hVg : D.V.map (MulAut.conj g⁻¹).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (D.V : Set G)).inv_mem hgV)
    rw [hVg] at hh
    simpa only [map_pow] using hh
  have hsq : ∀ a : S ⧸ N, a ^ 2 = 1 := by
    intro a
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N a
    have hprod : (s : G) ∈ (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hXS.trans hSW), ← hsplit]
      exact s.property
    obtain ⟨w, hw, x, hx, hwx⟩ := hprod
    let wS : S := ⟨w, hWS hw⟩
    let xS : S := ⟨x, hXS hx⟩
    have hs : wS * xS = s := Subtype.ext hwx
    have hqw : (q wS) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqW w hw)
    have hqx : (q xS) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqX x hx)
    have hqcomm : Commute (q wS) (q xS) := by
      change q wS * q xS = q xS * q wS
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hWX (commutator_mem_commutator hw hx))
    change (q s) ^ 2 = 1
    rw [← hs, map_mul, hqcomm.mul_pow, hqw, hqx, mul_one]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

end CFSG.Quasithin.ChapterG.Section02.Setup
