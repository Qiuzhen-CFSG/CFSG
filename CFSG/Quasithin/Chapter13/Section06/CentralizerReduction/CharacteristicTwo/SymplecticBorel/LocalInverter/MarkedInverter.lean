module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ResidualAction
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.SylowLocalCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A marked Sylow element inverting the local cubic quotient

Intersect the specified Sylow two-subgroup of C_G(v) with C_L(v).
Relative normalization suffices: restrict first to the normalizer of C_L(v)
inside C_G(v). The marked A₅ action with two-group kernel then proves
[Lᵥ, Tᵥ ∩ L] = Lᵥ by the S₃ stabilizer's normal generation.
Consequently the action on Lᵥ/O₂(Lᵥ) cannot be trivial. Its order is three,
so a nonidentity actor inverts the quotient. The resulting element lies in
the actual Tᵥ ∩ L; its own order need not be two.

The earlier quotient cardinal remains explicit and is discharged by the
marked residual module calculation in the higher configuration assembly.
`MarkedInverter.Transport` applies the result to the literal Borel quotient
and the parent's residual-displacement convention.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed p.928 (PDF p.945).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
open Subgroup

private theorem cubic_aut_inverts {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 3) (f : MulAut Q) (hf : f ≠ 1) : ∀ q, f q = q⁻¹ := by
  classical
  let : IsCyclic Q := isCyclic_of_prime_card hQ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  have ho : orderOf g = 3 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hQ
  have hpow : g ^ 3 = 1 := ho ▸ pow_orderOf_eq_one g
  have hsq : g ^ 2 = g⁻¹ := by
    apply mul_right_cancel (b := g)
    simpa [pow_succ] using hpow
  have hfg : f g = g⁻¹ := by
    have hm := hg (f g)
    rw [(isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf, ho] at hm
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    have hn3 := Finset.mem_range.mp hn
    interval_cases n
    · have hgone : g = 1 := f.injective (by simpa using he.symm)
      simp [hgone] at ho
    · exfalso
      apply hf
      ext q
      change f q = q
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg q)
      rw [map_zpow, show f g = g from by simpa using he.symm]
    · simpa [hsq] using he.symm
  intro q
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg q)
  rw [map_zpow, hfg, inv_zpow]

open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- Restrict the given Sylow to C_L(v), using normality only inside
its relative normalizer. The marked S₃ stabilizer then gives the commutator identity
with the actual intersection Tᵥ ∩ L. -/
theorem marked_intersection_commutator (s : Marking L V) (T : Subgroup G)
    (hk : s.action.ker = pCore 2 L) (hTL : T ≤ normalizer (L : Set G))
    (P : Sylow 2 (Gv (markedV s)))
    (hP : (P : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype = Tv T (markedV s)) :
    ⁅Lv L (markedV s), Tv T (markedV s) ⊓ L⁆ = Lv L (markedV s) := by
  let H := Gv (markedV s)
  let J := L.subgroupOf H
  have hPJ : (P : Subgroup H) ≤ normalizer (J : Set H) := by
    apply le_normalizer_iff.mpr
    intro t ht j hj
    have htT : t.val ∈ T := (hP ▸ mem_map_of_mem H.subtype ht).1
    exact le_normalizer_iff.mp hTL t.val htT j.val hj
  obtain ⟨S, hS⟩ := (P.subtype hPJ).exists_map_subtype_eq_inf_of_normalizes
    J.le_normalizer le_rfl
  rw [P.coe_subtype, map_subgroupOf_eq_of_le hPJ] at hS
  let e : J ≃* (L ⊓ H : Subgroup G) :=
    (J.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype L H))
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRT : (R : Subgroup (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ Tv T (markedV s) ⊓ L := by
    rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    have hjP : j.val ∈ (P : Subgroup H) := (hS ▸ mem_map_of_mem J.subtype hj).1
    exact ⟨hP ▸ mem_map_of_mem H.subtype hjP, j.property⟩
  have he : Tv (Tv T (markedV s) ⊓ L) (markedV s) = Tv T (markedV s) ⊓ L :=
    inf_eq_left.mpr (inf_le_left.trans inf_le_right)
  have hc := ComponentReduction.NormalizedBorel.ambient_residual_commutator s
    (Tv T (markedV s) ⊓ L) (hk ▸ pCore_isPGroup)
    (inf_le_right.trans L.le_normalizer) R hRT
  rwa [he] at hc

private theorem quotient_inverter_of_commutator (D A : Subgroup G)
    (hAN : A ≤ normalizer (D : Set G)) (hc : ⁅D, A⁆ = D)
    (hcard : Nat.card (D ⧸ pCore 2 D) = 3) :
    ∃ x ∈ A, ∃ hxN : x ∈ normalizer (D : Set G),
      ∀ d : D, QuotientGroup.mk' (pCore 2 D) (D.normalizerMonoidHom ⟨x, hxN⟩ d) =
        (QuotientGroup.mk' (pCore 2 D) d)⁻¹ := by
  classical
  let a (x : A) : MulAut (D ⧸ pCore 2 D) :=
    quotientAut (pCore 2 D) (D.normalizerMonoidHom ⟨x, hAN x.property⟩)
  have hn : ∃ x : A, a x ≠ 1 := by
    by_contra hn
    push Not at hn
    have hcomm : ⁅A, D⁆ ≤ (pCore 2 D).map D.subtype := by
      apply commutator_le.mpr
      intro x hx d hd
      let α := D.normalizerMonoidHom ⟨x, hAN hx⟩
      let δ : D := ⟨d, hd⟩
      have hfix : QuotientGroup.mk' (pCore 2 D) (α δ) =
          QuotientGroup.mk' (pCore 2 D) δ := by
        have he := DFunLike.congr_fun (hn ⟨x, hx⟩) (QuotientGroup.mk' (pCore 2 D) δ)
        change quotientAut (pCore 2 D) α (QuotientGroup.mk' (pCore 2 D) δ) =
          QuotientGroup.mk' (pCore 2 D) δ at he
        rwa [quotientAut_apply_mk] at he
      have hm : α δ * δ⁻¹ ∈ pCore 2 D := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' (pCore 2 D) (α δ * δ⁻¹) = 1
        rw [map_mul, map_inv, hfix, mul_inv_cancel]
      exact ⟨α δ * δ⁻¹, hm, rfl⟩
    rw [commutator_comm, hc] at hcomm
    have hcore : pCore 2 D = ⊤ := by
      apply top_unique
      intro d _
      exact (mem_map_iff_mem D.subtype_injective).mp (hcomm d.property)
    have hone : Nat.card (D ⧸ pCore 2 D) = 1 := by
      rw [hcore]
      exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    omega
  obtain ⟨x, hx⟩ := hn
  refine ⟨x, x.property, hAN x.property, ?_⟩
  intro d
  simpa only [a, quotientAut_apply_mk] using
    cubic_aut_inverts hcard (a x) hx (QuotientGroup.mk' (pCore 2 D) d)

/-- The actual Sylow intersection contains an inverter of the literal
residual quotient. The cardinal-three premise is the earlier marked residual
module calculation; no actor or inversion identity is assumed. -/
theorem exists_marked_inverter (s : Marking L V) (T : Subgroup G)
    (hk : s.action.ker = pCore 2 L) (hTL : T ≤ normalizer (L : Set G))
    (P : Sylow 2 (Gv (markedV s)))
    (hP : (P : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype = Tv T (markedV s))
    (hcard : Nat.card (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) = 3) :
    ∃ x ∈ Tv T (markedV s) ⊓ L,
      ∃ hxN : x ∈ normalizer (Lv L (markedV s) : Set G),
        ∀ d : Lv L (markedV s),
          QuotientGroup.mk' (pCore 2 (Lv L (markedV s)))
            ((Lv L (markedV s)).normalizerMonoidHom ⟨x, hxN⟩ d) =
          (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))) d)⁻¹ := by
  apply quotient_inverter_of_commutator _ _ _
    (marked_intersection_commutator s T hk hTL P hP) hcard
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ Gv (markedV s)) (pResidual 2 (L ⊓ Gv (markedV s) : Subgroup G)))
  exact (le_inf (inf_le_right.trans L.le_normalizer)
    ((inf_le_left.trans inf_le_right).trans (Gv (markedV s)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
