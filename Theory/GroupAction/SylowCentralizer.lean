module

public import Theory.GroupTheory.SylowCentralizerTrivialIntersection
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Sylow actions with centralizer containment

If a nonnormal Sylow subgroup contains the centralizer of each of its
nonidentity elements, its action on the other Sylow subgroups is free and
the ambient action on all Sylow subgroups is faithful. The kernel commutes
with the chosen Sylow subgroup, since its intersection with that subgroup
is trivial; centralizer containment then kills the kernel.

If the chosen Sylow subgroup is transitive on the other Sylow subgroups,
no nonidentity element fixes three Sylow subgroups. After conjugating one
fixed point to the chosen Sylow subgroup, freeness shows that the actor
centralizes the element taking the second fixed point to the third.
Centralizer containment puts the actor in the chosen Sylow subgroup,
and freeness makes it the identity.

Independently, a trivial p-prime core excludes regular normal subgroups in
the Sylow action: such a subgroup would have order equal to the number of
Sylow subgroups, which is coprime to p.

These are the elementary action reductions for Glauberman,
*A Characterization of the Suzuki Groups* (1968), Corollary 5.1, p. 92.
-/

namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
/-- A nonnormal Sylow subgroup has a distinct conjugate. -/
public theorem exists_ne_of_not_normal (P : Sylow p G)
    (hn : ¬ (P : Subgroup G).Normal) : ∃ Q : Sylow p G, Q ≠ P := by
  by_contra! h
  let : Subsingleton (Sylow p G) := ⟨fun Q R => (h Q).trans (h R).symm⟩
  exact hn P.normal_of_subsingleton

/-- A nonidentity element of the chosen Sylow subgroup fixes no other Sylow subgroup. -/
public theorem eq_one_of_smul_eq_of_centralizer_le (P Q : Sylow p G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (hne : Q ≠ P) (x : P) (hx : (x : G) • Q = Q) : x = 1 := by
  have hxN := Sylow.smul_eq_iff_mem_normalizer.mp hx
  have hxQ : (x : G) ∈ (Q : Subgroup G) := by
    have hxI : (x : G) ∈ (P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) :=
      ⟨x.property, hxN⟩
    rw [P.isPGroup'.inf_normalizer_sylow Q] at hxI
    exact hxI.2
  have hxI : (x : G) ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := ⟨x.property, hxQ⟩
  rw [P.inf_eq_bot_of_ne_of_centralizer_le Q hcent hne] at hxI
  exact Subtype.ext (Subgroup.mem_bot.mp hxI)

/-- The conjugation action on Sylow subgroups is faithful under centralizer containment. -/
public theorem toPermHom_injective_of_centralizer_le (P : Sylow p G)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G)) :
    Function.Injective (MulAction.toPermHom G (Sylow p G)) := by
  let ρ := MulAction.toPermHom G (Sylow p G)
  let K : Subgroup G := ρ.ker
  have hKN : K ≤ Subgroup.normalizer (P : Set G) := by
    intro k hk
    exact Sylow.smul_eq_iff_mem_normalizer.mp
      (Equiv.congr_fun (MonoidHom.mem_ker.mp hk) P)
  obtain ⟨Q, hQ⟩ := P.exists_ne_of_not_normal hn
  have hKP : K ⊓ (P : Subgroup G) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have he := P.eq_one_of_smul_eq_of_centralizer_le Q hcent hQ ⟨x, hx.2⟩
      (Equiv.congr_fun (MonoidHom.mem_ker.mp hx.1) Q)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val he)
  have hcomm : ⁅K, (P : Subgroup G)⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    exact (le_inf (Subgroup.commutator_le_left K (P : Subgroup G))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hKN)).trans hKP.le
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro h
    exact hn (h ▸ Subgroup.normal_bot)
  let : Nontrivial P := (P : Subgroup G).nontrivial_iff_ne_bot.mpr hPne
  obtain ⟨x, hx⟩ := exists_ne (1 : P)
  have hxne : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  have hle : K ≤ (P : Subgroup G) := by
    intro k hk
    apply hcent x x.property hxne
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk) x x.property).symm)
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  exact le_antisymm ((le_inf le_rfl hle).trans hKP.le) bot_le

/-- A trivial p-prime core excludes nontrivial regular normal subgroups of the Sylow action. -/
public theorem no_regular_normal_of_pPrimeCore_eq_bot (hcore : pPrimeCore p G = ⊥) :
    ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
      ∀ Q S : Sylow p G, ∃! r : R, (r : G) • Q = S := by
  rintro ⟨R, hRn, hRne, hreg⟩
  let Q : Sylow p G := Classical.choice Sylow.nonempty
  have hbij : Function.Bijective (fun r : R => (r : G) • Q) := by
    constructor
    · intro x y hxy
      obtain ⟨r, _, hr⟩ := hreg Q ((x : G) • Q)
      exact (hr x rfl).trans (hr y hxy.symm).symm
    · intro S
      obtain ⟨r, hr, _⟩ := hreg Q S
      exact ⟨r, hr⟩
  have hcard : Nat.card R = Nat.card (Sylow p G) := Nat.card_congr (Equiv.ofBijective _ hbij)
  have hcop : Nat.Coprime p (Nat.card R) := by
    rw [hcard]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (not_dvd_card_sylow p G)
  have hle : R ≤ pPrimeCore p G := le_sSup ⟨hRn, hcop⟩
  exact hRne (eq_bot_iff.mpr (hcore ▸ hle))

/-- Transitivity of the chosen Sylow subgroup on the other Sylow subgroups,
together with centralizer containment, bounds nonidentity fixed sets by two. -/
public theorem at_most_two_fixed_of_centralizer_le_of_transitive (P : Sylow p G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (htrans : ∀ Q R : Sylow p G, Q ≠ P → R ≠ P →
      ∃ x : P, (x : G) • Q = R) :
    ∀ g : G, g ≠ 1 → ∀ Q R S : Sylow p G,
      Q ≠ R → Q ≠ S → R ≠ S →
        ¬ (g • Q = Q ∧ g • R = R ∧ g • S = S) := by
  have hbase (g : G) (R S : Sylow p G) (hR : R ≠ P) (hS : S ≠ P)
      (hRS : R ≠ S) (hgP : g • P = P) (hgR : g • R = R) (hgS : g • S = S) :
      g = 1 := by
    obtain ⟨u, hu⟩ := htrans R S hR hS
    have hune : (u : G) ≠ 1 := by
      intro h
      exact hRS (by simpa [h] using hu)
    have hnorm := Sylow.smul_eq_iff_mem_normalizer.mp hgP
    let v : P := ⟨g * (u : G) * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hnorm (u : G)).mp u.property⟩
    have hv : (v : G) • R = S := by
      change (g * (u : G) * g⁻¹) • R = S
      have hgi : g⁻¹ • R = R := by
        simpa only [inv_smul_smul] using congrArg (fun A : Sylow p G => g⁻¹ • A) hgR.symm
      rw [mul_smul, mul_smul, hgi, hu, hgS]
    have huv : u = v := inv_mul_eq_one.mp
      (P.eq_one_of_smul_eq_of_centralizer_le R hcent hR (u⁻¹ * v) (by
        change ((u : G)⁻¹ * (v : G)) • R = R
        rw [mul_smul, hv, ← hu, inv_smul_smul]))
    have hgu : g * (u : G) * g⁻¹ = (u : G) := (congrArg Subtype.val huv).symm
    have hgmem : g ∈ (P : Subgroup G) := hcent u u.property hune
      (Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgu))
    exact congrArg Subtype.val
      (P.eq_one_of_smul_eq_of_centralizer_le R hcent hR ⟨g, hgmem⟩ hgR)
  intro g hgne Q R S hQR hQS hRS ⟨hgQ, hgR, hgS⟩
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq G Q P
  have hR : t • R ≠ P := by
    rw [← ht]
    exact fun h => hQR (smul_left_cancel t h).symm
  have hS : t • S ≠ P := by
    rw [← ht]
    exact fun h => hQS (smul_left_cancel t h).symm
  have hRS' : t • R ≠ t • S := fun h => hRS (smul_left_cancel t h)
  have hfix (A : Sylow p G) (ha : g • A = A) :
      (t * g * t⁻¹) • (t • A) = t • A := by
    rw [mul_smul, mul_smul, inv_smul_smul, ha]
  have he : t * g * t⁻¹ = 1 := hbase (t * g * t⁻¹) (t • R) (t • S)
    hR hS hRS' (by rw [← ht]; exact hfix Q hgQ) (hfix R hgR) (hfix S hgS)
  apply hgne
  apply (MulAut.conj t).injective
  simpa using he

end Sylow
