module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ContainedNormalizer
public import CFSG.Quasithin.FermatMersenne
public import Theory.SpecificGroups.PSL2.PrimeSylowMaximal
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PCoreProduct

/-!
# The large-prime linear component in the original source

For a Fermat or Mersenne prime p>7, the concrete PSL2(p) Sylow two-subgroup
is maximal. The original 1.1.5 marking puts the component Sylow in the
proper intersection with M, identifying those two subgroups. No block
classification input is needed for this source 2.5.2(4) conclusion.

In the contained-normalizer branch, saturation places the intersection's
two-core inside D∩Q. That intersection is itself a two-group, while D∩Q lies
back in M. Thus D∩Q is already a Sylow subgroup of D. This allows removal
of the whole characteristic component subfamily, even when H permutes it.

Source: Aschbacher--Smith 2.5.2(4) and 2.5.3(4), printed pp.551--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

private theorem adjacent_two_power {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hbig : 7 < p) :
    ∃ k : ℕ, 4 ≤ k ∧ (p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) := by
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha2 : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    exact ⟨2 ^ a, Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha2,
      Or.inl (by omega)⟩
  · have ha4 : 4 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    exact ⟨a, ha4, Or.inr ha⟩

/-- The literal intersection in source 2.5.2(4), obtained directly from the
original marking and the maximality of the model's Sylow subgroup. -/
theorem linear_prime_intersection_of_source_marking
    {S : Sylow 2 H} {z : G} (h : Chapter1.Lemma115Hypotheses H S M z)
    (D : Subgroup H) (hD : IsComponent H D)
    (p : ℕ) [Fact p.Prime] (hp : IsFermatOrMersennePrime p) (hbig : 7 < p)
    (e : D ≃* PSL(2, ZMod p)) :
    ∃ P : Sylow 2 D, ((M.subgroupOf H).subgroupOf D) = (P : Subgroup D) ∧
      (P : Subgroup D) = (S : Subgroup H).subgroupOf D := by
  obtain ⟨hout, _α, _P, _ha, _d, _hc⟩ := h.component_inputs D hD
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  obtain ⟨k, hk, hpk⟩ := adjacent_two_power hp hbig
  have hmax : IsCoatom (P : Subgroup D) := by
    apply (OrderIso.isCoatom_iff e.mapSubgroup (P : Subgroup D)).mp
    change IsCoatom ((P : Subgroup D).map e.toMonoidHom)
    exact Matrix.ProjectiveSpecialLinearGroup.sylow_two_isCoatom_of_adjacent_power
      hk hpk (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  let I := (M.subgroupOf H).subgroupOf D
  have hPI : (P : Subgroup D) ≤ I := by
    rw [hP]
    intro x hx
    exact h.mem_HeOver.2.2 (mem_map_of_mem H.subtype hx)
  have hproper : I ≠ ⊤ := by
    intro he
    apply hout
    rintro x ⟨a, ha, rfl⟩
    exact (show (⟨a, ha⟩ : D) ∈ I from he ▸ mem_top _)
  exact ⟨P, (hmax.le_iff_eq hproper).mp hPI, hP⟩

/-- In the contained-normalizer branch, the actual saturated component
intersection is already a Sylow subgroup; no component normality is assumed. -/
theorem linear_prime_contained_source_sylow
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hpB : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (p : ℕ) [Fact p.Prime] (hp : IsFermatOrMersennePrime p) (hbig : 7 < p)
    (e : D ≃* PSL(2, ZMod p))
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = D ⊓ (twoCore HU).subgroupOf H := by
  obtain ⟨S, z, h, _hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hpB hBH hHnorm hpair hsat
  obtain ⟨P, hI, _hP⟩ := linear_prime_intersection_of_source_marking h D hD p hp hbig e
  let I := (M.subgroupOf H).subgroupOf D
  let Q := (twoCore HU).subgroupOf H
  let R := D ⊓ Q
  have hcore : I.pCoreIn 2 ≤ Q.subgroupOf D :=
    intersection_core_le_saturated_component_of_normalizer_le hpair hsat D hD hinside
  change I = (P : Subgroup D) at hI
  have hIp : IsPGroup 2 I := hI.symm ▸ P.isPGroup'
  rw [pCoreIn_eq_self_of_isPGroup 2 I hIp] at hcore
  have hRI : Q.subgroupOf D ≤ I := by
    intro d hd
    exact hinside (mem_map_of_mem H.subtype
      ⟨d.property, R.le_normalizer ⟨d.property, hd⟩⟩)
  have heq : (P : Subgroup D) = Q.subgroupOf D := hI.symm.trans (le_antisymm hcore hRI)
  refine ⟨P, ?_⟩
  rw [heq, subgroupOf_map_subtype, inf_comm]

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
