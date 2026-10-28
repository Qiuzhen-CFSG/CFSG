module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement

/-!
# Three-cycle control of the normalizer of an A₅ in A₇

A Sylow-normalized A₅ fixes exactly two letters. A three-cycle outside
that A₅ moves the marked pair. A subgroup preserving the pair and normalized
by the cycle must preserve each of its three rotated pairs, so it fixes the
support of the cycle pointwise. Consequently the cycle centralizes it.

The small permutation calculation below checks membership in the three
rotated pairs; all conjugation and subgroup transport is structural.
Source: Aschbacher–Smith 5.1.13, printed p.638, refs/quasithin.pdf,
the chief-factor exclusion of the right block.
-/

public noncomputable section
open Subgroup Equiv
namespace Theory.SpecificGroups.Alternating.SevenFiveCubicControl
private def t : Perm (Fin 7) := swap 0 1 * swap 1 2
private theorem t_three : t.IsThreeCycle := by
  rw [Perm.IsThreeCycle]
  decide

private theorem signatures (i j z w : Fin 7) (hij : i ≠ j)
    (ht : t i ≠ i ∨ t j ≠ j) (hz : z.val < 3)
    (hs : ∀ k : Fin 3, ((t^k.val) z = i ∨ (t^k.val) z = j) ↔
      ((t^k.val) w = i ∨ (t^k.val) w = j)) : z = w := by
  revert i j z w
  decide +kernel

private theorem standard_commutes (g : Perm (Fin 7)) (i j : Fin 7) (hij : i ≠ j)
    (ht : t i ≠ i ∨ t j ≠ j)
    (hs : ∀ k : Fin 3, ∀ z, (t^k.val * g * (t^k.val)⁻¹) z ∈ ({i,j} : Set (Fin 7)) ↔
      z ∈ ({i,j} : Set (Fin 7))) : Commute g t := by
  have hf (z : Fin 7) (hz : z.val < 3) : g z = z := by
    apply (signatures i j z (g z) hij ht hz ?_).symm
    intro k
    have hh := hs k ((t^k.val) z)
    simpa only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hh.symm
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  have h2 := hf 2 (by decide)
  change g * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * g
  rw [←mul_assoc, mul_swap_eq_swap_mul g 0 1, h0,h1,mul_assoc,
    mul_swap_eq_swap_mul g 1 2,h1,h2,←mul_assoc]

/-- A three-cycle moving the marked pair centralizes a subgroup of its
setwise stabilizer that it normalizes. -/
theorem pair_threeCycle_centralizes (a : Perm (Fin 7)) (ha : a.IsThreeCycle)
    (R : Subgroup (Perm (Fin 7))) (hn : a ∈ normalizer (R : Set _))
    (i j : Fin 7) (hij : i ≠ j) (hm : a i ≠ i ∨ a j ≠ j)
    (hR : ∀ g ∈ R, ∀ z, g z ∈ ({i,j} : Set (Fin 7)) ↔ z ∈ ({i,j} : Set (Fin 7))) :
    a ∈ centralizer (R : Set _) := by
  obtain ⟨s,hs⟩ := isConj_iff.mp (Perm.isConj_of_cycleType_eq (t_three.cycleType.trans ha.cycleType.symm))
  have has : a = s*t*s⁻¹ := hs.symm
  intro g hg
  have ht : t (s⁻¹ i) ≠ s⁻¹ i ∨ t (s⁻¹ j) ≠ s⁻¹ j := by
    by_contra! hc
    have hi : a i = i := by
      rw [has]
      change s (t (s⁻¹ i)) = i
      rw [hc.1]
      exact s.apply_symm_apply i
    have hj : a j = j := by
      rw [has]
      change s (t (s⁻¹ j)) = j
      rw [hc.2]
      exact s.apply_symm_apply j
    exact hm.elim (fun h => h hi) (fun h => h hj)
  have hc := standard_commutes (s⁻¹*g*s) (s⁻¹ i) (s⁻¹ j) ((s⁻¹).injective.ne hij) ht
  have hc' : Commute (s⁻¹*g*s) t := hc (by
    intro k z
    have hgk : a^k.val * g * (a^k.val)⁻¹ ∈ R :=
      le_normalizer_iff.mp le_rfl _ ((normalizer (R : Set (Perm (Fin 7)))).pow_mem hn k.val) g hg
    have hh := hR _ hgk (s z)
    have he : a^k.val = s*t^k.val*s⁻¹ := by rw [has,conj_pow]
    rw [he] at hh
    have hx : (s*t^k.val*s⁻¹ * g * (s*t^k.val*s⁻¹)⁻¹) (s z) =
        s ((t^k.val * (s⁻¹*g*s) * (t^k.val)⁻¹) z) := by
      have heq : (s*t^k.val*s⁻¹ * g * (s*t^k.val*s⁻¹)⁻¹)*s =
          s*(t^k.val * (s⁻¹*g*s) * (t^k.val)⁻¹) := by group
      exact congrArg (fun p : Perm (Fin 7) => p z) heq
    rw [hx] at hh
    simp only [Perm.inv_def,Set.mem_insert_iff,Set.mem_singleton_iff,←Equiv.eq_symm_apply] at hh ⊢
    exact hh)
  rw [has]
  calc
    g * (s*t*s⁻¹) = s*((s⁻¹*g*s)*t)*s⁻¹ := by group
    _ = s*(t*(s⁻¹*g*s))*s⁻¹ := by rw [hc'.eq]
    _ = (s*t*s⁻¹)*g := by group

open MulAction
local notation "A7" => alternatingGroup (Fin 7)
/-- The three-cycle outside the placed A5 centralizes each normalized subgroup
of its normalizer. -/
theorem five_threeCycle_centralizes (B : Subgroup A7)
    (e : B ≃* alternatingGroup (Fin 5)) (P : Sylow 2 A7)
    (hPB : (P : Subgroup A7) ≤ normalizer (B : Set A7))
    (a : A7) (ha : a.val.IsThreeCycle) (hout : a ∉ B)
    (R : Subgroup A7) (hRB : R ≤ normalizer (B : Set A7))
    (hn : a ∈ normalizer (R : Set A7)) : a ∈ centralizer (R : Set A7) := by
  classical
  obtain ⟨i,j,hij,hB⟩ := Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B e P hPB
  have hfixed : fixedPoints B (Fin 7) = {i,j} := by
    apply (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · intro x hx b
      exact (hB ▸ b.property : b.val ∈ fixingSubgroup A7 ({i,j} : Set (Fin 7))) ⟨x,hx⟩
    · rw [Theory.SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two B e P hPB,
        Set.ncard_pair hij]
  have hm : a.val i ≠ i ∨ a.val j ≠ j := by
    by_contra! hh
    apply hout
    rw [hB]
    rintro ⟨x,hx⟩
    rcases hx with rfl | ⟨rfl⟩
    · exact hh.1
    · exact hh.2
  have hstab : ∀ g ∈ normalizer (B : Set A7), ∀ z,
      g.val z ∈ ({i,j} : Set (Fin 7)) ↔ z ∈ ({i,j} : Set (Fin 7)) := by
    have he (g : A7) (hg : g ∈ normalizer (B : Set A7)) (z : Fin 7)
        (hz : z ∈ fixedPoints B (Fin 7)) : g.val z ∈ fixedPoints B (Fin 7) := by
      intro b
      have hb := (mem_normalizer_iff''.mp hg b.val).mp b.property
      have hh := hz ⟨g⁻¹*b.val*g,hb⟩
      change (g.val⁻¹*b.val.val*g.val) z = z at hh
      have hh' := congrArg g.val hh
      change b.val.val (g.val z) = g.val z
      simpa only [Perm.mul_apply,Perm.inv_def,Equiv.apply_symm_apply] using hh'
    intro g hg z
    rw [←hfixed]
    constructor
    · intro hz
      simpa using he g⁻¹ ((normalizer (B : Set A7)).inv_mem hg) (g.val z) hz
    · exact he g hg z
  have hh := pair_threeCycle_centralizes a.val ha (R.map (alternatingGroup (Fin 7)).subtype)
    (R.le_normalizer_map (alternatingGroup (Fin 7)).subtype (mem_map_of_mem (alternatingGroup (Fin 7)).subtype hn)) i j hij hm (by
      rintro _ ⟨g,hg,rfl⟩ z
      exact hstab g (hRB hg) z)
  intro r hr
  exact Subtype.ext (hh r.val (mem_map_of_mem (alternatingGroup (Fin 7)).subtype hr))

end Theory.SpecificGroups.Alternating.SevenFiveCubicControl
