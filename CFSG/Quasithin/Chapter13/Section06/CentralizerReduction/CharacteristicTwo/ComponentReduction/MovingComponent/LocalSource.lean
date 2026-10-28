module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Exclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter.ModuleKernel

/-!
# The original local module inputs of the Suzuki contradiction

An element fixing the marked weight-two vector has sixth power one on the
actual five-point module. Cauchy's theorem therefore makes the full local
conjugation image a {2,3}-group. The original kernel O₂(L) and normalization
of L and V supply the mutual normalizer and two-core intersection bounds.
No Borel placement or module-action conclusion is assumed.

Source: Aschbacher--Smith, proof of 13.6.6, printed p.927.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
open A5Module SuzukiPair BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open SymplecticBorel.LocalInverter
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

private theorem fixed_vector_six : ∀ g : Equiv.Perm (Fin 5),
    coreRepresentation (Fin 5) g v = v → g ^ 6 = 1 := by decide +kernel

theorem source_local_action_pi (s : A5Module.Marking L V)
    (ρ : normalizer (V : Set G) →* Equiv.Perm (Fin 5))
    (he : ∀ (g : normalizer (V : Set G)) (w : Space),
      MulAut.conj (g : G) (s.map (Multiplicative.ofAdd w)) =
        s.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (ρ g) w))) :
    IsPiGroup twoThreePrimes (localAction V (markedV s)).range := by
  have hsix (g : localNormalizer V (markedV s)) :
      localAction V (markedV s) g ^ 6 = 1 := by
    let a : normalizer (V : Set G) := inclusion inf_le_left g
    have hv : coreRepresentation (Fin 5) (ρ a) v = v := by
      apply Multiplicative.ofAdd.injective
      apply s.injective
      rw [← he]
      change (g : G) * markedV s * (g : G)⁻¹ = markedV s
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property.2)
    have ha := fixed_vector_six (ρ a) hv
    rw [← map_pow]
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    obtain ⟨u, hu⟩ := s.range_eq.ge w.property
    have hh := he (a ^ 6) u.toAdd
    rw [map_pow, ha, map_one] at hh
    change (g : G) ^ 6 * s.map u * ((g : G) ^ 6)⁻¹ = s.map u at hh
    change (g : G) ^ 6 * (w : G) * ((g : G) ^ 6)⁻¹ = (w : G)
    simpa only [hu] using hh
  rw [IsPiGroup_iff]
  intro p hp
  let : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p.val hp
  have hh : x ^ 6 = 1 := by
    apply Subtype.ext
    obtain ⟨g, hg⟩ := x.property
    change (x.val) ^ 6 = 1
    rw [← hg]
    exact hsix g
  have hd : p.val ∣ 2 * 3 := hx ▸ orderOf_dvd_of_pow_eq_one hh
  exact (p.property.dvd_mul.mp hd).imp
    (fun h => (Nat.prime_two.eq_one_or_self_of_dvd p.val h).resolve_left p.property.ne_one)
    (fun h => (Nat.prime_three.eq_one_or_self_of_dvd p.val h).resolve_left p.property.ne_one)

omit [Finite G] in
theorem source_local_centralizer_laws (s : A5Module.Marking L V)
    (hk : s.action.ker = pCore 2 L) :
    Lv L (markedV s) ≤ normalizer
      (normalizer (L : Set G) ⊓ centralizer (V : Set G) : Set G) ∧
    normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤
      normalizer (Lv L (markedV s) : Set G) ∧
    Lv L (markedV s) ⊓ (normalizer (L : Set G) ⊓ centralizer (V : Set G)) ≤
      (Lv L (markedV s)).pCoreIn 2 := by
  have hDL : Lv L (markedV s) ≤ L := (map_subtype_le _).trans inf_le_left
  have hvV : markedV s ∈ V := s.range_eq.le ⟨_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (le_inf (hDL.trans L.le_normalizer |>.trans (normalizer (L : Set G)).le_normalizer)
      (hDL.trans (marking_normalizes s) |>.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf
  · intro g hg
    apply normalizer_le_normalizer_characteristic_image _ (pResidual 2 _)
    apply inf_normalizer_le_normalizer_inf
    refine ⟨hg.1, (Gv (markedV s)).le_normalizer ?_⟩
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg.2 _ hvV).symm
  · intro g hg
    exact pCoreIn_inf_le_of_normalizes (hDL.trans L.le_normalizer)
      ⟨marking_centralizer_le_core s hk ⟨hDL hg.1, hg.2.2⟩, hg.1⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
