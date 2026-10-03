module
public import Stellmacher.SectionFiveToSeven.Result5_2
public import Stellmacher.CharacteristicTwoNormal


/-!
# Applying (5.2) inside a two-subgroup centralizer

Assume Hypothesis Two and the branch where `P₂` centralizes the central
involutions of `S`. Let `K ≤ P₂` satisfy `K = [K,B(S)]`. If a nontrivial
two-subgroup `R` is centralized by both `B(S)` and `K`, then `C_H(R)` has
characteristic two and `K` is subnormal in `C_H(R)`.

The normalizer `N_H(R)` is a genuine two-local subgroup containing `B(S)`;
Hypothesis Two therefore makes it solvable of characteristic two. Its
normal subgroup `C_H(R)` inherits characteristic two, and the canonical
subgroup equivalence gives this property for the literal ambient
centralizer. The central alternative of (5.1) identifies `S` with the
ambient Sylow and supplies the P-star membership needed by (5.2).
Applying (5.2) in `N_H(R)` proves subnormality of `K` there. Pulling back
along the centralizer inclusion proves the requested subnormality.

This is the centralizer transfer used in the `R₁` branch of Stellmacher
(9.3), Journal of Algebra 190 (1997), p.49. The proof uses the normalizer
as the two-local overgroup and retains the given centralizer as the final
ambient group.
-/

namespace Stellmacher.SectionsFiveToSeven

/-- The central branch of (5.1) and (5.2) give characteristic two and
subnormality inside a supplied nontrivial two-subgroup centralizer. -/
public theorem fiveTwo_centralizer_subnormal_characteristicTwo
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (K : Subgroup H) (hKP : K ≤ P2) (hKB : K = ⁅K, baumannIn S⁆)
    (R : Subgroup H) (hRne : R ≠ ⊥) (hRtwo : IsPGroup 2 R)
    (hBC : baumannIn S ⊔ K ≤ Subgroup.centralizer (R : Set H)) :
    IsCharacteristicTwoType (Subgroup.centralizer (R : Set H)) ∧
      SubnormalIn K (Subgroup.centralizer (R : Set H)) := by
  let C := Subgroup.centralizer (R : Set H)
  let N := Subgroup.normalizer (R : Set H)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hNlocal : IsTwoLocal N := ⟨R, hRne, hRtwo, rfl⟩
  have hBN : baumannIn S ⊔ K ≤ N := hBC.trans hCN
  obtain ⟨hNsolv, hNchar⟩ := h.local_B N hNlocal (le_sup_left.trans hBN)
  have hCchar : IsCharacteristicTwoType C := by
    have hchar := characteristicTwo_normal_subgroup hNsolv hNchar (C.subgroupOf N)
    let e : C.subgroupOf N ≃* C := Subgroup.subgroupOfEquivOfLe hCN
    have hcore := pCore_map_iso 2 e
    intro c hc
    obtain ⟨a, rfl⟩ := e.surjective c
    rw [← hcore]
    apply Subgroup.mem_map_of_mem
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    apply e.injective
    have hbC : e b ∈ pCore 2 C := by
      rw [← hcore]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hb
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hc (e b) hbC
  have hZP : omegaOneCenter S ≤ P2 :=
    (Subgroup.map_subtype_le _).trans h.fiveOne.P2_mem.1.2.1.1
  have hZn : NormalIn (omegaOneCenter S) P2 := by
    refine ⟨hZP, (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr ?_⟩
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcase : S = (S0 : Subgroup H) ∧ P2 ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter S : Set H)) S := by
    cases h.fiveOne.alternative with
    | a _ _ hn => exact (hn hZn).elim
    | b hS hstar => exact ⟨hS, hstar⟩
    | c _ _ _ _ hn _ _ _ _ _ _ _ _ => exact (hn hZn).elim
  obtain ⟨rfl, hstar⟩ := hcase
  have hsub := lemma_five_two S0 (omegaOneCenter (S0 : Subgroup H))
    (baumannIn (S0 : Subgroup H))
    (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup H) : Set H))
    P2 K rfl rfl rfl hstar hKP h.local_B hKB N hNlocal hBN
  refine ⟨hCchar, le_sup_right.trans hBC, ?_⟩
  exact hsub.2.comap (Subgroup.inclusion hCN)

end Stellmacher.SectionsFiveToSeven
