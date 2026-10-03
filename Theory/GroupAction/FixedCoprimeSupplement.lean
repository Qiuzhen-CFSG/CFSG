module

public import Theory.GroupAction.InvariantCommonSylow
public import Theory.GroupTheory.SylowNormalCoprimeSupplement

/-!
# Fixed conjugation into a coprime normal supplement

Let a finite two-group A act on an odd finite solvable group K. If a
normal q′-subgroup N supplements an invariant subgroup H, every invariant
q-subgroup W of K lies in a conjugate of H by an A-fixed element. The
normal subgroup N need not itself be invariant, and W may be trivial.

Choose an invariant Sylow q-subgroup of H. Its ambient image is Sylow
in K because adjoining a normal q′-subgroup preserves the Sylow image.
The invariant common-Sylow conjugacy theorem puts a fixed conjugate of W
in that Sylow subgroup. Inverting the fixed conjugator yields W contained
in a conjugate of H. Every native subgroup action uses the supplied
ambient action and its exact invariance instance.

This is the coprime conjugation step used in Kurzweil–Stellmacher,
*The Theory of Finite Groups*, 11.2.6 (printed p. 321). It is independent
of signalizer families and uses only the general Theory action APIs.
-/

open scoped Pointwise

/-- An invariant prime subgroup lies in a fixed conjugate of an invariant
subgroup supplemented by a normal subgroup of coprime order. -/
public theorem exists_fixedPoint_conj_le_of_coprime_normal_supplement
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    [MulDistribMulAction A K] (hA : IsPGroup 2 A)
    (hKodd : Odd (Nat.card K)) (hKsolv : Group.IsSolvable K)
    {q : ℕ} [Fact q.Prime] (N H W : Subgroup K) [N.Normal]
    (hN : Nat.Coprime q (Nat.card N)) (hsup : N ⊔ H = ⊤)
    (hHI : IsInvariant A K H) (hW : IsPGroup q W) (hWI : IsInvariant A K W) :
    ∃ c : K, c ∈ fixedPointSubgroup A K ∧ W ≤ H.map (MulAut.conj c) := by
  let _ : IsInvariant A K H := hHI
  have hHodd : Odd (Nat.card H) := hKodd.of_dvd_nat H.card_subgroup_dvd_card
  have hbotI : IsInvariant A H (⊥ : Subgroup H) := by
    refine ⟨fun a x => ?_⟩
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      exact smul_one a
    · intro h
      have hh := congrArg (fun y : H => a⁻¹ • y) h
      simpa only [inv_smul_smul, smul_one] using hh
  obtain ⟨S, _, hSI⟩ := exists_invariant_sylow_le_of_isPGroup (p := q) hA hHodd
    (⊥ : Subgroup H) IsPGroup.of_bot hbotI
  have hNnot : ¬ q ∣ Nat.card N := (Fact.out : q.Prime).coprime_iff_not_dvd.mp hN
  obtain ⟨T, hT⟩ := S.exists_map_eq_map_of_normal_coprime_sup N H hNnot
  have hsurj : Function.Surjective (N ⊔ H : Subgroup K).subtype := by
    intro x
    exact ⟨⟨x, by rw [hsup]; trivial⟩, rfl⟩
  let T₀ : Sylow q K := T.mapSurjective (f := (N ⊔ H : Subgroup K).subtype) hsurj
  have hT₀ : (T₀ : Subgroup K) = (S : Subgroup H).map H.subtype := hT
  let _ : IsInvariant A H (S : Subgroup H) := hSI
  have hT₀I : IsInvariant A K (T₀ : Subgroup K) := by
    rw [hT₀]
    exact isInvariant_map_subtype H (S : Subgroup H)
  obtain ⟨c, hc, E, hE, _, hWE, hTE⟩ :=
    exists_fixedPoint_conj_le_common_invariant_pSubgroup hA hKodd hKsolv
      W (T₀ : Subgroup K) hW T₀.isPGroup' hWI hT₀I
  have hEH : E ≤ H := by
    have hET : E = (T₀ : Subgroup K) := T₀.is_maximal' hE hTE
    rw [hET, hT₀]
    exact Subgroup.map_subtype_le _
  refine ⟨c⁻¹, (fixedPointSubgroup A K).inv_mem hc, ?_⟩
  have hle := Subgroup.map_mono (f := (MulAut.conj c⁻¹ : K →* K)) (hWE.trans hEH)
  have hcomp : (MulAut.conj c⁻¹ : K →* K).comp (MulAut.conj c : K →* K) =
      MonoidHom.id K := by
    ext x
    change c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x
    group
  simpa only [Subgroup.map_map, hcomp, Subgroup.map_id] using hle
