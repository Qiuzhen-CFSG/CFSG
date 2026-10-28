module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.PrimeReduction

/-!
# Odd normal images outside the distinguished maximal subgroup

A p-subgroup whose image in H/O₂(H) is normal lies in the Fitting preimage.
For odd p, its two-residual is itself. Thus the 13.8.12 trichotomy would put
such a subgroup inside L₁ if it lay in M. The local two-core centralizes
its normal odd image, contradicting movement by Vα*. Minimality in the
actual Hz family then gives H = ⟨P,L₁,T⟩.

All quotient maps and relative normalizers are retained. In particular the
odd subgroup embeds in H/O₂(H); no assertion of ambient normality of P is
made. Existence of P and Frattini irreducibility remain separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed pp.950–951.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three
open Subgroup
variable {G : Type*} [Group G]

/-- Subgroup containment passes to the actual star images. -/
theorem starImage_mono (H : Subgroup G) {A B : Subgroup G} (h : A ≤ B) :
    Source.starImage H A ≤ Source.starImage H B :=
  map_mono (subgroupOf_mono H h)

/-- The actual star image of a p-group remains a p-group. -/
theorem starImage_isPGroup {p : ℕ} (H P : Subgroup G) (hp : IsPGroup p P) :
    IsPGroup p (Source.starImage H P) := hp.comap_subtype.map _

/-- The quotient by O₂(H) is injective on an odd subgroup of H. -/
noncomputable def oddStarEquiv {p : ℕ} {H P : Subgroup G}
    (hp : IsPGroup p P) (ho : Odd p) (hPH : P ≤ H) :
    P ≃* Source.starImage H P := by
  let R := P.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hd : Disjoint (pCore 2 H) R :=
    pCore_isPGroup.disjoint_of_coprime hp.comap_subtype (Nat.coprime_two_left.mpr ho)
  have hi : Function.Injective (q.subgroupMap R) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hc : (a : H) ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val ha)
    exact Subtype.ext (hd.le_bot ⟨hc, a.property⟩)
  exact (subgroupOfEquivOfLe hPH).symm.trans
    (MulEquiv.ofBijective (q.subgroupMap R) ⟨hi, q.subgroupMap_surjective R⟩)

/-- Local normalization passes to the quotient images, with no ambient normality. -/
theorem starImage_normalizes (H : Subgroup G) {A B : Subgroup G}
    (hn : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply le_normalizer_iff.mpr
  intro a ha b hb
  change a ∈ (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) at ha
  change b ∈ (B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) at hb
  obtain ⟨a, haA, rfl⟩ := mem_map.mp ha
  obtain ⟨b, hbB, rfl⟩ := mem_map.mp hb
  refine mem_map.mpr ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact le_normalizer_iff.mp hn a haA b hbB

/-- The embedded core is normal in its defining overgroup. -/
theorem le_normalizer_pCoreIn (p : ℕ) (K : Subgroup G) :
    K ≤ normalizer (K.pCoreIn p : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer (pCoreIn_le p K)).mp
  have he : (K.pCoreIn p).subgroupOf K = pCore p K :=
    comap_map_eq_self_of_injective K.subtype_injective _
  rw [he]
  infer_instance

/-- Normal p-images lie in the ordinary Fitting subgroup, hence in its preimage. -/
theorem normal_starImage_le_twoFitting [Finite G] {p : ℕ} [Fact p.Prime]
    {H P : Subgroup G} (hPH : P ≤ H) (hp : IsPGroup p P)
    (hn : (Source.starImage H P).Normal) : P ≤ twoFitting H := by
  have hfit : Source.starImage H P ≤ fittingSubgroup (Source.Hstar H) :=
    le_sSup ⟨hn, (starImage_isPGroup H P hp).isNilpotent⟩
  intro x hx
  refine mem_map.mpr ⟨⟨x, hPH hx⟩, ?_, rfl⟩
  exact hfit (mem_map.mpr ⟨⟨x, hPH hx⟩, hx, rfl⟩)

/-- An odd p-subgroup has no nontrivial two-group quotient. -/
theorem odd_twoResidual_eq {p : ℕ} {P : Subgroup G}
    (hp : IsPGroup p P) (ho : Odd p) : twoResidual P = P := by
  apply le_antisymm (twoResidual_le P)
  intro x hx
  refine mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
  exact mem_pResidual_of_orderOf_coprime
    (hp.orderOf_coprime (Nat.coprime_two_right.mpr ho) ⟨x, hx⟩).symm

/-- An odd subgroup with normal star image, if in M, lies in the source residual. -/
theorem normal_odd_le_residualInM [Finite G] {p : ℕ} [Fact p.Prime]
    {H P M : Subgroup G} (hPH : P ≤ H) (hp : IsPGroup p P) (ho : Odd p)
    (hn : (Source.starImage H P).Normal) (hPM : P ≤ M) :
    P ≤ residualInM H M := by
  have hPF := normal_starImage_le_twoFitting hPH hp hn
  have hh := twoResidual_mono (le_inf hPF hPM)
  rw [odd_twoResidual_eq hp ho] at hh
  exact hh

/-- A local two-core centralizes a normal odd star image contained in the
corresponding local group K*. Only P* is assumed normal in H*. -/
theorem normal_odd_starImage_commutator_eq_bot {p : ℕ}
    {H P K A : Subgroup G} (hp : IsPGroup p P) (ho : Odd p)
    (hn : (Source.starImage H P).Normal) (hPK : P ≤ K)
    (hA : A ≤ K.pCoreIn 2) :
    ⁅Source.starImage H P, Source.starImage H A⁆ = ⊥ := by
  let := hn
  have hnorm := starImage_normalizes H (le_normalizer_pCoreIn 2 K)
  have hcomm : ⁅Source.starImage H P, Source.starImage H A⁆ ≤
      Source.starImage H (K.pCoreIn 2) :=
    (commutator_mono (starImage_mono H hPK) (starImage_mono H hA)).trans
      (le_normalizer_iff_commutator_le_right.mp hnorm)
  have hd := (starImage_isPGroup H P hp).disjoint_of_coprime
    (starImage_isPGroup H (K.pCoreIn 2) (isPGroup_pCoreIn 2 K))
    (Nat.coprime_two_right.mpr ho)
  exact le_bot_iff.mp ((le_inf (commutator_le_left _ _) hcomm).trans hd.le_bot)

/-- All three residual alternatives give containment in L₁, retaining L₁,+ ≤ L₁. -/
theorem residualAlternative_le {L L₁ L₁plus X : Subgroup G}
    (hX : ResidualAlternative L L₁ L₁plus X) (hplus : L₁plus ≤ L₁) : X ≤ L₁ := by
  rcases hX with h | ⟨_, h⟩ | ⟨_, h⟩
  · exact h ▸ bot_le
  · exact h ▸ le_rfl
  · exact h ▸ hplus

/-- The nontrivial Vα* action rules out P ≤ M by the exact residual trichotomy. -/
theorem normal_odd_outside [Finite G] {p : ℕ} [Fact p.Prime]
    {H P L L₁ L₁plus T M Vα : Subgroup G}
    (hPH : P ≤ H) (hp : IsPGroup p P) (ho : Odd p)
    (hn : (Source.starImage H P).Normal)
    (hmoved : ⁅Source.starImage H P, Source.starImage H Vα⁆ ≠ ⊥)
    (hVα : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (hres : ResidualAlternative L L₁ L₁plus (residualInM H M))
    (hplus : L₁plus ≤ L₁) : ¬ P ≤ M := by
  intro hPM
  have hPL₁ := (normal_odd_le_residualInM hPH hp ho hn hPM).trans
    (residualAlternative_le hres hplus)
  exact hmoved (normal_odd_starImage_commutator_eq_bot hp ho hn
    (hPL₁.trans le_sup_left) hVα)

/-- The outside subgroup generates the minimal Hz member together with L₁T. -/
theorem normal_odd_generated [Finite G] {p : ℕ} [Fact p.Prime]
    {H P Z L L₁ L₁plus T G₁ M Vα : Subgroup G}
    (hZ : Z ≠ ⊥) (hpZ : IsPGroup 2 Z) (hZLT : Z ≤ L₁ ⊔ T)
    (hGZ : G₁ ≤ normalizer (Z : Set G))
    (hH : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hPH : P ≤ H) (hp : IsPGroup p P) (ho : Odd p)
    (hn : (Source.starImage H P).Normal)
    (hmoved : ⁅Source.starImage H P, Source.starImage H Vα⁆ ≠ ⊥)
    (hVα : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (hres : ResidualAlternative L L₁ L₁plus (residualInM H M))
    (hplus : L₁plus ≤ L₁) : H = P ⊔ (L₁ ⊔ T) :=
  minimal_Hz_eq_generated hZ hpZ hZLT hGZ hH hPH
    (normal_odd_outside hPH hp ho hn hmoved hVα hres hplus)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three

end
