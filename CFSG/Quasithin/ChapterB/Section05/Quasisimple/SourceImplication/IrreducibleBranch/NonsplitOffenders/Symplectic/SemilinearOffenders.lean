module
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Coefficients
public import Theory.Representation.SymplecticConjugatePair.Ambient.Semilinear

/-!
# The equality case for semilinear offenders

A field-linear map fixing all fixed vectors of a nontrivial semilinear
involution is the identity: a trace-one scalar expresses every vector as a
field-linear combination of two such fixed vectors. Consequently, if the
involution centralizers have two-rank at most half the binary dimension,
no offender has nontrivial coefficient action. The argument includes equality
in the rank estimate, needed over the field of four elements.

This is the linear reduction used by the natural-quotient route to
Aschbacher--Smith B.5.1, final irreducible paragraph, printed p.100.
The symplectic centralizer estimate is a separate input of its consumer.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open SymplecticConjugatePair.Ambient
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
open SemilinearCoefficients
variable {F G V : Type*} [Field F] [CharP F 2] [Group G]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V]

/-- The fixed vectors of a nontrivial semilinear involution span over the field. -/
theorem linear_eq_one_of_fixes_semilinear_fixedSpace
    (ρ : Representation (ZMod 2) G V) (s : G) (hs : s ^ 2 = 1)
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ c : F, ∀ v : V, ρ s (c • v) = σ c • ρ s v)
    (f : V →ₗ[F] V)
    (hf : ∀ v ∈ fixedSpace ρ (zpowers s), f v = v) : f = LinearMap.id := by
  obtain ⟨c, hc⟩ := exists_trace_one σ hσ hne
  have hfixed (v : V) : ρ s v - v ∈ fixedSpace ρ (zpowers s) := by
    rw [semilinear_involution_fixedSpace ρ s hs σ hσ hne hsemi]
    exact ⟨v, rfl⟩
  apply LinearMap.ext
  intro v
  have hv : σ c • (ρ s v - v) - (ρ s (c • v) - c • v) = v := by
    calc
      _ = (c - σ c) • v := by rw [smul_sub, hsemi, sub_smul]; abel
      _ = v := by rw [sub_eq_add_neg, CharTwo.neg_eq, add_comm c (σ c), hc, one_smul]
  calc
    f v = f (σ c • (ρ s v - v) - (ρ s (c • v) - c • v)) := congrArg f hv.symm
    _ = σ c • (ρ s v - v) - (ρ s (c • v) - c • v) := by
      rw [map_sub, map_smul, hf _ (hfixed v), hf _ (hfixed (c • v))]
    _ = v := hv

/-- The equality case of the half-dimension estimate also excludes offenders. -/
theorem offender_le_coefficient_kernel_of_centralizer_bound
    [Finite F] [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ)
    (π : G →* (F ≃+* F))
    (hsemi : ∀ g : G, ∀ (c : F) (v : V), ρ g (c • v) = π g c • ρ g v)
    {d : ℕ} (hd : 1 < d) (hdim : Module.finrank (ZMod 2) V = 2 * d)
    (hbound : ∀ s : G, orderOf s = 2 → π s ≠ 1 →
      primeRank 2 (centralizer ({s} : Set G)) ≤ d)
    {A : Subgroup G} (hA : IsOffender ρ A) : A ≤ π.ker := by
  by_contra hle
  obtain ⟨s, hsA, hsπ⟩ := SetLike.not_le_iff_exists.mp hle
  have hsne : s ≠ 1 := fun he => hsπ (he ▸ π.ker.one_mem)
  let := hA.1.2
  have hs2 : s ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian s hsA
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hsne
  have hσ := coefficient_involutive π hs2
  have hne : π s ≠ RingEquiv.refl F := hsπ
  have hc := semilinear_involution_twice_codim ρ s hs2 (π s) hσ hne (hsemi s)
  rw [hdim] at hc
  have hr := rank_le_of_centralizer hA.1 hsA (hbound s hso hsπ)
  have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers s) :=
    fun v hv a => hv ⟨a, (zpowers_le.mpr hsA) a.property⟩
  have hm := Submodule.finrank_mono hfix
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank ρ (zpowers s)
  have hoff := hA.2
  have heq : fixedSpace ρ A = fixedSpace ρ (zpowers s) :=
    Submodule.eq_of_le_of_finrank_eq hfix (by omega)
  have hker : A ⊓ π.ker = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    have hbπ : π b = 1 := hb.2
    let f : V →ₗ[F] V := {
      toFun := ρ b
      map_add' := (ρ b).map_add
      map_smul' := by
        intro c v
        change ρ b (c • v) = c • ρ b v
        simpa only [hbπ, RingAut.one_apply] using hsemi b c v }
    have hf : f = LinearMap.id := linear_eq_one_of_fixes_semilinear_fixedSpace
      ρ s hs2 (π s) hσ hne (hsemi s) f (by
        intro v hv
        exact (heq ▸ hv : v ∈ fixedSpace ρ A) ⟨b, hb.1⟩)
    apply hfaith
    rw [map_one]
    exact LinearMap.ext (fun v => LinearMap.congr_fun hf v)
  have hcard := kernel_relativeIndex_le_two π hA.1.2
  rw [hker, relIndex_bot_left, hA.1.card_eq_two_pow_rank] at hcard
  have hsmall : rank A ≤ 1 := by
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa using hcard)
  omega
end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
