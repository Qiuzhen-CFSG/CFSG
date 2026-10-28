module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Schur
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Rank
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Contracts
public import Theory.SpecificGroups.Suzuki.TwoRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryRankOne
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.Representation.Quotient

/-!
# Reducing large tensor factors in G.9.3

For a factor of dimension at least four, the tensor degree and the actor
rank estimate imply `n ≤ r` directly. A maximal elementary subgroup of
`L` therefore gives the smaller constituent a genuine G.9.1 setup. The
proved binary SL₂ highest-weight classification, applied to its actual
commutant field, leaves only the degree-four orthogonal possibility; the
original tensor degree excludes that possibility.

These reductions preserve the original actor and its rank. They do not
assert the automorphism-rank estimate or narrow the A.1.34 quotient list.
Those group-theoretic inputs remain separate obligations. No induction
hypothesis at the original degree is used.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356.
-/

public noncomputable section

open scoped MatrixGroups MonoidAlgebra

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

universe u v

variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}

namespace TensorData

/-- The required splitting-field inequality follows already from the tensor
bound in this branch; no existence of a splitting field is assumed. -/
theorem field_degree_le_rank_of_large (T : TensorData ρ L L₂) {r m : ℕ}
    (hk : 4 ≤ T.k) (hm : m ≤ 2 * r)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) : T.n ≤ r := by
  have hs : 16 ≤ T.k ^ 2 := by nlinarith
  have ht := Nat.mul_le_mul_left T.n hs
  rw [← T.degree_eq] at ht
  omega

/-- A maximal elementary actor inside the component supplies the precise
smaller-degree setup, while the original actor is retained in `hm` and `hd`. -/
theorem exists_maximal_factor_setup [Finite G] (T : TensorData ρ L L₂) {m : ℕ}
    (hk : 4 ≤ T.k) (hm : m ≤ 2 * primeRank 2 L)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) :
    ∃ B : Subgroup L, Setup (Representation.restrictScalars T.left) B (primeRank 2 L) ∧
      Module.finrank (ZMod 2) T.I < Module.finrank (ZMod 2) V := by
  obtain ⟨B, hB, hc⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := 2)
  exact ⟨B, T.factor_setup_and_degree_lt B hB hc hm
    (T.field_degree_le_rank_of_large hk hm hd) (by omega) hd⟩

/-- In the binary SL₂ family the actual Schur-field classification excludes
a large tensor factor. The field order is indexed by the component's rank;
the original actor and small-degree bound have not been replaced. -/
theorem exclude_large_binary_factor [Finite G] (T : TensorData ρ L L₂) {m : ℕ}
    (hL : Theory.GroupTheory.IsComponent G L)
    (hm : m ≤ 2 * primeRank 2 L)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : L ≃* SL(2,F)) (hF : Nat.card F = 2 ^ primeRank 2 L)
    (hk : 4 ≤ T.k) : False := by
  have hr := (T.large_factor_rank hk hm hd).2
  obtain ⟨B, hB, _⟩ := T.exists_maximal_factor_setup hk hm hd
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  let σ : Representation (ZMod 2) SL(2,F) T.I := τ.comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective τ).mpr T.left_irreducible
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ Subgroup.center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  have hnontrivial : ∃ g, σ g ≠ 1 := by
    obtain ⟨l, hl⟩ := exists_ne (1 : L)
    refine ⟨e l, ?_⟩
    intro he
    apply hl
    apply T.left_faithful
    ext x
    have hx := congrArg (fun f : Module.End (ZMod 2) T.I => f x) he
    simpa [σ, τ, Representation.restrictScalars] using hx
  have hs := T.left_schur_degree_comp e.symm
  change Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] σ.asModule) = T.n at hs
  have hpos := T.n_pos
  have hdegree := T.factor_degree_eq
  rcases DefiningCharacteristic.binary_small_degree_schur_alternatives σ hnontrivial
      (primeRank 2 L) (by omega) hF hB.degree_le with h | h | h
  · rw [hs] at h
    nlinarith [h.1, h.2]
  · rw [hs] at h
    have hk4 : T.k = 4 := by nlinarith [h.1, h.2]
    exact T.exclude_orthogonal_factor hm h.1.symm hk4 hd
  · omega

/-- Suzuki's genuine degree theorem rules out the other large-rank model
on the actual smaller constituent. The degree theorem remains an input. -/
theorem exclude_large_suzuki_factor [Finite G] (T : TensorData ρ L L₂) {m s : ℕ}
    (hsz : FactorReduction.SuzukiBinaryDegreeTheorem.{v})
    (hm : m ≤ 2 * primeRank 2 L)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1))
    (hs : 0 < s) (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s)
    (hk : 4 ≤ T.k) : False := by
  have hr := (T.large_factor_rank hk hm hd).2
  obtain ⟨B, hB, _⟩ := T.exists_maximal_factor_setup hk hm hd
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  let σ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s) T.I :=
    τ.comp e.symm.toMonoidHom
  have hi : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective τ).mpr T.left_irreducible
  have hf : Function.Injective σ := by
    intro a b hab
    apply e.symm.injective
    apply T.left_faithful
    ext x
    exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) hab
  have hlower := hsz s hs σ hi hf
  have hrank : primeRank 2 L = 2 * s + 1 :=
    (Theory.GroupTheory.primeRank_equiv 2 e).trans
      (BenderSuzuki.MatrixGroups.suzuki_two_rank s hs)
  have hupper := hB.degree_le
  omega

/-- Once the source model restrictions and the original actor's bound have
been proved, both large-factor models are excluded. No tensor factor
alternative or degree-induction hypothesis is assumed. -/
theorem factor_dimension_two_or_three_of_large_models [Finite G]
    (T : TensorData ρ L L₂) {m : ℕ}
    (hsz : FactorReduction.SuzukiBinaryDegreeTheorem.{v})
    (hL : Theory.GroupTheory.IsComponent G L)
    (hm : m ≤ 2 * primeRank 2 L)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1))
    (hmodels : 4 ≤ primeRank 2 L → FactorReduction.LargeRankModel L) :
    T.k = 2 ∨ T.k = 3 := by
  have hk := T.two_le_factor_dimension hL
  by_contra hsmall
  have hlarge : 4 ≤ T.k := by omega
  rcases hmodels (T.large_factor_rank hlarge hm hd).2 with hlinear | hsuzuki
  · obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := hlinear
    exact T.exclude_large_binary_factor hL hm hd e hF hlarge
  · obtain ⟨s, hs, ⟨e⟩⟩ := hsuzuki
    exact T.exclude_large_suzuki_factor hsz hm hd hs e hlarge

end TensorData

variable [Finite G] [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {A H : Subgroup G} {m : ℕ}

/-- Assembly of the factor reduction conditional on the two remaining
group-theoretic results and Suzuki's representation theorem. These inputs
must be discharged before this is a source-theorem proof. In particular
centerlessness and the restricted models are not read off A.1.34. -/
theorem rank_and_factor_dimension_of_restrictions
    (hsquare : FactorReduction.SquareAutomorphismRankTheorem.{u})
    (hsz : FactorReduction.SuzukiBinaryDegreeTheorem.{v})
    (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : Theory.GroupTheory.IsComponent G L₂) (hH : H = L ⊔ L₂)
    (hne : L ≠ L₂)
    (hq : Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
      Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))
    (T : TensorData ρ L L₂)
    (hZ : Subgroup.center L = ⊥) (hpos : 0 < primeRank 2 L)
    (hfactor : primeRank 2 (MulAut L) ≤ primeRank 2 L)
    (hmodels : 4 ≤ primeRank 2 L → FactorReduction.LargeRankModel L) :
    m ≤ 2 * primeRank 2 L ∧ (T.k = 2 ∨ T.k = 3) := by
  obtain ⟨e⟩ : Nonempty (L ≃* L₂) := by
    rcases hq with ⟨e, _, _⟩ | ⟨e, _, _⟩ <;> exact ⟨e⟩
  let : Theory.GroupTheory.IsQuasisimple L := h.component.2
  have hinner := Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot hZ)
  have hm := actor_rank_bound_of_square_bound h hL₂ hH hne e hZ
    (hsquare L hZ (lt_of_lt_of_le hpos hinner)) hfactor
  exact ⟨hm, T.factor_dimension_two_or_three_of_large_models hsz h.component hm
    h.degree_le hmodels⟩
end CFSG.Quasithin.ChapterG.Section09.TwoComponents
