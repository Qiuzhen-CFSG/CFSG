module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction

/-!
# Radical selection and offender reselection in Lemma 8.2.7

This file records the part of the proof of Lemma 8.2.7 which is independent of
the final chief-factor calculation.  The radical is selected from the actual
starred radical family, so the resulting `X` is literally `Ξ_p(L₀)` and the
prime satisfies `3 < p`.  The local input for A.3.12 is then rebuilt for the
replacement `H = XT`; no witness belonging to a previous overgroup is reused.

The universal A.3.6, A.3.8, 1.1.3, 1.1.4, 1.2.7 and A.3.12 implications are
parameters.  They are earlier source results.  The declarations below prove
the Chapter 8 deductions from those implications and from the actual local
normalizer `Normalizer.localResidual L U`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Lemma 8.2.7,
printed pp.717--718 (PDF pp.734--735), together with Lemma 1.3.3 and
Proposition 1.3.4, printed pp.509--511.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.Reselection

open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.XiEmbedding
open CFSG.Quasithin.Chapter8.Section02.Normalizer

universe u
variable {G : Type u} [Group G]

/- The polymorphic form below is the useful interface in Chapter 8.  It keeps
the actual `T` and its local-family hypotheses visible, instead of baking a
conclusion into an input structure. -/

theorem select_radical
    {𝒦 : GroupClass.{u}}
    [Finite G]
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T : Subgroup G}
    (h113 : ∀ M ∈ He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ He G)
    (h114 : HOver G (T : Set G) ⊆ He G)
    (h127 : ∀ K ∈ LStar G T,
      IsMaximalTwoLocal (normalizer (componentOrbit K T : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K T : Set G))
    (hQ : ∀ L₀ ∈ L G T,
      IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    {X : Subgroup G} (hX : X ∈ XiRadStar G T) :
    ∃ L₀ ∈ LStar G T, ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
      ¬ IsQuasisimple (XiQuotient L₀) ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
      X = XiP p L₀ ∧ (X.subgroupOf L₀).Characteristic ∧
      ∃ P : Sylow p X,
        IsPGroup p (P : Subgroup X) ∧
        normalizer (L₀ : Set G) = normalizer (X : Set G) ∧
        IsMaximalTwoLocal (normalizer (L₀ : Set G)) ∧
        L₀ ⊔ T ≤ normalizer (L₀ : Set G) := by
  obtain ⟨L₀, hL, p, hp, ho, hp3, hn, hd, heq, hchar, P, _, hnorm, hmax,
      hTL, _⟩ := XiRadStar_structure_of_source hA36 hA38 h113 h114 h127 hQ hX
  exact ⟨L₀, hL, p, hp, ho, hp3, hn, hd, heq, hchar, P, P.isPGroup', hnorm,
    hmax, hTL⟩

/-- The literal local residual is relatively normal in `N_G(U)`, and it is
T-normalized by the two normalizer hypotheses used in §8.2.6. -/
theorem localResidual_data (L U T N : Subgroup G)
    (hN : N = normalizer (U : Set G))
    (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G))
    (hLN : L ≤ N) (hNL : N ≤ normalizer (L : Set G)) :
    T ≤ normalizer (localResidual L U : Set G) ∧
      localResidual L U ≤ N ∧
      ((localResidual L U).subgroupOf N).Normal := by
  have hT := normalizes_localResidual L U T hTL hTU
  have hrel := localResidual_normal_in_relative_normalizer L N U hLN hNL
  have hrelN : N ⊓ normalizer (U : Set G) = N := by
    rw [hN, inf_idem]
  rw [hrelN] at hrel
  exact ⟨hT, hrel.1, hrel.2⟩

/-- Once the selected radical is a perfect normal subgroup of the literal
local residual, its commutators with that residual are the whole radical.  The
normality premise is relative to the ambient group in which the displayed
commutator is taken; this is the exact normality supplied by the 8.2.6 local
setup. -/
theorem commutator_eq_of_perfect
    (X R : Subgroup G) [X.Normal] [Group.IsPerfect X]
    (hXR : X ≤ R) : ⁅X, R⁆ = X := by
  apply le_antisymm (commutator_le_left X R)
  have hself : ⁅X, X⁆ = X := Subgroup.commutator_eq_self
  have hmono : ⁅X, X⁆ ≤ ⁅X, R⁆ :=
    commutator_mono (H₁ := X) (H₂ := X) (K₁ := X) (K₂ := R) le_rfl hXR
  simpa only [hself] using hmono

/-- A marked containing C-component remains relative-normal in `N`, and its
T-normalization follows by restricting the relative normalizer to T. -/
theorem containing_component_data
    (K N T : Subgroup G) (hK : K ∈ cComponentsIn N)
    (hKN : T ≤ N) (hnormal : (K.subgroupOf N).Normal) :
    K ≤ N ∧ N ≤ normalizer (K : Set G) ∧ T ≤ normalizer (K : Set G) := by
  have hnorm : N ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1).mp hnormal
  exact ⟨hK.1, hnorm, hKN.trans hnorm⟩

/-- `X` is outside the maximal two-local `M` once the replacement join is
outside and `T` is already contained in `M`.  This is the literal source
`H*(T,M)` predicate. -/
theorem join_outside (X T M : Subgroup G)
    (hH : X ⊔ T ∈ H G) (hTM : T ≤ M)
    (hout : ¬ X ⊔ T ≤ M) :
    X ≤ X ⊔ T ∧ ¬ X ≤ M ∧
      X ⊔ T ∈ HOutside G (T : Set G) (M : Set G) := by
  have hXT : T ≤ X ⊔ T := le_sup_right
  have hXnot : ¬ X ≤ M := by
    intro hXM
    exact hout (sup_le hXM hTM)
  refine ⟨le_sup_left, hXnot, ?_⟩
  exact ⟨⟨hH, hXT⟩, hout⟩

/-- Rebuild the A.3.12 input after replacing the old overgroup by the actual
join `H = XT`.  In particular the Sylow carrier and quotient residual are
constructed again from `X`, rather than transported from a former witness. -/
theorem replacement_local_input
    {𝒦 : GroupClass.{u}}
    [Finite G]
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T X H : Subgroup G} {p : ℕ}
    (hXrad : X ∈ XiRadStar G T)
    (hQ : ∀ L₀ ∈ L G T,
      IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hT : IsSylowIn 2 T H) (hHT : X ⊔ T ≤ H)
    (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hsel : ∃ L₀ ∈ LStar G T, X = XiP p L₀ ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
      ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ P : Sylow p X,
      3 < p ∧ LocalInput p T X ((P : Subgroup X).map X.subtype) H := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hXi : X ∈ Xi G T := lemma_1_3_3 hA36 hA38 hQ hXrad.1
  obtain ⟨L₀, hL, heq, hd, hn⟩ := hsel
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := X)
  subst X
  have hlocal := hQ L₀ hL.1
  have hq := (XiP_oddQuotient_of_A36 hA36 hL.1 hlocal hn ho hd).2
  exact ⟨P, hp3, localInput_of_mem_Xi hXi hT hHT ho hq P⟩

/-- Apply the genuine A.3.12 conclusion to the rebuilt input.  The normal
branch is separated explicitly; in the component branch the first assertion
of `Alternatives` is the elementary plane required by §8.2.7. -/
theorem embedding_plane_of_reselection
    {p : ℕ} {T X P H : Subgroup G}
    (_hinput : LocalInput p T X P H)
    (hA312 : ∀ {q : ℕ} {T' X' P' H' : Subgroup G},
      LocalInput q T' X' P' H' → Conclusion q T' X' P' H')
    (hnormal : ¬ (X.subgroupOf H).Normal) :
    ∃ L₀ : Subgroup G, L₀ ∈ cComponentsIn H ∧
      IsQuasisimple (XiQuotient L₀) ∧ X ≤ componentOrbit L₀ T ∧
      Nonempty (P ≃* Plane p) ∧ Alternatives p T P L₀ := by
  rcases hA312 _hinput with hN | ⟨L₀, hL, hq, hXL, halt⟩
  · exact (hnormal hN).elim
  · exact ⟨L₀, hL, hq, hXL, halt.1, halt⟩

/-- The extraspecial order-three alternative is incompatible with the rebuilt
input and the source nonnormality.  This uses the actual complement quotient
equivalence, so it excludes the selected Sylow carrier itself. -/
theorem sylow_not_extraspecial_order_three
    {p : ℕ} {T X P H : Subgroup G}
    (hinput : LocalInput p T X P H)
    (hA312 : ∀ {q : ℕ} {T' X' P' H' : Subgroup G},
      LocalInput q T' X' P' H' → Conclusion q T' X' P' H')
    (hnormal : ¬ (X.subgroupOf H).Normal)
    (hPcard : Nat.card P = p ^ 3) : False := by
  have hQcard : Nat.card (XiQuotient X) = p ^ 3 := by
    exact (Nat.card_congr hinput.complementQuotientEquiv.toEquiv).symm.trans hPcard
  have hnorm := normal_of_extraspecial_quotient_of_conclusion hinput hQcard
    (hA312 hinput)
  exact hnormal hnorm

/-- After the swapped and symplectic branches have been excluded by the local
action calculations, A.3.12 leaves exactly the linear-three or exceptional
branch.  This is the source reduction used for the L₃(4) and M₂₂ rows. -/
theorem surviving_linear_or_exceptional
    {p : ℕ} {T P L₀ : Subgroup G}
    (halt : Alternatives p T P L₀)
    (hswapped : ¬ SwappedFactors T P L₀)
    (hsymplectic : ¬ SymplecticModel p (XiQuotient L₀)) :
    LinearThreeModel p (XiQuotient L₀) ∨
      (p = 3 ∧ ExceptionalModel (XiQuotient L₀)) := by
  rcases halt.2 with hswap | hrest
  · exact (hswapped hswap.1).elim
  · rcases hrest.2 with hlinear | hrest
    · exact Or.inl hlinear
    · rcases hrest with hsymp | hexceptional
      · exact (hsymplectic hsymp.1).elim
      · exact Or.inr hexceptional

/-- The numerical `k = 1` reduction is kept as a separate arithmetic lemma,
so the model proof can use the source's lower and upper rank bounds directly. -/
theorem corank_eq_one_of_bounds {k : ℕ} (hkpos : 0 < k) (hkupper : k ≤ 1) :
    k = 1 := by omega

/-- A convenient marked package consumed by the chief-action proof.  Its
`HOutside` field, the literal normalizer, and the A.3.12 plane are all tied to
the same replacement join. -/
structure MarkedData (T X M H L U : Subgroup G) (p : ℕ) (P : Subgroup G) : Prop where
  replacement : H = X ⊔ T
  outside : H ∈ HOutside G (T : Set G) (M : Set G)
  x_not_le_M : ¬ X ≤ M
  plane : Nonempty (P ≃* Plane p)
  residual_le : localResidual L U ≤ H
  residual_normal : ((localResidual L U).subgroupOf H).Normal

/-- Assemble the marked data after the replacement.  Every field is attached
to the same `H`, `L`, `U`, and `P`, making the witness transport explicit. -/
theorem markedData_of_reselection
    {T X M H L U : Subgroup G} {p : ℕ} {P : Subgroup G}
    (hreplacement : H = X ⊔ T)
    (houtside : H ∈ HOutside G (T : Set G) (M : Set G))
    (hxnot : ¬ X ≤ M) (hplane : Nonempty (P ≃* Plane p))
    (hresidual : localResidual L U ≤ H)
    (hnormal : ((localResidual L U).subgroupOf H).Normal) :
    MarkedData T X M H L U p P :=
  ⟨hreplacement, houtside, hxnot, hplane, hresidual, hnormal⟩

/-- Transport the normalizer data when the chosen witnesses are replaced by
equal subgroups.  The equalities are explicit so an old offender witness cannot
be silently retained under a new name. -/
theorem transport_local_witness
    (L U L' U' T N N' : Subgroup G)
    (hL : L = L') (hU : U = U') (hN : N = N')
    (hNU : N = normalizer (U : Set G))
    (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G))
    (hLN : L ≤ N) (hNL : N ≤ normalizer (L : Set G)) :
    T ≤ normalizer (localResidual L' U' : Set G) ∧
      localResidual L' U' ≤ N' ∧
      ((localResidual L' U').subgroupOf N').Normal := by
  subst L'
  subst U'
  subst N'
  exact localResidual_data L U T N hNU hTL hTU hLN hNL

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.Reselection
