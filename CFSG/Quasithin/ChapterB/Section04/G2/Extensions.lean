module

public import Theory.Representation.G2NaturalExtensions
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# B.4.6(1) on the literal natural quotient

For an actual marked copy L of G₂(2ⁿ), form V/C_V(L) using the original action.
An equivariant identification of this quotient with the six-dimensional
split-octonion natural module transports both I.1.6(5) and its scalar
commutant. The hypothesis V = [V,E(L)] implies derived generation because
every component is perfect. The universal octonion cover then yields the
7n bound and its equality case, with full L-equivariance and the original
quotient projection preserved.

The equality conclusion identifies V with the trace-zero Weyl module;
its defining-field scalar structure can be transported along that equivalence.
The ambient hypothesis F*(G) = E(L) is not needed for this individual clause.
No conclusion-bearing record or extra cohomological premise is used.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.6(1), printed p.88, using I.1.5--6 and I.2.3,
printed pp.408 and 413. This is an application to the literal source quotient
of Theory.Representation.G2NaturalExtensions.
-/

@[expose] public section

noncomputable section
open Representation Representation.OneCohomology
open Atlas.G2.Natural
namespace CFSG.Quasithin.ChapterB.Section04.G2
variable {F L V : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
  [Group L] [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual action on V/C_V(L), formed using the fixed subspace of the
original L-action. -/
def naturalQuotientAction (σ : Representation (ZMod 2) L V) :
    Representation (ZMod 2) L (V ⧸ fixed σ) :=
  σ.quotient (fixed σ) (fun g v hv => by
    change σ g v ∈ fixed σ
    rw [hv g]
    exact hv)

private def derivedEquiv (eL : L ≃* Atlas.G2.Model F) :
    commutator L ≃* commutator (Atlas.G2.Model F) :=
  (eL.subgroupMap (commutator L)).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eL.surjective]
    rfl))

/-- I.1.6(5) on the literal natural quotient of the B.4.6 extension, with the
original derived subgroup transported through the marked group isomorphism. -/
theorem natural_quotient_cohomology
    (σ : Representation (ZMod 2) L V)
    (eL : L ≃* Atlas.G2.Model F)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, eN (naturalQuotientAction σ g v) = action F (eL g) (eN v))
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2)
      (H1 ((naturalQuotientAction σ).comp (commutator L).subtype)) = n :=
  Extensions.cohomology_dimension _ (derivedEquiv eL) eN
    (fun g v => he g.val v) n hcard

omit [Finite F] in
/-- The End_{F₂ L}(V/C_V(L)) = F assertion, expressed as an exact
characterization of its binary linear endomorphisms by unique field scalars. -/
theorem natural_quotient_commutant
    (σ : Representation (ZMod 2) L V)
    (eL : L ≃* Atlas.G2.Model F)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, eN (naturalQuotientAction σ g v) = action F (eL g) (eN v))
    (f : (V ⧸ fixed σ) →ₗ[ZMod 2] (V ⧸ fixed σ)) :
    (∀ g v, f (naturalQuotientAction σ g v) = naturalQuotientAction σ g (f v)) ↔
      ∃! c : F, ∀ v, eN (f v) = c • eN v := by
  constructor
  · intro hf
    exact (Extensions.scalar_commutant ((naturalQuotientAction σ).comp (commutator L).subtype) (derivedEquiv eL) eN
      (fun g v => he g.val v) f).mp (fun g v => hf g.val v)
  · rintro ⟨c, hc, _⟩ g v
    apply eN.injective
    rw [hc, he, he, hc, map_smul]

/-- The extension bound and equality case on an arbitrary marked copy of G₂.
The Weyl comparison is equivariant for the original full L and commutes with
the literal quotient by C_V(L). No F-module structure on the kernel is assumed. -/
theorem natural_extension_dimension [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) L V)
    (hgen : Coinvariants.ker (σ.comp (commutator L).subtype) = ⊤)
    (eL : L ≃* Atlas.G2.Model F)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, eN (naturalQuotientAction σ g v) = action F (eL g) (eN v))
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) V ≤ 7 * n ∧
      (Module.finrank (ZMod 2) V = 7 * n →
        ∃ e : TraceZero F ≃ₗ[ZMod 2] V,
          (∀ g w, e (traceZeroAction F (eL g) w) = σ g (e w)) ∧
          ∀ w, eN ((fixed σ).mkQ (e w)) = mk F w) := by
  let σM := σ.comp eL.symm.toMonoidHom
  let p := eN.toLinearMap.comp (fixed σ).mkQ
  have hp : Function.Surjective p := eN.surjective.comp (fixed σ).mkQ_surjective
  have hfixed : p.ker ≤ fixed σM := by
    intro v hv g
    have hz : (fixed σ).mkQ v = 0 := eN.injective (by simpa [p] using hv)
    exact ((Submodule.Quotient.mk_eq_zero _).mp hz) (eL.symm g)
  have hgenM : Coinvariants.ker (σM.comp (commutator (Atlas.G2.Model F)).subtype) = ⊤ := by
    have hle : Coinvariants.ker (σ.comp (commutator L).subtype) ≤
        Coinvariants.ker (σM.comp (commutator (Atlas.G2.Model F)).subtype) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, v⟩, rfl⟩
      have hh := Coinvariants.sub_mem_ker
        (ρ := σM.comp (commutator (Atlas.G2.Model F)).subtype) (derivedEquiv eL g) v
      simpa [σM, derivedEquiv] using hh
    exact top_unique (hgen ▸ hle)
  have heM (g : Atlas.G2.Model F) (v : V) : p (σM g v) = action F g (p v) := by
    simpa [p, σM, naturalQuotientAction] using he (eL.symm g) ((fixed σ).mkQ v)
  obtain ⟨hle, heq⟩ := Extensions.dimension_and_equality σM p hp hfixed hgenM heM n hcard
  refine ⟨hle, fun hv => ?_⟩
  obtain ⟨e, he, hover⟩ := heq hv
  refine ⟨e, ?_, hover⟩
  intro g w
  simpa [σM] using he (eL g) w

/-- The literal natural quotient has binary dimension 6n. -/
theorem natural_quotient_dimension
    (σ : Representation (ZMod 2) L V)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) (V ⧸ fixed σ) = 6 * n := by
  rw [eN.finrank_eq, ← Module.finrank_mul_finrank (ZMod 2) F (Space F),
    finrank_space, coefficient_finrank_of_card 2 n hcard, Nat.mul_comm]

/-- B.4.6(1), including its equality clause, from V = [V,E(L)] and the
marked natural quotient. The ambient F*(G) hypothesis is unnecessary for this
clause. Perfectness of components supplies the required derived generation;
there is no additional extension or cohomology premise. -/
theorem lemma_B46_one [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) L V)
    (hgen : Coinvariants.ker (σ.comp (Theory.GroupTheory.componentLayer L).subtype) = ⊤)
    (eL : L ≃* Atlas.G2.Model F)
    (eN : (V ⧸ fixed σ) ≃ₗ[ZMod 2] Space F)
    (he : ∀ g v, eN (naturalQuotientAction σ g v) = action F (eL g) (eN v))
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) :
    (∀ f : (V ⧸ fixed σ) →ₗ[ZMod 2] (V ⧸ fixed σ),
      (∀ g v, f (naturalQuotientAction σ g v) = naturalQuotientAction σ g (f v)) ↔
        ∃! c : F, ∀ v, eN (f v) = c • eN v) ∧
    Module.finrank (ZMod 2) V ≤ 7 * n ∧
      (Module.finrank (ZMod 2) V = 7 * n →
        ∃ e : TraceZero F ≃ₗ[ZMod 2] V,
          (∀ g w, e (traceZeroAction F (eL g) w) = σ g (e w)) ∧
          ∀ w, eN ((fixed σ).mkQ (e w)) = mk F w) := by
  have hE : Theory.GroupTheory.componentLayer L ≤ commutator L := by
    apply sSup_le
    intro K hK
    have : Theory.GroupTheory.IsQuasisimple K := hK.2
    calc
      K = ⁅K, K⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ commutator L := Subgroup.commutator_mono le_top le_top
  have hD : Coinvariants.ker (σ.comp (commutator L).subtype) = ⊤ := by
    have hle : Coinvariants.ker (σ.comp (Theory.GroupTheory.componentLayer L).subtype) ≤
        Coinvariants.ker (σ.comp (commutator L).subtype) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, v⟩, rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := σ.comp (commutator L).subtype)
        ⟨g.val, hE g.property⟩ v
    exact top_unique (hgen ▸ hle)
  exact ⟨natural_quotient_commutant σ eL eN he,
    natural_extension_dimension σ hD eL eN he n hcard⟩
end CFSG.Quasithin.ChapterB.Section04.G2
