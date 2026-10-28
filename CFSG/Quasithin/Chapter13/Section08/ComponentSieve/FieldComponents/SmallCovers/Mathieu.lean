module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Seed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Native
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.SourceSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.CentralSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.Contracts
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Exclusion
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic

/-!
# The M₂₂ exclusion in 13.8.21(2)

The literal seed Ṽ₃ embeds equivariantly in I = [Ũ_H,K], using its earlier
commutator identity and L₁ ≤ K. Once the marked radical of K₁T lies in L₁T,
relative normality gives C_I(O₂(L₁T)) ≤ C_I(O₂(K₁T)). Intertwining code
coordinates on that radical transport the fixed line, contradicting the
irreducible rank-two seed via SmallCovers.no_rank_two_seed_in_parabolic_fixed_line.

Native.lean proves the inner hexad/partition core comparison and three-part
bound. Seed.lean keeps Source.Utilde and proves invariance from actual
conjugation. The quotient comparison here retains an actual K/O₂(K) ≃ M₂₂
and its canonical identification with Source.starImage H K.

Placement now constructs the actual parabolic, handles the outer supplement,
and proves |L₁|₃ = 3. CodeAction chooses compatible component coordinates
from code recognition and proves the radical intertwining, then transfers
the precise M₂₄ fixed-line input through the genuine ten-dimensional M₂₂
hyperplane. SourceSeed derives the seed's dimension, irreducibility and
linear commutator identity from the earlier subgroup facts.

`source_contradiction_of_earlier` completes this branch from the genuine
standing setup and explicit earlier F.9.18/B.4 inputs. The full alternatives
give invariance, absence of every faithful FF-module, I = [Ũ_H,K], and code
recognition on the literal central quotient I/C_I(K). CentralSeed proves the
seed survives that quotient injectively and equivariantly, so no splitting
of the Irr⁺ space is assumed. The native M₂₄ octad fixed-line theorem is now
proved and discharges the fixed-line input through the M₂₂ restriction.

The B.4.2 input uses the corrected projective-line convention in
Recognition.SourceB4. The universal earlier classification implications
and the precise F.9.18 outputs remain explicit inputs, whose source owners
must supply them in the full 13.8.21 assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21(2), printed p.956, PDF p.973 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
variable {A D E W : Type*} [Group A] [Group D] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The terminal reduction constructs the seed embedding and derives the
fixed-space comparison; its model coordinates and radical placement remain inputs. -/
theorem no_rank_two_commutator_seed
    (ρ : Representation (ZMod 2) A E) (K L P Q : Subgroup A)
    (I : Subrepresentation ρ) (S : Subrepresentation (ρ.comp P.subtype))
    [Representation.IsIrreducible S.toRepresentation]
    (hLK : L ≤ K) (hI : I.toSubmodule = subspaceCommutator ρ ⊤ K)
    (hS : S.toSubmodule = subspaceCommutator ρ S.toSubmodule L)
    (hseed : Module.finrank (ZMod 2) S.toSubmodule = 2)
    (hPQ : P ≤ Q) (hcore : Q.pCoreIn 2 ≤ P)
    (σ : Representation (ZMod 2) D W) (f : Q.pCoreIn 2 →* D)
    (e : I.toSubmodule ≃ₗ[ZMod 2] W)
    (he : ∀ q v, e (I.toRepresentation q.val v) = σ (f q) (e v))
    (R : Subgroup D) (hR : f.range = R)
    (hline : Module.finrank (ZMod 2) (fixedSpace σ R) = 1) : False := by
  exact no_rank_two_seed_in_parabolic_fixed_line I.toRepresentation P Q S.toRepresentation
    (seedEmbedding ρ K L I S.toSubmodule hLK hI hS)
    (seedEmbedding_injective ρ K L I S.toSubmodule hLK hI hS)
    (seedEmbedding_equivariant ρ K L I P S hLK hI hS)
    hseed (fixed_core_compare I.toRepresentation P Q hPQ hcore)
    (fixed_line_of_radical_model I.toRepresentation Q σ f e he R hR hline)

variable {G : Type*} [Group G] [Finite G]
/-- Coordinates on K* are obtained from the genuine component quotient
comparison, rather than identifying K/O₂(K) with its image without proof. -/
noncomputable def componentCoordinates (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    Source.starImage H K ≃* Sporadic.Mathieu.M22 :=
  (Components.componentStarEquiv H K hKH hK).symm.trans e

/-- The model coordinates commute with the actual component quotient comparison. -/
theorem componentCoordinates_apply (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) (x : K ⧸ pCore 2 K) :
    componentCoordinates H K hKH hK e (Components.componentStarEquiv H K hKH hK x) = e x := by
  simp only [componentCoordinates, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

variable (H K K₁ L₁ T V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The same deduction for Source.Utilde and the literal image of V₃.
This is a conditional reduction, not the completed M₂₂ source exclusion. -/
theorem source_seed_contradiction (d : SourceAction H V₃ V₁)
    (hn : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (I : Subrepresentation d.onH)
    [Representation.IsIrreducible
      (seedRepresentation d.onH ((L₁ ⊔ T).subgroupOf H)
        (source_seed_stable d (L₁ ⊔ T) hn)).toRepresentation]
    (hLK : L₁ ≤ K) (hLK₁ : L₁ ≤ K₁)
    (hI : I.toSubmodule = subspaceCommutator d.onH ⊤ (K.subgroupOf H))
    (hS : seedSpace H V₃ V₁ =
      subspaceCommutator d.onH (seedSpace H V₃ V₁) (L₁.subgroupOf H))
    (hseed : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (hcore : ((K₁ ⊔ T).subgroupOf H).pCoreIn 2 ≤ (L₁ ⊔ T).subgroupOf H)
    (σ : Representation (ZMod 2) D W) (f : ((K₁ ⊔ T).subgroupOf H).pCoreIn 2 →* D)
    (e : I.toSubmodule ≃ₗ[ZMod 2] W)
    (he : ∀ q v, e (I.toRepresentation q.val v) = σ (f q) (e v))
    (R : Subgroup D) (hR : f.range = R)
    (hline : Module.finrank (ZMod 2) (fixedSpace σ R) = 1) : False := by
  exact no_rank_two_commutator_seed d.onH (K.subgroupOf H) (L₁.subgroupOf H)
    ((L₁ ⊔ T).subgroupOf H) ((K₁ ⊔ T).subgroupOf H) I
    (seedRepresentation d.onH ((L₁ ⊔ T).subgroupOf H)
      (source_seed_stable d (L₁ ⊔ T) hn))
    (subgroupOf_mono H hLK) hI hS hseed
    (subgroupOf_mono H (sup_le_sup hLK₁ le_rfl)) hcore σ f e he R hR hline
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
