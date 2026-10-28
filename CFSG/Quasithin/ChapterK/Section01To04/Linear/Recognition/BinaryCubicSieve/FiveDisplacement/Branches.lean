module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.Support

/-!+# The inner and graph fixed-space obligations for binary SL₅

These are the two independent mathematical estimates remaining in the SL₅
multiple-support argument. The inner estimate acts on the actual matrix group.
The graph estimate retains the full linear normalizer and only concerns actors
outside the image. Such actors have rank at most five, by `Actors`.

Neither definition asserts a proved estimate. In particular, no total-dimension
bound or absolute irreducibility is included as a hypothesis. The assembly in
`FiveDisplacement` transports the inner actors and discharges the stronger rank
bound in the graph branch.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Proposition 4.7 and Proposition 4.8(3), pp.25–28; Aschbacher–Smith K.3.2,
printed pp.454–455 (PDF pp.465–466).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement

open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The remaining common-fixed-space estimate for actors in SL₅ itself. -/
def InnerEstimate (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    2 ≤ J.card → ∀ B : Subgroup SL5TenDimensional.Group,
    IsElementaryTwo B → IsCubic σ B → rank B ≤ 6 →
    2 * rank B < fixedCodim σ B

/-- The remaining graph-actor estimate, with the proved outer rank bound. -/
def GraphEstimate (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    2 ≤ J.card → ∀ A : Subgroup (linearNormalizer σ),
    IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
    ¬ A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) → rank A ≤ 5 →
    2 * rank A < fixedCodim (normalizerRepresentation σ) A

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement
