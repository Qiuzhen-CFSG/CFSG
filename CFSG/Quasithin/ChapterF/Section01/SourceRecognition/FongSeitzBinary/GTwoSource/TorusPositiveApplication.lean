module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.TorusWeights
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.RankOnePositiveApplication

/-!
# The two source Cartan factors in the marked-quotient coefficient argument

Use the original full H = B intersect N, its two rank-one torus maps,
and its linear action on the source section. The two weight vectors and
scalar kernel action determine the field twist. The constructed torus
h(l,m) = h₁(l)h₂(lm) then supplies the exact six left-conjugation weights
needed by positive coefficient completion. This replaces that consumer's
assumed two-parameter weights by the literal source right-action table.
The short SL₂ pinning determines the last coefficient even in F₂.

All maps live in the specified X / Q.D. The resulting map onto the original
S retains both original endpoint equations. The section representation,
pinnings, lower root equations and positive generation remain intermediate
source inputs; this does not derive them from I (6E)(a). In particular, no
binary module classification or full Borel--Weyl recognition is claimed.
Source: Fong--Seitz II (9.13)--(9.21), printed pp.215--217.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.TorusPositive
variable {G X K V : Type*} [Group G] [Group X] [Field K] [CharP K 2] [Finite K]
  [AddCommGroup V] [Module K V]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (roots : PositiveRoots K (X ⧸ Q.D))

/-- Explicit lower exchanges before the two coefficients and the twist have
been determined. The module actors are in the same full H, with the same
rank-one torus restrictions as the root-action table. -/
structure Input where
  torusData : SourceTorusData roots
  h₁ : Kˣ →* (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  h₂ : Kˣ →* (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  first_eq : ∀ a, (h₁ a : X ⧸ Q.D) = torusData.h₁ a
  second_eq : ∀ a, (h₂ a : X ⧸ Q.D) = torusData.h₂ a
  action : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →* V ≃ₗ[K] V
  v : V
  w : V
  v_ne_zero : v ≠ 0
  w_ne_zero : w ≠ 0
  v_weight : ∀ a : Kˣ, action ((h₁ a * h₂ (a^2))⁻¹) v =
    (torusData.twist (a : K) / (a : K)^3) • v
  w_weight : ∀ a : Kˣ, action ((h₁ a * h₂ (a^2))⁻¹) w =
    ((a : K) / torusData.twist (a : K)) • w
  scalar : ∀ a : Kˣ, ∃ c : K, ∀ u : V, action ((h₁ a * h₂ (a^2))⁻¹) u = c • u
  highest_injective : Function.Injective (roots.root 0)
  commuting : roots.CommutingRelations
  dc : ∀ d c, roots.x 3 d * roots.x 2 c = roots.x 0 (c*d) * roots.x 2 c * roots.x 3 d
  fc : ∀ z c, roots.x 5 z * roots.x 2 c = roots.x 1 (c*z) * roots.x 2 c * roots.x 5 z
  fd : ∀ z d, roots.x 5 z * roots.x 3 d =
    roots.x 0 (d^2*z) * roots.x 1 (d*z^2) * roots.x 3 d * roots.x 5 z
  eb_mem : ∀ b e, ⁅roots.x 4 e, roots.x 1 b⁆ ∈ (roots.root 0).range
  eb_one : ⁅roots.x 4 1, roots.x 1 1⁆ = roots.x 0 1
  fe_mem : ∀ z e, ∃ a, roots.x 5 z * roots.x 4 e =
    roots.x 0 a * roots.x 1 (e*z^3) * roots.x 2 (e*z^2) * roots.x 3 (e*z) *
      roots.x 4 e * roots.x 5 z

namespace Input
variable (d : Input (V := V) Q roots)

omit [Finite K] in
/-- The source scalar action forces Frobenius on the original field. -/
theorem twist : ∀ a, d.torusData.twist a = a^2 :=
  twist_eq_square d.torusData.twist (Q.tits.B ⊓ Q.tits.N) d.h₁ d.h₂ d.action
    d.v d.w d.v_ne_zero d.w_ne_zero d.v_weight d.w_weight d.scalar

omit [Finite K] in
/-- Both rank-one torus maps remain in the actual full Cartan. -/
theorem torus_range : d.torusData.torus.range ≤ Q.tits.B ⊓ Q.tits.N :=
  (d.torusData.torus_root_of_scalar_action (Q.tits.B ⊓ Q.tits.N) d.h₁ d.h₂
    d.first_eq d.second_eq d.action d.v d.w d.v_ne_zero d.w_ne_zero
    d.v_weight d.w_weight d.scalar).1

omit [Finite K] in
/-- The exact left-conjugation weights used by the published presentation. -/
theorem torus_root (l m : Kˣ) (i : Fin 6) (a : K) :
    d.torusData.torus (l,m) * roots.x i a * (d.torusData.torus (l,m))⁻¹ =
      roots.x i (BorelWeylData.weight l m i * a) :=
  d.torusData.torus_root (d.twist Q roots) l m i a

/-- Fill the torus-weight premise from the actual source table and module. -/
def partialData : PartialPositiveData roots where
  A_injective := d.highest_injective
  commuting := d.commuting
  dc := d.dc
  fc := d.fc
  fd := d.fd
  eb_mem := d.eb_mem
  eb_one := d.eb_one
  fe_mem := d.fe_mem
  torus := d.torusData.torus
  torus_root := d.torus_root Q roots

variable (p : ShortRankOneData roots) (hU : roots.generated = split.U)

include d p in
/-- Both unknown coefficients are now fixed, with no field-size exclusion. -/
theorem positiveRelations : roots.CharTwoRelations :=
  (d.partialData Q roots).relations_of_short_rankOne p

/-- Apply the existing positive presentation to the same source U. -/
def quotientUnipotentHom : Atlas.G2.unipotent (K := K) →* split.U :=
  RankOnePositive.quotientUnipotentHom Q split roots (d.partialData Q roots) p hU

theorem quotientUnipotentHom_surjective :
    Function.Surjective (d.quotientUnipotentHom Q split roots p hU) :=
  RankOnePositive.quotientUnipotentHom_surjective Q split roots (d.partialData Q roots) p hU

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

/-- Pull the constructed positive homomorphism back to the original common S. -/
def sourceSylowHom : Atlas.G2.unipotent (K := K) →* S :=
  RankOnePositive.sourceSylowHom Q split roots (d.partialData Q roots) p hU e h

theorem sourceSylowHom_surjective :
    Function.Surjective (d.sourceSylowHom Q split roots p hU e h) :=
  RankOnePositive.sourceSylowHom_surjective Q split roots (d.partialData Q roots) p hU e h

/-- The coefficient construction preserves the original common-overlap map. -/
theorem sourceSylowHom_quotient (u : Atlas.G2.unipotent (K := K)) :
    MarkedLocal.sylowMap Q e h (d.sourceSylowHom Q split roots p hU e h u) =
      roots.unipotentHom (d.positiveRelations Q roots p).collection u :=
  RankOnePositive.sourceSylowHom_quotient Q split roots (d.partialData Q roots) p hU e h u

/-- Both endpoint equations hold for the same original Sylow representative. -/
theorem sourceSylowHom_endpoint (i : Fin 2) (a : Fin 6 → K) :
    let s := d.sourceSylowHom Q split roots p hU e h (Atlas.G2.unipotentEquiv a)
    MarkedLocal.endpointMap Q e i
      ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        roots.product a :=
  RankOnePositive.sourceSylowHom_endpoint Q split roots (d.partialData Q roots) p hU e h i a
end Input
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.TorusPositive
