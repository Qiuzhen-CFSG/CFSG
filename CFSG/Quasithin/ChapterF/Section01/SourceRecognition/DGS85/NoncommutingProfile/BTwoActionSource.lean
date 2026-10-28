module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCoreSpan
public import Theory.Representation.BinaryConjugationSection.ComplementaryFixed

/-!
# Constructing the b=2 quotient geometry from earlier source products

The Chapter 7 full-vertex Sylow products contain the intermediate core,
and hence prove its span by the two center groups and the literal D.
When D equals the middle center, those groups have complementary images
in the actual core quotient. Their Sylow-fixed conjugacy eliminates every
global fixed vector, so fixed-preimage control is a theorem rather than an
extra action premise. The existing quadratic and index calculations then
exclude the paired noncommuting configuration in characteristic two.

The original F1.11 application retains the reduced-completion inclusion
and the line indices in the original marked subgroups. The actor and
natural-center products are earlier Chapter 6--7 inputs, produced by the
critical noncommuting family. Constructing the two D identities and the
shifted noncommuting pair remains with this Chapter 10 proof; final source
assembly must discharge the earlier inputs. This does not establish the
unconditional 10.6 exclusion or either 10.9/10.10 alternative.

Source: DGS, *Groups and Graphs* (1985), 7.1, 10.1(c), 10.3--10.6,
printed pp.126--127 and 154--158.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

/-- Marked local actor and its chosen neighbor conjugator. This contains
neither a core span nor an assertion about fixed vectors on Q/Z. -/
structure BTwoActionData (F : Bool → Subgroup G) (t v w u : Vertex F)
    (k : Type*) [Field k] [Finite k] [CharP k 2] where
  actor : Subgroup G
  actor_le : actor ≤ stabilizer F w
  core_le : Q F w ≤ actor
  quotient : actor →* SL(2,k)
  onto : Function.Surjective quotient
  kernel : quotient.ker = (Q F w).subgroupOf actor
  sylow : Sylow 2 SL(2,k)
  actor_image : ((Z F t).subgroupOf actor).map quotient = sylow
  conjugator : actor
  moves : (conjugator : G) • v = u

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- The literal D identity and the earlier full-vertex Sylow products
construct both the source core span and fixed-preimage control. -/
def BTwoActionData.localGeometry (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {t v w u : Vertex (family P)}
    (htv : (graph (family P)).Adj t v) (hvw : (graph (family P)).Adj v w)
    (huw : (graph (family P)).Adj u w) (hc : IsCriticalPair (family P) v u)
    (c : BTwoActionData (family P) t v w u k)
    (hD : D (family P) v u = Z (family P) w)
    (hsv : Stellmacher.IsSylowSubgroupIn
      (Z (family P) u ⊔ Q (family P) v) (stabilizer (family P) v))
    (hsu : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) u) (stabilizer (family P) u)) :
    BTwoLocalGeometry (family P) t v w u k := by
  let := finite_endpoints h
  let F := family P
  have hZQ (x : Vertex F) : Z F x ≤ Q F x := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h x).1 hz)).1
  have hspan := bTwo_core_span_of_sylow_products h hS hb huw hvw.symm hsv hsu
    (hD.le.trans (hZQ w))
  have hAQ : Z F v ≤ Q F w := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw,hb]; decide)
  have hCQ : Z F u ≤ Q F w := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr huw,hb]; decide)
  have hZV : Z F w ≤ Q F v := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw.symm,hb]; decide)
  have hZU : Z F w ≤ Q F u := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr huw.symm,hb]; decide)
  have hspanZ : Q F w = (Z F v ⊔ Z F u) ⊔ Z F w := by rwa [hD] at hspan
  have hcomm : ⁅Z F v,Z F u⁆ ≤ Z F w :=
    (criticalPair_centers F h.generate hc).2.trans
      ((inf_le_inf (hZQ v) (hZQ u)).trans hD.le)
  have hnQ : c.actor ≤ normalizer (Q F w : Set G) := c.actor_le.trans
    ((stabilizer F w).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hnZ : c.actor ≤ normalizer (Z F w : Set G) := c.actor_le.trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F w)).mp (Z_normal F w))
  let : ((Z F w).subgroupOf (Q F w)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hZQ w)).mpr (c.core_le.trans hnZ)
  let := graph_Z_elementary h v
  let := graph_Z_elementary h u
  let := pair_quotient_elementary (Q F w) (Z F w) (Z F v) (Z F u)
    hAQ hCQ (hZQ w) hspanZ hcomm
  have hcanonical := exists_canonical c.actor (Q F w) (Z F w)
    c.core_le (hZQ w) hnQ hnZ c.quotient c.onto c.kernel
  let σ := hcanonical.choose
  let e := hcanonical.choose_spec.choose
  have hinter : (Z F v ⊔ Z F w) ⊓ (Z F u ⊔ Z F w) = Z F w := by
    apply le_antisymm
    · exact (inf_le_inf (sup_le (hZQ v) hZV) (sup_le (hZQ u) hZU)).trans hD.le
    · exact le_inf le_sup_right le_sup_right
  have hconj : Z F u = (Z F v).conjBy (c.conjugator : G) :=
    (congrArg (Z F) c.moves).symm.trans (Z_translate F (c.conjugator : G) v)
  have hfix : ⁅Z F t,Z F v⁆ ≤ Z F w := by
    have he : ⁅Z F t,Z F v⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (graph_centers_commute_of_short h hS
        (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv,hb]; decide))
    exact he.le.trans bot_le
  exact {
    actor := c.actor
    actor_le := c.actor_le
    core_le := c.core_le
    quotient := c.quotient
    onto := c.onto
    kernel := c.kernel
    sylow := c.sylow
    actor_image := c.actor_image
    conjugator := c.conjugator
    moves := c.moves
    span := hspan
    intersection := hD
    fixed_preimage := fixed_preimage_of_complementary_pair c.actor (Q F w) (Z F w)
      (Z F v) (Z F u) (Z F t) σ c.quotient c.onto e hAQ hCQ hspanZ hinter
      c.conjugator hconj c.sylow c.actor_image hfix }

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- Original marked F1.11 application: the two D identities and the earlier
Chapter 7 Sylow products and center-line indices suffice. Both the core
spans and fixed-preimage assertions are proved by the constructor above. -/
theorem original_bTwo_noncentral_exclusion_of_D_identities
    (h : HypothesisF11 L S) (hb : b F = 2) {t u : Vertex F}
    (ht : (graph F).Adj t α) (hu : (graph F).Adj u β)
    (hc₀ : IsCriticalPair F β t) (hc₁ : IsCriticalPair F α u)
    (hne₀ : ⁅Z F β,Z F t⁆ ≠ ⊥) (hne₁ : ⁅Z F α,Z F u⁆ ≠ ⊥)
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (c₀ : BTwoActionData F u β α t k₀)
    (c₁ : BTwoActionData F t α β u k₁)
    (hD₀ : D F β t = Z F α) (hD₁ : D F α u = Z F β)
    (hs₀ : Stellmacher.IsSylowSubgroupIn (Z F t ⊔ Q F β) (stabilizer F β) ∧
      Stellmacher.IsSylowSubgroupIn (Z F β ⊔ Q F t) (stabilizer F t))
    (hs₁ : Stellmacher.IsSylowSubgroupIn (Z F u ⊔ Q F α) (stabilizer F α) ∧
      Stellmacher.IsSylowSubgroupIn (Z F α ⊔ Q F u) (stabilizer F u))
    (hline₀ : ((Q F u).map (G₀ L S).subtype).relIndex
      ((Z F α).map (G₀ L S).subtype) = Nat.card k₀)
    (hline₁ : ((Q F t).map (G₀ L S).subtype).relIndex
      ((Z F β).map (G₀ L S).subtype) = Nat.card k₁) : False := by
  have hadj : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  let d₀ := c₀.localGeometry (reduced_triple h) (reduced_kernel_sylow h)
    hb hu hadj.symm ht hc₀ hD₀ hs₀.1 hs₀.2
  let d₁ := c₁.localGeometry (reduced_triple h) (reduced_kernel_sylow h)
    hb ht hadj hu hc₁ hD₁ hs₁.1 hs₁.2
  exact original_bTwo_noncentral_exclusion_of_line_indices h hb ht hu
    hc₀ hc₁ hne₀ hne₁ d₀ d₁ hline₀ hline₁

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
