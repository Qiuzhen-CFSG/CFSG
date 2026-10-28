module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Generic
public import Theory.Frattini.PGroup

/-!
# The marked binary hypotheses of original MS93 (1.7)

Section 1 retains (WBN) and the three extension clauses (A), not the later
MS3 or characteristic minimality assumptions. The kernel E of the marked
SL₃(2) quotient is retained: Q is O₂(E), not silently E. The two parabolics
P_i are preimages for the same marking and the same flag. A common Sylow
subgroup selects Q_i inside the preimage of O₂(P_i/E); the Section 1 vertex
group is M_i = N_(P_i)(Q_i). Keeping this normalizer is essential if E/Q has
odd order. In a two-group-kernel specialization M_i can be identified with
P_i, but that identification is not inserted as a source assumption.

There are two different local residuals in the original notation. On p.832,
L_delta is O^{2′}(M_delta), and tilde L_delta is O²(L_delta). The existing
`MS93.rankOne` is the latter; it generates the global L. The fixed-point
and rank-one-module conditions of (1.7) use the former.

Natural factors below are surjective coordinate homomorphisms with the
specified intrinsic kernel and the actual conjugation formula. Thus they
supply quotient isomorphisms, not dimension or group-family tags. The
rank-one domain is the actual M_beta-normal closure of X_alpha, and C is
the preimage of C_(U/Z)(L). Only X_alpha's parabolic normality is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (A) on p.828, notation on pp.829,832, and (1.7) on pp.847--848.
This file specifies the inputs; it does not assert (1.7)'s conclusions.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing

open Subgroup
open scoped commutatorElement

universe u
variable {M : Type u} [Group M]

/-- The source Q = O₂(E), included in M; E is the marked quotient kernel. -/
def extensionCore (π : M →* SL) : Subgroup M :=
  (pCore 2 π.ker).map π.ker.subtype

instance extensionCore_normal (π : M →* SL) : (extensionCore π).Normal := by
  constructor
  intro x hx g
  obtain ⟨y, hy, rfl⟩ := hx
  let a := π.ker.normalizerMonoidHom ⟨g, by simp only [normalizer_eq_top, mem_top]⟩
  exact ⟨a y, characteristic_iff_le_comap.mp inferInstance a hy, rfl⟩

/-- The actual extension core is a two-group. -/
theorem extensionCore_isPGroup (π : M →* SL) : IsPGroup 2 (extensionCore π) :=
  pCore_isPGroup.map π.ker.subtype

/-- The kernel contains its two-core. -/
theorem extensionCore_le_kernel (π : M →* SL) : extensionCore π ≤ π.ker :=
  map_subtype_le _

/-- The global L, with the ordered residuals of source p.828. -/
def component (π : M →* SL) (g : SL) : Subgroup M :=
  rankOne (parabolic π g false) ⊔ rankOne (parabolic π g true)

/-- The untilded L_delta of Section 1. -/
def localResidual (P : Subgroup M) : Subgroup M :=
  (primeToResidual 2 P).map P.subtype

/-- The Q_delta of Section 1, included in M. -/
def localCore (P : Subgroup M) : Subgroup M := (pCore 2 P).map P.subtype

/-- The inverse image of the fixed flag Borel, used as the common Sylow carrier. -/
def borelPreimage (π : M →* SL) (g : SL) : Subgroup M :=
  (modelBorel g).comap π

/-- The extension clauses used throughout Section 1, with an actual quotient
marking. No pushing-up minimality is imposed. -/
structure ExtensionBase where
  projection : M →* SL
  surjective : Function.Surjective projection
  flag : SL
  weakBN : BinaryWeakBN flag
  odd_core : pPrimeCore 2 projection.ker = ⊥
  odd_index : Nat.Coprime 2 (pCore 2 projection.ker).index
  no_supplement : ∀ F : Subgroup M,
    component projection flag ≤ F ⊔ projection.ker →
      projection.ker ≤ F ⊔ extensionCore projection

/-- The source common Sylow is kept over the already specified extension. -/
structure Extension where
  base : ExtensionBase (M := M)
  borel : Subgroup M
  borel_eq : borel = borelPreimage base.projection base.flag
  sylow : Sylow 2 borel

namespace Extension

abbrev projection (e : Extension (M := M)) : M →* SL := e.base.projection
abbrev flag (e : Extension (M := M)) : SL := e.base.flag

end Extension

/-- The common source Sylow subgroup S, included in M. -/
def commonSylow (e : Extension (M := M)) : Subgroup M :=
  (e.sylow : Subgroup e.borel).map e.borel.subtype

/-- The chosen Q_i in S with quotient O₂(P_i/E), before taking its normalizer. -/
def selectedCore (e : Extension (M := M)) (i : Bool) : Subgroup M :=
  commonSylow e ⊓
    ((pCore 2 (modelParabolic e.flag i)).map (modelParabolic e.flag i).subtype).comap
      e.projection

/-- The actual M_i = N_(P_i)(Q_i) from source p.832. It must not be silently
replaced by P_i when E has an odd quotient above Q. -/
def localParabolic (e : Extension (M := M)) (i : Bool) : Subgroup M :=
  parabolic e.projection e.flag i ⊓ normalizer (selectedCore e i : Set M)

/-- A natural three-dimensional factor, using one automorphism of the
marked quotient. The kernel and conjugation equation specify the module. -/
structure NaturalFactor (π : M →* SL) (L H N : Subgroup M) where
  marking : SL ≃* SL
  coordinates : H →* Multiplicative (Fin 3 → ZMod 2)
  surjective : Function.Surjective coordinates
  kernel : coordinates.ker = N.subgroupOf H
  normalized : L ≤ normalizer (H : Set M)
  action : ∀ l ∈ L, ∀ x y : H,
    (y : M) = l * (x : M) * l⁻¹ →
    Multiplicative.toAdd (coordinates y) =
      (marking (π l)).val.mulVec (Multiplicative.toAdd (coordinates x))

namespace NaturalFactor
variable {π : M →* SL} {L H N : Subgroup M}

/-- Normality of the intrinsic kernel follows from the coordinate map. -/
theorem kernel_normal (n : NaturalFactor π L H N) : (N.subgroupOf H).Normal :=
  n.kernel ▸ inferInstance

/-- The specified factor is genuinely isomorphic to the additive three-space. -/
noncomputable def quotientEquiv (n : NaturalFactor π L H N) :
    letI := n.kernel_normal
    H ⧸ N.subgroupOf H ≃* Multiplicative (Fin 3 → ZMod 2) := by
  letI := n.kernel_normal
  exact (QuotientGroup.quotientMulEquivOfEq n.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective n.coordinates n.surjective)

/-- Trivial intrinsic kernel gives coordinates on Z itself. -/
noncomputable def equivOfBot (n : NaturalFactor π L H ⊥) :
    H ≃* Multiplicative (Fin 3 → ZMod 2) :=
  MulEquiv.ofBijective n.coordinates
    ⟨n.coordinates.ker_eq_bot_iff.mp (by simpa using n.kernel), n.surjective⟩

@[simp] theorem quotientEquiv_apply (n : NaturalFactor π L H N) (x : H) :
    letI := n.kernel_normal
    n.quotientEquiv (QuotientGroup.mk' (N.subgroupOf H) x) = n.coordinates x := rfl

end NaturalFactor

/-- A factor contragredient to the specified natural Z, with the very same
quotient marking. This is a conclusion type for part (ii), not a source input. -/
structure DualFactor (π : M →* SL) (L H N Z : Subgroup M)
    (z : NaturalFactor π L Z ⊥) where
  coordinates : H →* Multiplicative (Fin 3 → ZMod 2)
  surjective : Function.Surjective coordinates
  kernel : coordinates.ker = N.subgroupOf H
  normalized : L ≤ normalizer (H : Set M)
  action : ∀ l ∈ L, ∀ x y : H,
    (y : M) = l * (x : M) * l⁻¹ →
    Multiplicative.toAdd (coordinates y) =
      ((z.marking (π l))⁻¹.val).transpose.mulVec
        (Multiplicative.toAdd (coordinates x))

namespace DualFactor
variable {π : M →* SL} {L H N Z : Subgroup M} {z : NaturalFactor π L Z ⊥}

theorem kernel_normal (n : DualFactor π L H N Z z) : (N.subgroupOf H).Normal :=
  n.kernel ▸ inferInstance

/-- Coordinates on the intrinsic quotient with contragredient action. -/
noncomputable def quotientEquiv (n : DualFactor π L H N Z z) :
    letI := n.kernel_normal
    H ⧸ N.subgroupOf H ≃* Multiplicative (Fin 3 → ZMod 2) := by
  letI := n.kernel_normal
  exact (QuotientGroup.quotientMulEquivOfEq n.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective n.coordinates n.surjective)

@[simp] theorem quotientEquiv_apply (n : DualFactor π L H N Z z) (x : H) :
    letI := n.kernel_normal
    n.quotientEquiv (QuotientGroup.mk' (N.subgroupOf H) x) = n.coordinates x := rfl

end DualFactor

/-- An actual natural rank-one factor for the specified local actor. -/
structure RankOneFactor (K H N : Subgroup M) where
  projection : K →* SL2
  surjective : Function.Surjective projection
  coordinates : H →* Multiplicative (Fin 2 → ZMod 2)
  coordinates_surjective : Function.Surjective coordinates
  kernel : coordinates.ker = N.subgroupOf H
  normalized : K ≤ normalizer (H : Set M)
  action : ∀ (l : K) (x y : H),
    (y : M) = (l : M) * (x : M) * (l : M)⁻¹ →
    Multiplicative.toAdd (coordinates y) =
      (projection l).val.mulVec (Multiplicative.toAdd (coordinates x))

namespace RankOneFactor
variable {K H N : Subgroup M}

/-- The rank-one factor has a genuine normal kernel. -/
theorem kernel_normal (n : RankOneFactor K H N) : (N.subgroupOf H).Normal :=
  n.kernel ▸ inferInstance

/-- The generated local factor is the actual natural two-space. -/
noncomputable def quotientEquiv (n : RankOneFactor K H N) :
    letI := n.kernel_normal
    H ⧸ N.subgroupOf H ≃* Multiplicative (Fin 2 → ZMod 2) := by
  letI := n.kernel_normal
  exact (QuotientGroup.quotientMulEquivOfEq n.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective n.coordinates n.coordinates_surjective)

@[simp] theorem quotientEquiv_apply (n : RankOneFactor K H N) (x : H) :
    letI := n.kernel_normal
    n.quotientEquiv (QuotientGroup.mk' (N.subgroupOf H) x) = n.coordinates x := rfl

end RankOneFactor

/-- Normal closure under the actual parabolic, included in M. -/
def localGenerated (P X : Subgroup M) : Subgroup M :=
  (normalClosure (X.subgroupOf P : Set P)).map P.subtype

/-- The actual source C/Z = C_(U/Z)(L). -/
def fixedPreimage (L X Z : Subgroup M) [Z.Normal] : Subgroup M :=
  centralizerModulo (generated X) L Z

/-- The local closure lies in the ambient closure, even though X need not
be normal in M. -/
theorem localGenerated_le_generated (P X : Subgroup M) :
    localGenerated P X ≤ generated X := by
  apply map_le_iff_le_comap.mpr
  apply normalClosure_le_normal
  intro x hx
  exact le_normalClosure hx

/-- If X is in the parabolic, the local closure contains all of X. -/
theorem le_localGenerated (P X : Subgroup M) (hXP : X ≤ P) :
    X ≤ localGenerated P X := by
  intro x hx
  exact ⟨⟨x, hXP hx⟩, le_normalClosure hx, rfl⟩

/-- The preimage definition means precisely commuting with L modulo Z. -/
theorem mem_fixedPreimage (L X Z : Subgroup M) [Z.Normal] (x : M) :
    x ∈ fixedPreimage L X Z ↔ x ∈ generated X ∧ ∀ l ∈ L, ⁅l, x⁆ ∈ Z :=
  mem_centralizerModulo_iff

/-- The genuine preimage C contains Z when Z is in U. -/
theorem le_fixedPreimage (L X Z : Subgroup M) [Z.Normal] (hZX : Z ≤ X) :
    Z ≤ fixedPreimage L X Z := by
  intro z hz
  exact mem_centralizerModulo_iff.mpr ⟨le_normalClosure (hZX hz),
    fun l hl => commutator_le_right L Z (commutator_mem_commutator hl hz)⟩

/-- Phi(U) ≤ Z makes C normal in U, so U/C is an intrinsic group quotient.
No ambient normality of X or additional fixed-space hypothesis is used. -/
theorem fixedPreimage_normal [Finite M] (L X Z : Subgroup M) [Z.Normal]
    (hZX : Z ≤ X) (hU : IsPGroup 2 (generated X))
    (hPhi : (frattini (generated X)).map (generated X).subtype ≤ Z) :
    ((fixedPreimage L X Z).subgroupOf (generated X)).Normal := by
  let : Fact (IsPGroup 2 (generated X)) := ⟨hU⟩
  apply commutator_top_left_le_iff.mp
  have hcomm : ⁅(⊤ : Subgroup (generated X)), ⊤⁆ ≤ frattini (generated X) :=
    commutator_le_frattini_of_isPGroup (p := 2)
  refine ((commutator_mono le_rfl le_top).trans hcomm).trans ?_
  intro x hx
  exact le_fixedPreimage L X Z hZX (hPhi (mem_map_of_mem _ hx))

/-- All hypotheses in original (1.7), specialized to q=2. The natural factor
of U/C_U(W) in part (ii) is deliberately an additional branch hypothesis. -/
structure SourceData [Finite M] (e : Extension (M := M)) (i : Bool) (Z W X : Subgroup M)
    [Z.Normal] [W.Normal] where
  z_le : Z ≤ X
  x_le : X ≤ extensionCore e.projection
  w_le : W ≤ extensionCore e.projection
  x_normal : (X.subgroupOf (localParabolic e i)).Normal
  natural : NaturalFactor e.projection (component e.projection e.flag) Z ⊥
  frattini_le : (frattini (generated X)).map (generated X).subtype ≤ Z
  commutator_le : ⁅X, W⁆ ≤ Z
  commutator_nontrivial : Nat.card (⁅X, W⁆ : Subgroup M) ≠ 1
  commutator_card_le : Nat.card (⁅X, W⁆ : Subgroup M) ≤ 4
  seed_fixed : ⁅X, localResidual (localParabolic e i)⁆ ≤
    fixedPreimage (component e.projection e.flag) X Z
  rank_one_natural : RankOneFactor
    (localResidual (localParabolic e (!i)))
    (localGenerated (localParabolic e (!i)) X)
    (fixedPreimage (component e.projection e.flag) X Z)

namespace SourceData
variable [Finite M] {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
  [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
include d

/-- U is a two-subgroup of the actual extension kernel. -/
theorem generated_isPGroup : IsPGroup 2 (generated X) :=
  (extensionCore_isPGroup e.projection).to_le
    (generated_le X (extensionCore e.projection) d.x_le)

/-- The local commutator bound extends to the whole normal closure. -/
theorem generated_commutator : ⁅generated X, W⁆ ≤ Z :=
  generated_commutator_le X W Z d.commutator_le

/-- The source nontriviality condition concerns a genuine nonzero pairing. -/
theorem generated_commutator_ne_bot : ⁅generated X, W⁆ ≠ ⊥ := by
  intro h
  have hx : ⁅X, W⁆ = ⊥ := bot_unique
    ((commutator_mono le_normalClosure le_rfl).trans h.le)
  apply d.commutator_nontrivial
  simpa only [hx] using (card_bot : Nat.card (⊥ : Subgroup M) = 1)

/-- The source U/C is well-defined under the stated source assumptions. -/
theorem C_normal :
    ((fixedPreimage (component e.projection e.flag) X Z).subgroupOf (generated X)).Normal :=
  fixedPreimage_normal _ _ _ d.z_le d.generated_isPGroup d.frattini_le

/-- The source barred U, with its proved intrinsic normal denominator. -/
abbrev Ubar :=
  letI := d.C_normal
  generated X ⧸ (fixedPreimage (component e.projection e.flag) X Z).subgroupOf (generated X)

end SourceData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
