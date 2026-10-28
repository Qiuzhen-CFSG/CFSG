module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Modules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Residual
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The actual incident frame and the starred seed

The two parabolics are preimages of one incident matrix flag, embedded in
G_alpha by embedM. Their intrinsic two-cores, prime-to-two residual actors
L_delta, and ordered residuals Ltilde_delta are kept distinct. The full
actors are the parabolics in the binary case; the ordered residuals generate
the actual local component.

First-color starred layers are conjugates of the actual edgeStar. At a
second-color vertex the tilde starred layer is the sum of the two-core-fixed
subspaces of all adjacent first-color layers. All these subspaces live in
one literal LayerModule for V_alpha/Z_alpha. The preimage construction
recovers an ambient subgroup with the specified quotient image.

The compatibility and seed records below are conditional inputs, not
recognition certificates. In particular they contain no assertion about
the full orbit span or its quotient. Source: Meierfrankenfeld--Stellmacher,
Pushing up weak BN-pairs of rank two (1993), notation on pp.832, 905 and
(4.6.12)(3), pp.910--911.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
universe u
variable {M : Type u} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace LayerModule
variable {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)

/-- The full ambient preimage of a subspace under the literal relative quotient. -/
def preimage (A : Submodule (ZMod 2) d.Space) : Subgroup (FreeAmalgam R) :=
  ((A.toAddSubgroup.toSubgroup).comap d.projection).map S.subtype

/-- Membership remembers the actual element of S, not an abstract isomorphic quotient. -/
theorem mem_preimage_iff (A : Submodule (ZMod 2) d.Space) (x : FreeAmalgam R) :
    x ∈ d.preimage A ↔ ∃ hx : x ∈ S, (d.projection ⟨x, hx⟩).toAdd ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hx, hA⟩
    exact ⟨⟨x, hx⟩, hA, rfl⟩

/-- The preimage is an actual subgroup of the specified ambient layer. -/
theorem preimage_le (A : Submodule (ZMod 2) d.Space) : d.preimage A ≤ S :=
  map_subtype_le _

/-- Every preimage contains the exact relative Z_alpha kernel. -/
theorem inf_Z_le_preimage (A : Submodule (ZMod 2) d.Space) :
    Z R (alpha R) ⊓ S ≤ d.preimage A := by
  intro x hx
  apply (d.mem_preimage_iff A x).mpr
  refine ⟨hx.2, ?_⟩
  have hk : d.projection ⟨x, hx.2⟩ = 1 := by
    change (⟨x, hx.2⟩ : S) ∈ d.projection.ker
    rw [d.kernel]
    exact hx.1
  rw [hk]
  exact A.zero_mem

/-- Taking the quotient image recovers the subspace exactly. -/
theorem subspace_preimage (A : Submodule (ZMod 2) d.Space) :
    d.subspace (d.preimage A) = A := by
  ext v
  rw [d.mem_subspace_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx, hv⟩ := (d.mem_preimage_iff A x).mp hx
    exact hv
  · intro hv
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
    refine ⟨x, (d.mem_preimage_iff A x).mpr ⟨x.property, ?_⟩, ?_⟩
    · change (d.projection x).toAdd ∈ A
      rw [hx]
      exact hv
    · exact congrArg Multiplicative.toAdd hx

end LayerModule

namespace Seed

/-- One chosen incident flag, with a choice of which color is delta1. -/
structure Frame (source : LocalSource L R) where
  flag : SL
  first : Bool

namespace Frame
variable (f : Frame source)

/-- False labels delta1; true labels delta2. Both use the original projection. -/
def parabolic (i : Bool) : Subgroup M :=
  MS93.parabolic source.projection f.flag (if i then !f.first else f.first)

/-- The finite coset geometries of the two actual parabolic preimages. -/
abbrev Vertex (i : Bool) := M ⧸ f.parabolic i

/-- Incidence is a nonempty intersection of the two left cosets. -/
def Incident (x : f.Vertex false) (y : f.Vertex true) : Prop :=
  ∃ m : M, QuotientGroup.mk m = x ∧ QuotientGroup.mk m = y

/-- The parabolic as an actual subgroup of the amalgam. -/
def ambient (i : Bool) : Subgroup (FreeAmalgam R) := (f.parabolic i).map (embedM R)

/-- The intrinsic two-core, included in M before being embedded in the amalgam. -/
def core (i : Bool) : Subgroup M :=
  (pCore 2 (f.parabolic i)).map (f.parabolic i).subtype

/-- The source L_delta, before applying the two-residual. -/
def actor (i : Bool) : Subgroup M :=
  (primeToResidual 2 (f.parabolic i)).map (f.parabolic i).subtype

/-- The source Ltilde_delta, with the two residual operations in their printed order. -/
def residual (i : Bool) : Subgroup M := rankOne (f.parabolic i)

/-- The binary full rank-one actor is the whole parabolic, including the kernel. -/
theorem actor_eq [Finite M] (i : Bool) : f.actor i = f.parabolic i := by
  unfold actor parabolic
  rw [primeToResidual_parabolic_eq_top source.projection source.projection_surjective
    (by rw [source.projection_kernel]; exact pCore_isPGroup)]
  rw [← MonoidHom.range_eq_map]
  exact (f.parabolic i).range_subtype

/-- The actual image parabolic lies in the base vertex stabilizer. -/
theorem ambient_le (i : Bool) : f.ambient i ≤ stabilizer R (alpha R) := by
  rw [alpha, stabilizer_m_base]
  exact map_le_range (embedM R) _

/-- Core normality is relative to its parabolic. -/
theorem core_normalized (i : Bool) : f.parabolic i ≤ normalizer (f.core i) :=
  (f.parabolic i).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)

/-- The two ordered residuals generate the given local component. -/
theorem residual_sup [Finite M] : f.residual false ⊔ f.residual true = L := by
  have h := rankOne_parabolic_generation source.projection source.projection_surjective
    (by rw [source.projection_kernel]; exact pCore_isPGroup) f.flag
  cases hi : f.first <;>
    simpa only [residual, parabolic, hi, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, sup_comm, source.residual] using h

/-- The corresponding full parabolics generate M. -/
theorem parabolic_sup : f.parabolic false ⊔ f.parabolic true = ⊤ := by
  have h := parabolic_generation source.projection source.projection_surjective f.flag
  cases hi : f.first <;>
    simpa only [parabolic, hi, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, sup_comm] using h

end Frame

/-- First-color U_delta-star is a conjugate of the literal edge star. -/
noncomputable def firstStar (geometry : Geometry R) (m : M) : Subgroup (FreeAmalgam R) :=
  (edgeStar R geometry (alpha R) (beta R)).map
    (MulAut.conj (embedM R m)).toMonoidHom

/-- The first-color tilde layer is its image in V_alpha/Z_alpha. -/
noncomputable def firstTildeStar (d : LayerModule source (V R (alpha R))) (m : M) :
    Submodule (ZMod 2) d.Space := d.subspace (firstStar geometry m)

/-- The core at the second-color vertex represented by m. -/
def secondCore (f : Frame source) (m : M) : Subgroup M :=
  (f.core true).map (MulAut.conj m).toMonoidHom

/-- The source second-color layer: span the Q_delta-fixed spaces in the
adjacent first-color starred layers, all modulo the same Z_alpha. -/
noncomputable def secondTildeStar (d : LayerModule source (V R (alpha R)))
    (f : Frame source) (m : M) : Submodule (ZMod 2) d.Space :=
  ⨆ p : f.parabolic true,
    firstTildeStar (geometry := geometry) d (m * p) ⊓
      fixedSpace d.representation ((secondCore f m).map source.projection)

/-- Explicit geometric flag-selection obligations, to be discharged by the
source assembly. The normalization identity makes firstStar independent of
the representative of a first-color coset. -/
structure Compatible (f : Frame source) (s : CriticalSegment geometry) : Prop where
  first_core : (f.core false).map (embedM R) = Q R (beta R)
  first_star_normalized : f.ambient false ≤ normalizer (edgeStar R geometry (alpha R) (beta R))
  endpoint_selected : ¬ Z R s.endpoint ⊓ (f.core true).map (embedM R) ≤ Q R (alpha R)

/-- Linear commutators in a subspace, for the actual supplied quotient action. -/
noncomputable def movedSpace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL W) (H : Subgroup SL) (A : Submodule (ZMod 2) W) :
    Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {w | ∃ h ∈ H, ∃ v ∈ A, ρ h v - v = w}

/-- Precisely the tilde seed premises in (4.6.12)(3), together with its
literal ambient preimage. There is no full-span or recognition premise. -/
structure Input (d : LayerModule source (V R (alpha R)))
    (f : Frame source) (c : Vertex R) where
  space : Submodule (ZMod 2) d.Space
  le_star : space ≤ secondTildeStar (geometry := geometry) d f 1
  normalized : ∀ m ∈ f.parabolic true, ∀ v ∈ space,
    d.representation (source.projection m) v ∈ space
  nonzero : space ≠ ⊥
  moved : movedSpace d.representation ((f.actor true).map source.projection) space = space
  preimage_le : d.preimage space ≤ Q R c

end Seed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
