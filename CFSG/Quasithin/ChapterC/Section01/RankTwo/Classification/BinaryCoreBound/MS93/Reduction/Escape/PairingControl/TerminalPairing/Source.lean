module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Quotient

/-!
# The actual local inputs to the terminal dual pairing

At c = alpha'-2 the groups for (1.7) are Z = U_c, W = Q_c and
U = Vcirc_c. The seed is the full inverse image, in Vcirc_c, of the
line fixed by a marked parabolic on the dual quotient Vcirc_c/U_c.
It is a subgroup of the finite stabilizer G_c. The extension uses the
same projection as both opposite sections and its kernel is exactly Q_c.

Two constructions remain distinct. `EdgeSeedAt` identifies a parabolic
whose seed lies in the actual V_t and has commutator of order at most four
with Q_c. That smallness condition is not a consequence of opposite module
coordinates alone. `CorePairing` supplies the remaining source
conditions and the natural factor on the intrinsic centralizer quotient.
These are intermediate targets, with no constructors assumed here. Their
producers are required before the terminal application proves (4.3.2).

Source: Meierfrankenfeld--Stellmacher (1993), (1.7), pp.847--848,
and the final paragraph of (4.3.2), pp.885--886.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
open RankOnePairing

section FinitePairing
variable {A : Type*} [Group A]

/-- The full preimage of the parabolic-fixed line, including its actual
kernel Z. This definition does not assume that it lies in an edge layer. -/
def canonicalSeed (e : Extension (M := A)) {J Z : Subgroup A}
    {z : NaturalFactor e.projection ⊤ Z ⊥}
    (o : DualFactor e.projection ⊤ J Z Z z) (i : Bool) : Subgroup A :=
  ((Incidence.DualGeometry.seedLine z.marking e.flag i).comap o.coordinates).map J.subtype

theorem canonicalSeed_le (e : Extension (M := A)) {J Z : Subgroup A}
    {z : NaturalFactor e.projection ⊤ Z ⊥}
    (o : DualFactor e.projection ⊤ J Z Z z) (i : Bool) :
    canonicalSeed e o i ≤ J := map_subtype_le _

theorem le_canonicalSeed (e : Extension (M := A)) {J Z : Subgroup A}
    {z : NaturalFactor e.projection ⊤ Z ⊥}
    (o : DualFactor e.projection ⊤ J Z Z z) (i : Bool) (hZ : Z ≤ J) :
    Z ≤ canonicalSeed e o i := by
  intro x hx
  refine ⟨⟨x, hZ hx⟩, ?_, rfl⟩
  have hk : (⟨x, hZ hx⟩ : J) ∈ o.coordinates.ker := by rw [o.kernel]; exact hx
  change o.coordinates ⟨x, hZ hx⟩ ∈ Incidence.DualGeometry.seedLine z.marking e.flag i
  rw [show o.coordinates ⟨x, hZ hx⟩ = 1 from hk]
  exact one_mem _

/-- The finite pairing construction must prove every source premise,
generation of J, and the additional natural-centralizer-factor hypothesis.
No commutator conclusion of (1.7) is a field. -/
structure CorePairing [Finite A] (e : Extension (M := A)) {J Z : Subgroup A}
    [Z.Normal] {z : NaturalFactor e.projection ⊤ Z ⊥}
    (o : DualFactor e.projection ⊤ J Z Z z) (i : Bool) where
  data : SourceData e i Z (extensionCore e.projection) (canonicalSeed e o i)
  generated_eq : generated (canonicalSeed e o i) = J
  natural_quotient : NaturalFactor e.projection (component e.projection e.flag)
    (generated (canonicalSeed e o i)) (centralizer (extensionCore e.projection : Set A))

end FinitePairing

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

local instance vertex_finite (a : Vertex R) : Finite (stabilizer R a) := finite_stabilizer R a

/-- Relative normality of the literal natural subgroup, inside G_a. -/
instance natural_normal (a : Vertex R) :
    ((U R a).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (U_normalized a)

/-- The extension lives in G_a, using the marking of the actual opposite
sections. Its flag may be selected to match the incident edge. -/
noncomputable def vertexExtension (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (o : OppositeSectionAt a)
    (flag : SL) (hflag : BinaryWeakBN flag) : Extension (M := stabilizer R a) :=
  FirstPairing.twoGroupExtension o.projection o.surjective
    (by rw [o.kernel]; exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype)
    flag hflag

@[simp] theorem vertexExtension_projection (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (o : OppositeSectionAt a)
    (flag : SL) (hflag : BinaryWeakBN flag) :
    (vertexExtension source a ha o flag hflag).projection = o.projection := rfl

theorem vertexExtension_core (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (o : OppositeSectionAt a)
    (flag : SL) (hflag : BinaryWeakBN flag) :
    extensionCore (vertexExtension source a ha o flag hflag).projection =
      (Q R a).subgroupOf (stabilizer R a) := by
  rw [vertexExtension_projection, FirstPairing.extensionCore_eq_kernel, o.kernel]
  rw [o.kernel]
  exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype

/-- The source local normalizers are the full parabolic preimages here,
as proved from the actual two-group kernel. -/
theorem vertexExtension_parabolic (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (o : OppositeSectionAt a)
    (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool) :
    localParabolic (vertexExtension source a ha o flag hflag) i =
      parabolic o.projection flag i := by
  apply localParabolic_eq_parabolic
  change IsPGroup 2 o.projection.ker
  rw [o.kernel]
  exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype

/-- The geometric obligation: select a marked parabolic of the orientation
with no fixed points on U_a and place its actual dual seed in V_t. -/
structure EdgeSeedAt (source : LocalSource L R) (a t : Vertex R)
    (ha : color R a = false) where
  opposite : OppositeSectionAt a
  flag : SL
  weakBN : BinaryWeakBN flag
  side : Bool
  fixed_bot : (U R a).subgroupOf (stabilizer R a) ⊓
    centralizer (localResidual
      (localParabolic (vertexExtension source a ha opposite flag weakBN) side) :
        Set (stabilizer R a)) = ⊥
  seed_le_edge : canonicalSeed (vertexExtension source a ha opposite flag weakBN)
    opposite.dual side ≤ (V R t).subgroupOf (stabilizer R a)
  small_commutator : Nat.card
    (⁅canonicalSeed (vertexExtension source a ha opposite flag weakBN) opposite.dual side,
      (Q R a).subgroupOf (stabilizer R a)⁆ : Subgroup (stabilizer R a)) ≤ 4

namespace EdgeSeedAt
variable {source : LocalSource L R} {a t : Vertex R} {ha : color R a = false}

/-- The extension and all source subgroups share the section's marking. -/
noncomputable abbrev extension (s : EdgeSeedAt source a t ha) :
    Extension (M := stabilizer R a) :=
  vertexExtension source a ha s.opposite s.flag s.weakBN

/-- The remaining finite algebra obligation for the selected geometric seed. -/
abbrev Pairing (s : EdgeSeedAt source a t ha) := CorePairing s.extension s.opposite.dual s.side

end EdgeSeedAt
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
