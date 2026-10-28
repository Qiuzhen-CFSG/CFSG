module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.SourceData
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.ModelTransport

/-!
# Intrinsic layers for the fixed-seed argument

The source group V_I is the conjugate closure of Z in the actual overgroup H.
The block layer is the embedded intrinsic commutator [O₂(L),L]. The cubic
actor condition identifies conjugation by an element of X with conjugation
by an element of L having order three modulo O₂(L). No seed-centrality
conclusion is included in these definitions.

Source: Aschbacher–Smith, proof of 15.4.20, printed p.1164, and C.1.7.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
open Subgroup ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}

/-- The literal conjugate closure of the source omega subgroup in H. -/
def seedClosure (c : ContraryData κ d i j) : Subgroup G :=
  (normalClosure (d.Z.subgroupOf c.H : Set c.H)).map c.H.subtype

/-- The intrinsic block commutator layer, embedded in G. -/
def firstLayer {c : ContraryData κ d i j} (b : ExchangedBlock c) : Subgroup G :=
  (blockU b.first).map b.first.subtype

/-- A marked source actor with a genuine cubic coordinate on the first block. -/
def HasCubicActor (c : ContraryData κ d i j) (b : ExchangedBlock c) : Prop :=
  ∃ (x : d.wholeX) (l : b.first),
    orderOf (QuotientGroup.mk' (pCore 2 b.first) l) = 3 ∧
    ∀ u : blockU b.first,
      (x : G) * ((u : b.first) : G) * (x : G)⁻¹ =
        ((blockConjugate b.first l u : b.first) : G)

variable (c : ContraryData κ d i j)

lemma Z_le_H : d.Z ≤ c.H :=
  c.Z_le_U.trans (c.sylow_image ▸ map_subtype_le (c.sylow : Subgroup c.H))

lemma Z_le_seedClosure : d.Z ≤ seedClosure c := by
  intro z hz
  exact ⟨⟨z, Z_le_H c hz⟩, le_normalClosure hz, rfl⟩

lemma seedClosure_le_H : seedClosure c ≤ c.H := map_subtype_le _

lemma normalizes_seedClosure : c.H ≤ normalizer (seedClosure c : Set G) := by
  apply le_normalizer_iff.mpr
  intro h hh v hv
  obtain ⟨v, hv, rfl⟩ := hv
  exact ⟨(⟨h, hh⟩ : c.H) * v * (⟨h, hh⟩ : c.H)⁻¹,
    (normalClosure_normal (s := (d.Z.subgroupOf c.H : Set c.H))).conj_mem v hv ⟨h, hh⟩,
    rfl⟩

lemma firstLayer_le_first (b : ExchangedBlock c) : firstLayer b ≤ b.first :=
  map_subtype_le _

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
