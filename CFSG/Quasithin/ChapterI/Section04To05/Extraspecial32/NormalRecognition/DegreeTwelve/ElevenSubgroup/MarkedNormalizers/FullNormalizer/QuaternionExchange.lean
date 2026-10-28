module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.Exchange
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.Conjugation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedFacts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedRootGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.RootAction

/-!
# Assembly of the two marked four-group exchanges

A quaternion element fixes the pivot b, inverts its square root w, sends
z to zb, and sends u to uw or uwb. Direct multiplication then exchanges
⟨b, uwz⟩ and ⟨b, uz⟩, in either case. This is left conjugation throughout.

The first relative normalizer is calculated in `MarkedFacts`. Conjugation
transports it to the second; the order 48 of the marked triple-transposition
centralizer proves equality there too. The final consumer constructs the
exact `FourNormalizerExchangeData` from the two local constructions.
`nonempty_fourNormalizerExchangeData` discharges both constructions from
the source hypotheses and the supplied marking, for either choice of u.
No normalization of S is assumed.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.8 and its preceding 4.6 calculation, p.41.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} {s : SymmetricSixData h a}

/-- The multiplication calculation applies to the literal marked subgroups. -/
theorem MarkedGeometry.exchanges_evenFusion (p : MarkedGeometry s)
    (c : RootConjugator p.toRootData) (d : FusionEightData z) :
    (s.evenFusion z).map (MulAut.conj c.y).toMonoidHom = s.evenFusion (z * p.b) ∧
    (s.evenFusion (z * p.b)).map (MulAut.conj c.y).toMonoidHom = s.evenFusion z := by
  rw [p.even_z, p.even_t]
  exact c.exchanges_generated d

omit [Finite G] in
private theorem map_relative_normalizer (e : G ≃* G) (x : G) (U : Subgroup G) :
    (Centralizer x ⊓ normalizer (U : Set G)).map e.toMonoidHom =
      Centralizer (e x) ⊓ normalizer (U.map e.toMonoidHom : Set G) := by
  rw [map_inf _ _ _ e.injective, map_equiv_normalizer_eq]
  have hc : (Centralizer x).map e.toMonoidHom = Centralizer (e x) := by
    apply le_antisymm
    · rintro g ⟨b, hb, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change e b * e x = e x * e b
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hb)
    · intro g hg
      refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hg
  rw [hc]

/-- Transport of the relative normalizer, followed by the marked order 48
calculation, supplies the second source identity. -/
theorem MarkedGeometry.centralizer_t (p : MarkedGeometry s)
    (c : RootConjugator p.toRootData) (d : FusionEightData z) :
    s.S ⊓ Centralizer (z * p.b) =
      Centralizer (z * p.b) ⊓ normalizer (s.evenFusion (z * p.b) : Set G) := by
  have hm : (Centralizer z ⊓ normalizer (s.evenFusion z : Set G)).map
      (MulAut.conj c.y).toMonoidHom =
      Centralizer (z * p.b) ⊓ normalizer (s.evenFusion (z * p.b) : Set G) := by
    rw [map_relative_normalizer, MulAut.conj_apply, c.conjugates_z,
      (p.exchanges_evenFusion c d).1]
  have hc : Nat.card (Centralizer (z * p.b) ⊓
      normalizer (s.evenFusion (z * p.b) : Set G) : Subgroup G) = 48 := by
    rw [← hm, card_map_of_injective (MulAut.conj c.y).injective,
      ← s.centralizer_z_eq_relative_normalizer d, s.centralizer_z_card]
  apply eq_of_le_of_card_ge (s.centralizer_le_relative_normalizer (z * p.b))
  rw [hc, s.centralizer_triple_card _ p.t_mem p.t_cycleType]

/-- This is a consumer of the two local calculations, not their existence
assertion. It discharges every field of the published exchange contract. -/
def MarkedGeometry.fourNormalizerExchangeData (p : MarkedGeometry s)
    (c : RootConjugator p.toRootData) (d : FusionEightData z) :
    FourNormalizerExchangeData s where
  t := z * p.b
  t_mem := p.t_mem
  t_cycleType := p.t_cycleType
  centralizer_z := s.centralizer_z_eq_relative_normalizer d
  centralizer_t := p.centralizer_t c d
  generated := p.generated
  y := c.y
  conjugates_z := c.conjugates_z
  conjugates_t := c.conjugates_t d
  exchanges_z := (p.exchanges_evenFusion c d).1
  exchanges_t := (p.exchanges_evenFusion c d).2

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} {s : SymmetricSixData h a}

/-- Conditional final assembly. The geometry and root-conjugator producers
must both be supplied before this establishes the existence in source 4.8. -/
theorem fourNormalizerExchangeData_of_root_calculations (d : FusionEightData z)
    (hp : Nonempty (QuaternionExchange.MarkedGeometry s))
    (hc : ∀ r : QuaternionExchange.RootData s,
      Nonempty (QuaternionExchange.RootConjugator r)) :
    Nonempty (FourNormalizerExchangeData s) := by
  obtain ⟨p⟩ := hp
  obtain ⟨c⟩ := hc p.toRootData
  exact ⟨p.fourNormalizerExchangeData c d⟩

/-- The quaternion exchange in source 4.8: the two literal even fusion
four-groups have the prescribed relative normalizers generating S, and
one ambient element exchanges both groups and their marked involutions
by left conjugation. The root geometry and conjugator are constructed
from the source hypotheses, including either permitted choice of u. -/
theorem nonempty_fourNormalizerExchangeData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) (s : SymmetricSixData h a) :
    Nonempty (FourNormalizerExchangeData s) :=
  fourNormalizerExchangeData_of_root_calculations d
    (QuaternionExchange.nonempty_markedGeometry h hn d a s)
    (fun r => r.nonempty_rootConjugator hn d)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
end
