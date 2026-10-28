module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.Exchange
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SymmetricRestriction

/-!
# The compatible full normalizer from the quaternion exchange

The literal normalizer acts on S, then on its characteristic A₆. Restriction
is faithful, and its preimage of the natural S₆ is exactly S. The index-two
calculation for Aut(A₆) therefore identifies the full image as soon as the
normalizer contains an element outside S. All maps agree with the original
marking on every element of S.

The local exchange contract supplies such an element by interchanging the
two relative four-group normalizers that generate S. A transposition is
sent to a product of three transpositions, so the element lies outside S.
The final theorem constructs the exchange from the source hypotheses using
`QuaternionExchange`, discharging the local premise and completing Lemma 4.8
for the supplied marked symmetric subgroup.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.8, p.41.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
namespace SymmetricSixData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} (s : SymmetricSixData h a)

/-- The actual normalizer action, transported through the marked isomorphism
and restricted to the characteristic alternating subgroup. -/
def alternatingNormalizerAction : normalizer (s.S : Set G) →*
    AlternatingSix.ShadowLocal.AutA6 :=
  AlternatingSix.ShadowLocal.symmetricRestriction.comp
    ((MulAut.congr s.equiv).toMonoidHom.comp s.S.normalizerMonoidHom)

theorem alternatingNormalizerAction_on_s (x : s.S) :
    s.alternatingNormalizerAction ⟨x, s.S.le_normalizer x.property⟩ =
      AlternatingSix.ShadowLocal.permutationAction (s.equiv x) := by
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  change s.equiv (x * s.equiv.symm q * x⁻¹) =
    s.equiv x * (q : Equiv.Perm (Fin 6)) * (s.equiv x)⁻¹
  rw [map_mul, map_mul, map_inv, s.equiv.apply_symm_apply]

theorem alternatingNormalizerAction_injective (d : FusionEightData z) :
    Function.Injective s.alternatingNormalizerAction :=
  AlternatingSix.ShadowLocal.symmetricRestriction_injective.comp
    ((MulAut.congr s.equiv).injective.comp (s.normalizerAction_injective d))

theorem natural_le_alternatingNormalizerAction_range :
    AlternatingSix.ShadowLocal.natural ≤ s.alternatingNormalizerAction.range := by
  rintro _ ⟨p, rfl⟩
  refine ⟨⟨s.equiv.symm p, s.S.le_normalizer (s.equiv.symm p).property⟩, ?_⟩
  rw [s.alternatingNormalizerAction_on_s, s.equiv.apply_symm_apply]
  rfl

/-- The preimage of the natural S₆ is exactly the original marked subgroup. -/
theorem alternatingNormalizerAction_mem_natural_iff (d : FusionEightData z)
    (y : normalizer (s.S : Set G)) :
    s.alternatingNormalizerAction y ∈ AlternatingSix.ShadowLocal.natural ↔
      (y : G) ∈ s.S := by
  constructor
  · rintro ⟨p, hp⟩
    have he : s.alternatingNormalizerAction
        ⟨s.equiv.symm p, s.S.le_normalizer (s.equiv.symm p).property⟩ =
        s.alternatingNormalizerAction y := by
      rw [s.alternatingNormalizerAction_on_s, s.equiv.apply_symm_apply]
      exact hp
    have hy := congrArg Subtype.val (s.alternatingNormalizerAction_injective d he)
    exact hy ▸ (s.equiv.symm p).property
  · intro hy
    refine ⟨s.equiv ⟨y, hy⟩, ?_⟩
    exact (s.alternatingNormalizerAction_on_s ⟨y, hy⟩).symm

/-- This discharges the full image and marking once the source quaternion
calculation has produced a normalizing element outside S. -/
theorem symmetricNormalizerData_of_outside (d : FusionEightData z)
    (y : G) (hy : y ∈ normalizer (s.S : Set G)) (hyS : y ∉ s.S) :
    Nonempty (SymmetricNormalizerData s) := by
  have hlt : AlternatingSix.ShadowLocal.natural < s.alternatingNormalizerAction.range := by
    apply lt_of_le_of_ne s.natural_le_alternatingNormalizerAction_range
    intro he
    apply hyS
    apply (s.alternatingNormalizerAction_mem_natural_iff d ⟨y, hy⟩).mp
    rw [he]
    exact ⟨⟨y, hy⟩, rfl⟩
  have hr := AlternatingSix.ShadowLocal.eq_top_of_natural_lt hlt
  let e := MulEquiv.ofBijective s.alternatingNormalizerAction
    ⟨s.alternatingNormalizerAction_injective d, MonoidHom.range_eq_top.mp hr⟩
  exact ⟨⟨e, s.alternatingNormalizerAction_on_s⟩⟩

end SymmetricSixData

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} {s : SymmetricSixData h a}

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

namespace FourNormalizerExchangeData

variable (c : FourNormalizerExchangeData s)

theorem map_centralizer_z :
    (s.S ⊓ Centralizer z).map (MulAut.conj c.y).toMonoidHom =
      s.S ⊓ Centralizer c.t := by
  rw [c.centralizer_z, map_relative_normalizer, MulAut.conj_apply,
    c.conjugates_z, c.exchanges_z, ← c.centralizer_t]

theorem map_centralizer_t :
    (s.S ⊓ Centralizer c.t).map (MulAut.conj c.y).toMonoidHom =
      s.S ⊓ Centralizer z := by
  rw [c.centralizer_t, map_relative_normalizer, MulAut.conj_apply,
    c.conjugates_t, c.exchanges_t, ← c.centralizer_z]

/-- Exchanging the two local normalizers normalizes their generated subgroup. -/
theorem y_normalizes : c.y ∈ normalizer (s.S : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change s.S.map (MulAut.conj c.y).toMonoidHom = s.S
  conv_lhs => rw [← c.generated]
  rw [Subgroup.map_sup, c.map_centralizer_z, c.map_centralizer_t, sup_comm, c.generated]

/-- Inner conjugation cannot carry the marked transposition to three 2-cycles. -/
theorem y_not_mem : c.y ∉ s.S := by
  intro hy
  let yS : s.S := ⟨c.y, hy⟩
  let zS : s.S := ⟨z, s.z_mem⟩
  let tS : s.S := ⟨c.t, c.t_mem⟩
  have he : yS * zS * yS⁻¹ = tS := Subtype.ext c.conjugates_z
  have hp : s.equiv yS * s.equiv zS * (s.equiv yS)⁻¹ = s.equiv tS := by
    rw [← map_inv, ← map_mul, ← map_mul, he]
  have ht : (s.equiv tS).cycleType = (s.equiv zS).cycleType := by
    rw [← hp, Equiv.Perm.cycleType_conj]
  rw [c.t_cycleType, Equiv.Perm.isSwap_iff_cycleType.mp s.z_swap] at ht
  have hc := congrArg Multiset.card ht
  norm_num at hc

/-- The local quaternion exchange supplies the full normalizer with the
prescribed action on the whole marked symmetric subgroup. -/
theorem symmetricNormalizerData (c : FourNormalizerExchangeData s) (d : FusionEightData z) :
    Nonempty (SymmetricNormalizerData s) :=
  s.symmetricNormalizerData_of_outside d c.y c.y_normalizes c.y_not_mem

end FourNormalizerExchangeData

/-- Source Lemma 4.8 for the supplied marked S₆: its literal ambient normalizer
is Aut(A₆), with the specified permutation action on every element of S.
The quaternion construction supplies the outer normalizing element; no
ambient normality of S or additional exchange witness is assumed. -/
theorem nonempty_symmetricNormalizerData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) (s : SymmetricSixData h a) :
    Nonempty (SymmetricNormalizerData s) := by
  obtain ⟨c⟩ := nonempty_fourNormalizerExchangeData h hn d a s
  exact c.symmetricNormalizerData d

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
