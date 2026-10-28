module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.Contracts

/-!
# The two marked four-groups in the quaternion exchange

The even part is the literal inverse image of A₆ under the supplied marking
of S, embedded back into G. Intersecting it with A(x) gives the four-groups
used in Aschbacher's Lemma 4.8. Their normalizers are relative to C_G(x).

`FourNormalizerExchangeData` isolates the local geometric calculation: the
two relative normalizers are C_S(z) and C_S(t), they generate S, and an
ambient element exchanges both their distinguished involutions and their
marked four-groups. Its existence is not asserted here. In the source this
element is constructed in a quaternion subgroup of Q_a, with t = za.
Neither normalization of S nor an automorphism-group identification is a
field of the contract. `FullNormalizer` derives both, with the exact marking.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.8 and the preceding 4.6 calculation, p.41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

namespace SymmetricSixData

/-- The original embedded alternating subgroup, using the supplied S₆ marking. -/
@[expose] public def markedAlternating (s : SymmetricSixData h a) : Subgroup G :=
  ((alternatingGroup (Fin 6)).comap s.equiv.toMonoidHom).map s.S.subtype

/-- The source's A(x) ∩ E(S), with the literal canonical fusion subgroup. -/
@[expose] public def evenFusion (s : SymmetricSixData h a) (x : G) : Subgroup G :=
  fusionCore x ⊓ s.markedAlternating

end SymmetricSixData

/-- Local identities to be supplied by the quaternion calculation of 4.8.
Conjugation is left conjugation in every field. -/
public structure FourNormalizerExchangeData (s : SymmetricSixData h a) where
  t : G
  t_mem : t ∈ s.S
  t_cycleType : (s.equiv ⟨t, t_mem⟩).cycleType = {2, 2, 2}
  centralizer_z : s.S ⊓ Centralizer z =
    Centralizer z ⊓ normalizer (s.evenFusion z : Set G)
  centralizer_t : s.S ⊓ Centralizer t =
    Centralizer t ⊓ normalizer (s.evenFusion t : Set G)
  generated : (s.S ⊓ Centralizer z) ⊔ (s.S ⊓ Centralizer t) = s.S
  y : G
  conjugates_z : y * z * y⁻¹ = t
  conjugates_t : y * t * y⁻¹ = z
  exchanges_z : (s.evenFusion z).map (MulAut.conj y).toMonoidHom = s.evenFusion t
  exchanges_t : (s.evenFusion t).map (MulAut.conj y).toMonoidHom = s.evenFusion z

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
