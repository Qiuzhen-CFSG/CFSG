module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessSaturation
/-!
# Compatible M24 pairs in the original three-space normalizer

A three-space contained in V and normalized by the original H is contained
in both members of every internal conjugate pair selected in H. The genuine
E.2 actor identity gives dim(Z) + k + dim(A/C_A(V)) = 11, while the native
rank-one models give dim(A/C_A(V)) >= 2k. Thus k <= 2. The original weak
closure minimum w = 2 gives the reverse inequality and identifies the core
actor with the whole offender normalizer. Since n(H) = 2, this also proves
the divisibility clause needed by the original Selected interface.

NonFFSourceMathieuM24Pair constructs all inputs on the chosen orbit and
identifies this intersection with the same original three-space. No degree
bound or pair containment is assumed by that consumer.
Source: Aschbacher--Smith E.2.13--14, 8.2.2--5, printed pp.224--228,714--717,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I U : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

omit [Finite G] in
/-- An internal conjugator preserves every H-invariant subgroup of V. -/
theorem invariant_le_intersection
    (s : GeometricSelected H T M V I k i S)
    (hUV : U ≤ V) (hHU : H ≤ normalizer (U : Set G)) :
    U ≤ V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  have he : U.map (MulAut.conj i.val⁻¹).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (hHU (H.inv_mem (s.family.le_ambient i.property)))
  exact le_inf hUV (he ▸ map_mono (f := (MulAut.conj i.val⁻¹).toMonoidHom) hUV)

/-- The original three-space forces the actual model degree to be two. -/
theorem parameter_eq_two_of_invariant_three_space
    (s : GeometricSelected H T M V I k i S)
    (hT : HypothesisE322 V T) (hw : globalW V T = 2)
    (hV : rank V = 11) (hU : rank U = 3)
    (hUV : U ≤ V) (hHU : H ≤ normalizer (U : Set G)) : k = 2 := by
  have hlo := (s.core_actor_data hT).2.2.2.2
  rw [hw] at hlo
  have hlo' : 2 ≤ k := by exact_mod_cast hlo
  have hle : rank U ≤ rank (V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :=
    Nat.log_mono_right (card_le_of_le (invariant_le_intersection s hUV hHU))
  have hid := s.actor_rank_identity
  have hrank := s.actor_rank_ge_twice_parameter
  rw [hV] at hid
  rw [hU] at hle
  omega

/-- The selected core actor attains the weak-closure minimum in the same H. -/
theorem compatible_offender
    (s : GeometricSelected H T M V I k i S)
    (hT : HypothesisE322 V T) (hw : globalW V T = 2)
    (hV : rank V = 11) (hU : rank U = 3)
    (hUV : U ≤ V) (hHU : H ≤ normalizer (U : Set G))
    (hn : generationParameter H = 2) :
    Selected H T M V I 2 i S ∧ IsWOffenderAt V T i.val⁻¹ ∧
      offenderNormalizer V i.val⁻¹ =
        V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      offenderNormalizer V i.val⁻¹ ≤ T ∧
      offenderNormalizer V i.val⁻¹ ⊓ centralizer (V : Set G) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U ≤ V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  have hk := parameter_eq_two_of_invariant_three_space s hT hw hV hU hUV hHU
  subst k
  obtain ⟨_,ho,ha,ht,hz⟩ := s.offender_of_parameter_bound hT (by rw [hw]; rfl)
  exact ⟨s.toSelected (hn ▸ dvd_rfl),ho,ha,ht,hz,invariant_le_intersection s hUV hHU⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
