module

public import CFSG.Quasithin.Chapter10.SourceA5PointParabolicCenter
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import Theory.SpecificGroups.Triality.CentralLocalFixer

/-!
# The marked triality row in the A5 point-centralizer inspection

The arms local residual is excluded by the original moved module's core-center
bound. Fixing the central local residual is faithful on involutory automorphisms
of every perfect cover. The original conjugate moved elementary subgroup
normalizes the component because it centralizes its chosen vector. Thus it
centralizes the component, giving the common-centralizer alternative.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, with the genuine marked
parabolics of F.1.12. All images use the literal quotient by the component center.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Triality.Standard Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L I U : Subgroup G}

/-- An elementary actor fixing the actual marked central local subgroup
centralizes a perfect containing triality component. -/
theorem source_triality_central_local_component_centralized
    [Group.IsPerfect I] [IsElementaryAbelian 2 U]
    (n : ℕ) (hn : 0 < n) (eI : (I ⧸ center I) ≃* BinaryCarrier n hn)
    (hmark : (L.subgroupOf I).map
      (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        localFactor (binaryParameters n hn) .central)
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  intro u hu
  let z : normalizer (I : Set G) := ⟨u, hUN hu⟩
  let a : MulAut I := I.normalizerMonoidHom z
  have hz : z ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian u hu)
  have ha : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom z) ^ 2 = 1
    rw [← map_pow, hz, map_one]
  have he : a = 1 := by
    apply perfect_cover_central_local_involutory_fixer_eq_one n hn eI
      (L.subgroupOf I) hmark a ha
    intro l hl
    apply Subtype.ext
    change u * l.val * u⁻¹ = l.val
    exact mul_inv_eq_iff_eq_mul.mpr ((hUL hu l.val hl).symm)
  intro i hi
  have hh := congrArg (fun f : MulAut I => (f ⟨i, hi⟩ : G)) he
  change u * i * u⁻¹ = i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Both marked triality rows at q=4 force the required centralization;
the arms row is impossible by the original core-center bound. -/
theorem source_a5_triality_component_centralized
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLI : L ≤ I) [Group.IsPerfect I] [IsElementaryAbelian 2 U]
    (n : ℕ) (hn : 0 < n) (hq : 2 ^ n = 4)
    (eI : (I ⧸ center I) ≃* BinaryCarrier n hn)
    (hmark : (L.subgroupOf I).map
      (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        localFactor (binaryParameters n hn) .arms ∨
      (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        localFactor (binaryParameters n hn) .central)
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  rcases hmark with hmark | hmark
  · exact (source_a5_point_not_triality_arms_parabolic D e hLI
      (binaryParameters n hn) rfl (by simpa using hq) eI hmark).elim
  · exact source_triality_central_local_component_centralized n hn eI hmark hUN hUL

/-- The original point-centralizer hypotheses discharge normalization of the
conjugate moved module, and give the common alternative for triality. -/
theorem source_a5_point_triality_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    (I : Subgroup G) [Group.IsPerfect I] (hLI : L ≤ I)
    (n : ℕ) (hn : 0 < n) (hq : 2 ^ n = 4)
    (eI : (I ⧸ center I) ≃* BinaryCarrier n hn)
    (hmark : (L.subgroupOf I).map
      (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        localFactor (binaryParameters n hn) .arms ∨
      (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        localFactor (binaryParameters n hn) .central)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) :
    SourceA5PointComponentAlternative D e t I := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hUC : U ≤ centralizer ({v} : Set G) := by
    intro u hu y hy
    have he : y = v := Set.mem_singleton_iff.mp hy
    rw [he]
    exact U.le_centralizer hu v hv
  exact .common (source_a5_triality_component_centralized D e hLI n hn hq eI
    hmark (hUC.trans hNI) hcross)

end CFSG.Quasithin.Chapter10
