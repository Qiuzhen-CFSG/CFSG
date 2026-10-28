module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalFixedCore

/-!
# The elementary quotient of the original core by its fixed line

The original fixed subgroup C_V(L) is central in Q. The A8-block
commutator identity [Q,L]=V, together with V central and elementary in Q,
makes every square of Q centralize L. The proved C_T(L)=C_V(L) thus
puts every square in this same fixed line. Hence the literal quotient
Q/C_V(L) is elementary abelian, with no elementary hypothesis on Q.

This prepares the quotient representation required for C.1.13(b)'s
cohomological upper bound in the conclusion of12.6.2. The upper bound
and extension classification still require proof. Source: Aschbacher--Smith,
C.1.13(a,b), printed pp.124--125, and12.6.2, printed p.828, combined
manuscript of1 March2004. Neither12.6.2 nor12.6.23 is asserted here.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section06
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- The original fixed subgroup is central, and hence normal, in the original Q. -/
theorem SourceHypothesis.original_fixed_normal_in_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V) :
    ((ZV L V).subgroupOf (Q T L)).Normal := by
  exact normal_subgroupOf_of_le_normalizer
    ((H.chosen.core_centralizes.trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _))

/-- The original core squares lie in the original fixed line, by the block
commutator identity and the proved full Sylow-centralizer equality. -/
theorem SourceHypothesis.original_core_square_mem_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hs : ChapterC.IsShort L)
    (hct : (T : Subgroup G) ⊓ centralizer (L : Set G) = ZV L V)
    (q : G) (hq : q ∈ Q T L) : q^2 ∈ ZV L V := by
  rw [←hct]
  refine ⟨(T : Subgroup G).pow_mem (((Q_le_Tv H.chosen (1 : V)).trans inf_le_left hq)) 2,?_⟩
  intro l hl
  let c := l*q*l⁻¹*q⁻¹
  have hc : c ∈ V := by
    rw [←H.original_core_commutator_of_short hs,commutator_comm]
    exact commutator_mem_commutator hl hq
  have hqc : Commute c q := H.chosen.core_centralizes hq c hc
  have hc2 : c^2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc
  have he : (l*q*l⁻¹)^2 = q^2 := by
    calc
      (l*q*l⁻¹)^2 = (c*q)^2 := by congr 1; dsimp [c]; group
      _ = c^2*q^2 := hqc.mul_pow 2
      _ = q^2 := by rw [hc2,one_mul]
  calc
    l*q^2 = (l*q*l⁻¹)^2*l := by simp only [pow_two]; group
    _ = q^2*l := by rw [he]

/-- The cohomology argument uses the elementary quotient of the original Q
by the original C_V(L), with its literal quotient projection. -/
theorem SourceHypothesis.core_fixed_quotient_elementary_of_nonsingular_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    letI := H.original_fixed_normal_in_core
    IsElementaryAbelian 2 ((Q T L) ⧸ (ZV L V).subgroupOf (Q T L)) := by
  let := H.original_fixed_normal_in_core
  obtain ⟨hct,_⟩ := H.sylow_centralizer_eq_fixed_of_nonsingular_escape D hTV hTI hz v hv he
  obtain ⟨_,hL,_⟩ := H.exists_preferred_nonsingular_original_blocks_of_fixed D hTV hTI hz v hv he
  have hsquare (x : (Q T L) ⧸ (ZV L V).subgroupOf (Q T L)) : x^2 = 1 := by
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective ((ZV L V).subgroupOf (Q T L)) x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (H.original_core_square_mem_fixed hL.2.1 hct q q.property)
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsquare x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
end CFSG.Quasithin.Chapter12.Section06
