module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Frattini
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.InvolutionGeneration
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.PSL3Two.ElementaryEightAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Constructing the natural core quotient from local group estimates

Conjugation on the actual central quotient core/U descends through the given
SL₃(2) projection once [core,Q] lies in U. The quotient is abelian by that
containment; involution generation makes it elementary abelian. The local
order calculation |core| = 64 then gives |core/U| = 8. Residual commutator
idempotence and simplicity make the descended action faithful. A basis of
the quotient constructs its independent automorphism marking.

The theorem proves the quotient map, its surjectivity, exact kernel and
ambient action formula. The order and commutator bounds remain explicit
inputs. Their derivation from b = 2 and the non-Frattini premise is required
before this is the source construction. The distance-two corollary supplies
involution generation from the actual critical pair.
Neither core commutativity nor a common marking with U is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), natural branch of (3.6), printed pp.870--871, using (3.3)--(3.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The actual quotient with its independent natural marking, conditional
only on the three local group estimates still needed from the source argument. -/
theorem exists_naturalCoreQuotient_of_order_and_commutator
    (source : LocalSource L R) (geometry : Geometry R) (hb : 0 < geometry.b R)
    (natural : NaturalU R source.projection)
    (hcard : Nat.card (core R (alpha R)) = 64)
    (hcomm : ⁅core R (alpha R), Q R (alpha R)⁆ ≤ U R (alpha R))
    (hgen : closure {x : core R (alpha R) | x ^ 2 = 1} = ⊤) :
    Nonempty (NaturalCoreQuotient source) := by
  let C := core R (alpha R)
  let N := (U R (alpha R)).subgroupOf C
  let : Finite C := finite_core (alpha R)
  let : N.Normal := U_subgroupOf_core_normal (alpha R) rfl
  let D := C ⧸ N
  let q : C →* D := QuotientGroup.mk' N
  have hderived : _root_.commutator C ≤ N := by
    intro x hx
    have hh := mem_map_of_mem C.subtype hx
    rw [map_subtype_commutator] at hh
    exact hcomm (commutator_mono le_rfl (core_le_Q (alpha R)) hh)
  let : IsMulCommutative D := Normal.quotient_commutative_iff_commutator_le.mpr hderived
  have hpow (x : C) : q x ^ 2 = 1 := by
    have hx : x ∈ closure {x : C | x ^ 2 = 1} := hgen.symm ▸ mem_top x
    induction hx using closure_induction with
    | mem y hy => rw [← map_pow, hy, map_one]
    | one => simp
    | mul y z _ _ hy hz => rw [map_mul, mul_pow, hy, hz, one_mul]
    | inv y _ hy => rw [map_inv, inv_pow, hy, inv_one]
  let : IsElementaryAbelian 2 D := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      exact hpow y) }
  have hU : Nat.card (U R (alpha R)) = 8 := by
    rw [Nat.card_congr natural.equiv.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fun]
  have hN : Nat.card N = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (U_le_core geometry hb (alpha R) rfl)).toEquiv).trans hU
  have hD : Nat.card D = 8 := by
    have h := N.card_mul_index
    rw [hN, hcard, index_eq_card] at h
    change 8 * Nat.card D = 64 at h
    omega
  let P := Mbar R
  have hPC : P ≤ normalizer C := by
    simpa only [P, C, alpha, stabilizer_m_base] using core_normalized (R := R) (alpha R)
  obtain ⟨a, ha⟩ := exists_quotient_conjugation_action P C (U R (alpha R))
    hPC natural.normalized inferInstance
  let i : M →* P := (embedM R).rangeRestrict
  let aM : M →* MulAut D := a.comp i
  have hkill : source.projection.ker ≤ aM.ker := by
    intro m hm
    have hmQ : embedM R m ∈ Q R (alpha R) := by
      rw [Q_alpha R source.two_group source.core_le]
      exact mem_map_of_mem _ (source.projection_kernel ▸ hm)
    exact quotient_conjugation_action_kills_commutator_layer P C (U R (alpha R))
      (Q R (alpha R)) inferInstance hPC hcomm a ha hmQ
  let aSL : SL →* MulAut D := source.projection.liftOfSurjective
    source.projection_surjective ⟨aM, hkill⟩
  have haSL (m : M) : aSL (source.projection m) = aM m :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hinj : Function.Injective aSL := by
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    apply aSL.ker_eq_bot_iff.mp
    rcases (inferInstance : aSL.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact hk
    exfalso
    have htriv (m : M) : a (i m) = 1 := by
      rw [← show aM m = a (i m) from rfl, ← haSL]
      exact (show source.projection m ∈ aSL.ker from hk.symm ▸ mem_top _)
    have hCU : C ≤ U R (alpha R) := by
      change core R (alpha R) ≤ _
      rw [← source.core_full_commutation (alpha R) rfl, commutator_comm]
      apply commutator_le.mpr
      intro l hl x hx
      have hlM : l ∈ Mbar R := by
        rw [← stabilizer_m_base R]
        exact map_subtype_le _ hl
      obtain ⟨m, rfl⟩ := hlM
      have hh := ha (i m) ⟨x, hx⟩
      rw [htriv] at hh
      have hmem := QuotientGroup.eq_iff_div_mem.mp hh.symm
      change embedM R m * x * (embedM R m)⁻¹ / x ∈ U R (alpha R) at hmem
      simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
    let : Finite (U R (alpha R)) := Nat.finite_of_card_ne_zero (by rw [hU]; decide)
    have hsmall := Nat.card_le_card_of_injective
      (inclusion hCU) (inclusion_injective hCU)
    rw [hcard, hU] at hsmall
    omega
  obtain ⟨e, marking, he⟩ := Matrix.PSL3Two.exists_natural_marking D hD aSL hinj
  refine ⟨{
    marking := marking
    projection := e.toMonoidHom.comp q
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective N)
    kernel := ?_
    action := ?_ }⟩
  · exact (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans
      (QuotientGroup.ker_mk' N)
  · intro m x y hy
    change (e (q y)).toAdd = (marking (source.projection m)).val.mulVec (e (q x)).toAdd
    rw [← he, haSL]
    change (e (q y)).toAdd = (e (a (i m) (q x))).toAdd
    rw [ha]
    congr 3
    exact Subtype.ext hy

/-- At distance two, critical-pair involution generation leaves only the
local order and commutator estimates as extra inputs for the quotient. -/
theorem exists_naturalCoreQuotient_of_local_estimates
    (source : LocalSource L R) (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hcard : Nat.card (core R (alpha R)) = 64)
    (hcomm : ⁅core R (alpha R), Q R (alpha R)⁆ ≤ U R (alpha R)) :
    Nonempty (NaturalCoreQuotient source) :=
  exists_naturalCoreQuotient_of_order_and_commutator source geometry
    (by omega) natural hcard hcomm (involution_generation source geometry hb)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
