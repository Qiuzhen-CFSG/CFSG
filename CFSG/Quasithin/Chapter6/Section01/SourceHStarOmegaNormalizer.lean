module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient

/-!
# The full omega centralizer normalizes the rank-one Sylow and orbit

Write Z = Ω₁(Z(T)) and U = ⟨Zᴸ⟩. The natural fixed quotient makes every
odd-order element of L fixing a nonfixed point of Z trivial. Cauchy's
theorem therefore makes C_L(Z) a two-group, and the Sylow intersection
identifies it with T ∩ L. Thus every element normalizing L and fixing Z
normalizes both T ∩ L and U.

For the literal H-star orbit centralizer, noncentrality makes C_H(Z) a
proper overgroup of T in H. H-star minimality puts it in M = N_G(L),
so the same normalization applies. This specializes source p.666 to
full Z, which the actual centralizer already fixes; it does not require
the larger semilinear normalizer of C_M(Z ∩ [U,L]). The natural quotient
remains the independent earlier source input.

Source: Aschbacher--Smith 6.1.5, printed p.666, third through fifth
paragraphs, `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

theorem natural_quotient_omega_centralizer
    {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    L ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ L := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let C := L ⊓ centralizer (Z : Set G)
  obtain ⟨z,hz,hzC⟩ := Set.not_subset.mp (natural_quotient_omega_not_fixed hm)
  have hp : IsPGroup 2 C := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
    intro q hq
    obtain ⟨hqp,hqd,_⟩ := Nat.mem_primeFactors.mp hq
    have hq2 : q = 2 := by
      by_contra hn
      let : Fact q.Prime := ⟨hqp⟩
      obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) q hqd
      have ho : Odd (orderOf (x : G)) := by
        rw [← Subgroup.orderOf_mk x.val x.property,hx]
        exact hqp.odd_of_ne_two hn
      have hx1 : (x : G) = 1 := natural_quotient_odd_point_stabilizer hm
        x.property.1 ho (le_conjugateSpanBy Z L hz) hzC
        (mul_inv_eq_iff_eq_mul.mpr ((x.property.2 z hz).symm))
      have he : x = 1 := Subtype.ext hx1
      rw [he,orderOf_one] at hx
      exact hqp.ne_one hx.symm
    subst q
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩
  obtain ⟨P,hP⟩ := exists_sylow_component hTL
  have hPC : (P : Subgroup L) ≤ C.subgroupOf L := by
    intro x hx
    have hxT : (x : G) ∈ (T : Subgroup G) :=
      (hP ▸ mem_map_of_mem L.subtype hx).1
    exact ⟨x.property,fun z hz =>
      (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 x hxT).symm⟩
  have he := congrArg (map L.subtype) (P.is_maximal' hp.comap_subtype hPC)
  change map L.subtype (C.subgroupOf L) = map L.subtype (P : Subgroup L) at he
  rw [map_subgroupOf_eq_of_le (show C ≤ L from inf_le_left),hP] at he
  exact he

theorem natural_quotient_omega_normalizer
    {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    normalizer (L : Set G) ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  rw [← natural_quotient_omega_centralizer hTL hm]
  exact (le_inf inf_le_left (inf_le_right.trans
    (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

omit [Finite G] in
theorem omega_centralizer_normalizes_span {T : Sylow 2 G} {L : Subgroup G} :
    normalizer (L : Set G) ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) :=
  normalizes_conjugateSpanBy _ _ _
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)) inf_le_left

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

omit [Finite G] h in
/-- H-star minimality places the actual full omega centralizer in M. -/
theorem hstar_omega_centralizer_le_M
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hCH : H ⊓ centralizer (Z : Set G) < H := lt_of_le_of_ne inf_le_left (by
    intro he
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    rw [←he]
    exact inf_le_right)
  exact Chapter3.HStar.proper_overgroup_le T hH (le_inf hH.1.1.2 hTZ) hCH

theorem hstar_omega_centralizer_normalizes
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊓
        normalizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hCM := hstar_omega_centralizer_le_M hH hZH
  have hCN : H ⊓ centralizer (Z : Set G) ≤
      normalizer (L : Set G) ⊓ centralizer (Z : Set G) :=
    le_inf (h.maximal_eq_normalizer_L ▸ hCM) inf_le_right
  exact le_inf
    (hCN.trans (RankOneGeneric.natural_quotient_omega_normalizer h.sylow_normalizes_L hm))
    (hCN.trans RankOneGeneric.omega_centralizer_normalizes_span)

theorem hstar_omega_orbit_centralizer_normalizes
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    (centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H)).map
        H.subtype ≤
      normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊓
        normalizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  apply le_trans _ (h.hstar_omega_centralizer_normalizes hH hm hZH)
  rintro x ⟨a,ha,rfl⟩
  refine ⟨a.property,?_⟩
  intro z hz
  exact congrArg H.subtype (ha
    ⟨z,hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1⟩
    (le_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H hz))

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
