module

public import Theory.Alternating.theorem_5_2_3
public import Theory.Alternating.Aut
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.QuasithinBasic
public import Theory.Representation.NormalInvariants
public import Mathlib.Algebra.Group.Shrink

/-!
# Local structure of the genuine triple cover of A₇

For a finite quasisimple group with central quotient A₇ and center of order
three, the existing Schur-cover theorem supplies Sylow subgroups of order
27 with center of order three. Normality places the ambient center in each
Sylow subgroup; equality of orders then identifies the two centers. The
noncyclic central quotient of order nine proves extraspeciality.

Automorphisms descend faithfully through the perfect central cover. Since
Aut(A₇) is S₇, its two-rank is at most three: an elementary subgroup of order
16 would be Sylow, contradicting the existence of a four-cycle in S₇.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.7.3,
printed p.349 (PDF p.360); GLS volume 3, Theorem 5.2.3(d).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover

open Theory.GroupTheory Subgroup

variable {L : Type*} [Group L] [Finite L]

/-- The actual central quotient map followed by the specified identification. -/
@[expose] def projection (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) :
    L →* alternatingGroup (Fin 7) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center L))

omit [Finite L] in
theorem projection_surjective (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) :
    Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite L] in
theorem projection_ker (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) :
    (projection e).ker = center L := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- Order 27 and center of order three imply the full extraspecial interface. -/
private theorem extraspecial_of_card_center {P : Type*} [Group P] [Finite P]
    (hp : Nat.card P = 27) (hz : Nat.card (center P) = 3) : IsExtraspecial 3 P := by
  have hq : Nat.card (P ⧸ center P) = 3 ^ 2 := by
    have h := (center P).card_eq_card_quotient_mul_card_subgroup
    rw [hp, hz] at h
    omega
  let : IsMulCommutative (P ⧸ center P) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hn : ¬ IsCyclic (P ⧸ center P) := by
    intro hcyc
    let := hcyc
    have hc : center P = ⊤ := center_eq_top_iff.mpr
      (isMulCommutative_of_isCyclic_quotient_center_self P)
    rw [hc, card_top, hp] at hz
    omega
  exact {
    center_order_p := hz
    quotient_elementary_abelian := {
      exponent_dvd_p := ((not_isCyclic_iff_exponent_eq_prime Nat.prime_three hq).mp hn).dvd }
    quotient_nontrivial := Finite.one_lt_card_iff_nontrivial.mp (by omega) }

/-- The genuine Sylow subgroup, including equality of centers in the ambient group. -/
theorem sylow_three_structure [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7))
    (hz : Nat.card (center L) = 3) (P : Sylow 3 L) :
    Nat.card (P : Subgroup L) = 27 ∧ IsExtraspecial 3 (P : Subgroup L) ∧
      (center (P : Subgroup L)).map (P : Subgroup L).subtype = center L := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : Nontrivial L := (projection_surjective e).nontrivial
  let r : Shrink.{0} L ≃* L := Shrink.mulEquiv
  let : Finite (Shrink.{0} L) := Finite.of_equiv L r.toEquiv.symm
  let : Nontrivial (Shrink.{0} L) := r.toEquiv.nontrivial
  let : IsQuasisimple (Shrink.{0} L) :=
    GLS3.Chapter5.isQuasisimple_of_surjective_of_ker_le_center r.symm.toMonoidHom
      r.symm.surjective (by rw [(MonoidHom.ker_eq_bot_iff _).mpr r.symm.injective]; exact bot_le)
  let f : Covering (Shrink.{0} L) (alternatingGroup (Fin 7)) := {
    toMonoidHom := (projection e).comp r.toMonoidHom
    surjective := (projection_surjective e).comp r.surjective }
  have hker : Nat.card f.toMonoidHom.ker = 3 := by
    rw [f.ker_eq_center_of_isSimple]
    exact (Nat.card_congr (centerCongr r).toEquiv).trans hz
  let Q := P.mapSurjective (f := r.symm.toMonoidHom) r.symm.surjective
  have hQ := GLS3.Chapter5.tripleCoverA7_sylow3 f hker Q
  let rP : (P : Subgroup L) ≃* (Q : Subgroup (Shrink.{0} L)) := r.symm.subgroupMap P
  have hPc : Nat.card (P : Subgroup L) = 27 := (Nat.card_congr rP.toEquiv).trans hQ.1
  have hPz : Nat.card (center (P : Subgroup L)) = 3 :=
    (Nat.card_congr (centerCongr rP).toEquiv).trans hQ.2
  have hZP : center L ≤ (P : Subgroup L) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hz)).le_sylow_of_normal P
  have hle : center L ≤ (center (P : Subgroup L)).map (P : Subgroup L).subtype := by
    intro z hz
    refine ⟨⟨z, hZP hz⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext (mem_center_iff.mp hz p)
  refine ⟨hPc, extraspecial_of_card_center hPc hPz, ?_⟩
  exact (eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (P : Subgroup L).subtype_injective, hPz, hz])).symm

omit [Finite L] in
/-- A faithful irreducible module has no fixed vectors for its nontrivial center. -/
theorem center_invariants_eq_bot
    (hz : Nat.card (center L) = 3)
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (rho : Representation F L V) [rho.IsIrreducible] (hrho : Function.Injective rho) :
    Representation.invariants (rho.comp (center L).subtype) = ⊥ := by
  by_contra h
  have hle := Representation.le_ker_of_normal_invariants_ne_bot rho (center L) h
  have hb : center L = ⊥ := le_bot_iff.mp ((rho.ker_eq_bot_iff.mpr hrho) ▸ hle)
  rw [hb, card_bot] at hz
  omega

/-- The Sylow-center restriction has zero fixed space, the input to coprime degree divisibility. -/
theorem sylow_center_invariants_eq_bot [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7))
    (hz : Nat.card (center L) = 3) (P : Sylow 3 L)
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (rho : Representation F L V) [rho.IsIrreducible] (hrho : Function.Injective rho) :
    Representation.invariants ((rho.comp (P : Subgroup L).subtype).comp (center (P : Subgroup L)).subtype) = ⊥ := by
  have he := (sylow_three_structure e hz P).2.2
  apply le_bot_iff.mp
  intro v hv
  have hvZ : v ∈ Representation.invariants (rho.comp (center L).subtype) := by
    intro z
    have hz' : (z : L) ∈ (center (P : Subgroup L)).map (P : Subgroup L).subtype := by
      rw [he]
      exact z.property
    obtain ⟨p, hp, hpz⟩ := hz'
    change rho (z : L) v = v
    rw [← hpz]
    exact hv ⟨p, hp⟩
  rwa [center_invariants_eq_bot hz rho hrho] at hvZ

/-- The two-rank of S₇ is bounded by three, using its actual four-cycles. -/
theorem symmetric_seven_two_rank : primeRank 2 (Equiv.Perm (Fin 7)) ≤ 3 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hcperm : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hd : 2 ^ a ∣ 5040 := by
    simpa only [ha, hcperm] using E.card_subgroup_dvd_card
  have hab : a ≤ 4 := by
    by_contra! hh
    have hbad : 32 ∣ 5040 := (pow_dvd_pow 2 hh).trans hd
    norm_num at hbad
  by_cases ha4 : a = 4
  · have hcard : Nat.card E = 16 := by simp [ha, ha4]
    let S : Sylow 2 (Equiv.Perm (Fin 7)) :=
      (IsElementaryAbelian.isPGroup 2 E).toSylow (by
        have h := E.card_mul_index
        rw [hcard, hcperm] at h
        have he : E.index = 315 := by omega
        rw [he]
        decide)
    let x : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
    have hx4 : x ^ 4 = 1 := by decide
    have hx2 : x ^ 2 ≠ 1 := by decide
    have hp : IsPGroup 2 (zpowers x) := by
      apply IsPGroup.of_card (n := 2)
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime_pow (p := 2) (n := 1) hx2 hx4
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    let y : T := ⟨x, hT (mem_zpowers x)⟩
    have hy : (T.equiv S y) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) _
    have hy2 : y ^ 2 = 1 := (T.equiv S).injective (by simpa using hy)
    exact (hx2 (congrArg Subtype.val hy2)).elim
  · rw [ha]
    exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The automorphism two-rank bound for A₇ itself. -/
theorem alternating_seven_automorphism_two_rank :
    primeRank 2 (MulAut (alternatingGroup (Fin 7))) ≤ 3 := by
  let a : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      7 (by decide) (by decide))
  exact (primeRank_le_of_injective 2 a.symm.toMonoidHom a.symm.injective).trans
    symmetric_seven_two_rank

/-- Faithful descent gives the same bound for every quasisimple cover of A₇. -/
theorem cover_automorphism_two_rank [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) : primeRank 2 (MulAut L) ≤ 3 := by
  let f : PerfectCentralCovering.Cover L (alternatingGroup (Fin 7)) := {
    toMonoidHom := projection e
    surjective := projection_surjective e
    isPerfect := inferInstance
    ker_le_center := (projection_ker e).le }
  have hk : f.toMonoidHom.ker = center L := projection_ker e
  exact (primeRank_le_of_injective 2 (f.autMap hk) (f.autMap_injective hk)).trans
    alternating_seven_automorphism_two_rank

end CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover
