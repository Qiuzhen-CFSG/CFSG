module

public import Theory.Alternating.theorem_5_2_3
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.QuasithinBasic
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryCoprimeDegree
public import Mathlib.Algebra.Group.Shrink

/-!
# The genuine triple cover of A₆ in G.9.3

A finite quasisimple group with center of order three and central quotient
A₆ has an extraspecial Sylow three-subgroup of order 27. Its center is the
ambient center. A faithful irreducible binary action has zero invariants
under that center, so its degree is divisible by six.

The actual Sylow subgroup of Aut(A₆) is the cyclic-eight holomorph. On an
elementary abelian subgroup, its projection to the four-element unit group
has kernel of order at most two. Perfect central-cover descent therefore
bounds the automorphism two-rank by three for the cover as well. In the
G.9 range the positive degree is thus exactly six.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(5),
printed pp.354,356; GLS volume 3, 5.2.3(d). We use the proved A₆ Schur-cover
Sylow theorem and actual Aut(A₆) Sylow identification. No split extension
or unconnected family label is substituted for the central cover.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover

open Theory.GroupTheory Subgroup

variable {L : Type*} [Group L] [Finite L]

/-- The actual central quotient map followed by the specified identification. -/
def projection (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) :
    L →* alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center L))

omit [Finite L] in
theorem projection_surjective (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) :
    Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite L] in
theorem projection_ker (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) :
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
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center L) = 3) (P : Sylow 3 L) :
    Nat.card (P : Subgroup L) = 27 ∧ IsExtraspecial 3 (P : Subgroup L) ∧
      (center (P : Subgroup L)).map (P : Subgroup L).subtype = center L := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Nontrivial L := (projection_surjective e).nontrivial
  let r : Shrink.{0} L ≃* L := Shrink.mulEquiv
  let : Finite (Shrink.{0} L) := Finite.of_equiv L r.toEquiv.symm
  let : Nontrivial (Shrink.{0} L) := r.toEquiv.nontrivial
  let : IsQuasisimple (Shrink.{0} L) :=
    GLS3.Chapter5.isQuasisimple_of_surjective_of_ker_le_center r.symm.toMonoidHom
      r.symm.surjective (by rw [(MonoidHom.ker_eq_bot_iff _).mpr r.symm.injective]; exact bot_le)
  let f : Covering (Shrink.{0} L) (alternatingGroup (Fin 6)) := {
    toMonoidHom := (projection e).comp r.toMonoidHom
    surjective := (projection_surjective e).comp r.surjective }
  have hker : Nat.card f.toMonoidHom.ker = 3 := by
    rw [f.ker_eq_center_of_isSimple]
    exact (Nat.card_congr (centerCongr r).toEquiv).trans hz
  let Q := P.mapSurjective (f := r.symm.toMonoidHom) r.symm.surjective
  have hQ := GLS3.Chapter5.tripleCoverA6_sylow3 f hker Q
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
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
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


/-- Every elementary abelian subgroup of the cyclic-eight holomorph has order at most eight. -/
theorem holomorph_elementary_card_le
    (E : Subgroup AlternatingSix.ShadowLocal.Holomorph.Model)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 8 := by
  classical
  let f : E →* (ZMod 8)ˣ := SemidirectProduct.rightHom.comp E.subtype
  let T := {x : AlternatingSix.ShadowLocal.Holomorph.Model // x.right = 1 ∧ x ^ 2 = 1}
  have hT : Nat.card T = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let j : f.ker → T := fun x => ⟨((x : E) : AlternatingSix.ShadowLocal.Holomorph.Model),
    x.property, by
      have hx := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) (x : E)
      exact congrArg (fun z : E => z.val) hx⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : T => z.val) h
  have hk : Nat.card f.ker ≤ 2 := (Nat.card_le_card_of_injective j hj).trans_eq hT
  have hr : Nat.card f.range ≤ 4 := f.range.card_le_card_group.trans_eq (by
    rw [Nat.card_eq_fintype_card]
    decide)
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  nlinarith

/-- The actual Aut(A₆) Sylow model has elementary rank at most three. -/
theorem alternating_six_automorphism_two_rank :
    primeRank 2 (MulAut (alternatingGroup (Fin 6))) ≤ 3 := by
  let P : Sylow 2 (MulAut (alternatingGroup (Fin 6))) := Classical.choice inferInstance
  rw [P.primeRank_eq]
  have he := AlternatingSix.ShadowLocal.Identification.sylowEquiv P
  have hle : primeRank 2 AlternatingSix.ShadowLocal.Holomorph.Model ≤ 3 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E hE
    let := hE
    exact holomorph_elementary_card_le E
  exact (primeRank_le_of_injective 2 he.symm.toMonoidHom he.symm.injective).trans hle

/-- Perfect central covers inherit the required automorphism-rank bound. -/
theorem cover_automorphism_two_rank [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) : primeRank 2 (MulAut L) ≤ 3 := by
  let f : PerfectCentralCovering.Cover L (alternatingGroup (Fin 6)) := {
    toMonoidHom := projection e
    surjective := projection_surjective e
    isPerfect := inferInstance
    ker_le_center := (projection_ker e).le }
  have hk : f.toMonoidHom.ker = center L := projection_ker e
  exact (primeRank_le_of_injective 2 (f.autMap hk) (f.autMap_injective hk)).trans
    alternating_six_automorphism_two_rank

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- The genuine triple cover forces divisibility by six, not merely a lower bound. -/
theorem six_dvd_dimension [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) (hz : Nat.card (center L) = 3)
    (ρ : Representation (ZMod 2) L V) [ρ.IsIrreducible]
    (hfaith : Function.Injective ρ) : 6 ∣ Module.finrank (ZMod 2) V := by
  let P : Sylow 3 L := Classical.choice inferInstance
  have hP := sylow_three_structure e hz P
  let : IsExtraspecial 3 (P : Subgroup L) := hP.2.1
  exact Representation.BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
    (ρ.comp (P : Subgroup L).subtype) hP.1
    (sylow_center_invariants_eq_bot e hz P ρ hfaith)

/-- The complete degree assertion for a genuine triple cover in the G.9 range. -/
theorem small_degree_eq_six [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) (hz : Nat.card (center L) = 3)
    (ρ : Representation (ZMod 2) L V) [ρ.IsIrreducible]
    (hfaith : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 (MulAut L) + 1)) :
    Module.finrank (ZMod 2) V = 6 := by
  have hdiv := six_dvd_dimension e hz ρ hfaith
  have hr := cover_automorphism_two_rank e
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hpos := Module.finrank_pos (R := ZMod 2) (M := V)
  omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
