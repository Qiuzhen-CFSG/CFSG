module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalHermitian
public import Theory.GroupTheory.OddInvertedModuloTwo

/-!
# Smaller module witnesses in the local Cartan argument

The maximal component constructed in the omega-centralizer controls every
nonidentity omega-point centralizer. Thus a minus torus fixing just one
such point already lies in that component and forces the original degree
two. Any nonzero elementary Sylow-invariant Hermitian subgroup supplies
such a point. It need not contain all of omega or split off from W.

The actual Thompson-moving branch also forces degree two: in its natural
alternative the escaping cubic fixes precisely the L-fixed kernel, which
outside centralization makes trivial. This contradicts the nonzero
intersection of W with omega. Consequently any higher-degree input has
Thompson centralizing both W and the actual omega-span.

All exits retain the original W and actual relative component and quotient.
The initial component-and-cubic sieve and exhaustive recognition in the
remaining Thompson-centralizing branch are still required.
Source: Aschbacher--Smith 5.1.2--3 and 5.1.13, pp.630--631,638,
refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
-- Explicit names avoid a collision when the local and global Cartan branches meet.
local instance cartanLocalSubmoduleFixedFieldAlgebra (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance cartanLocalSubmoduleBinarySpace (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

/-- Fixing one nonidentity omega-point is enough to place an inverted odd
torus in the centralizing maximal component. -/
theorem localCartan_inverted_torus_centralizes_of_point
    {T : Sylow 2 G} {L W H A B Y X D E : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hEA : E ≤ A) {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hz1 : z ≠ 1) (hEz : E ≤ centralizer ({z} : Set G))
    (hinv : ∃ t ∈ (T : Subgroup G) ⊓ X,
      ∀ e ∈ E, t*e*t⁻¹*e ∈ (T : Subgroup G)) :
    E ≤ omegaCentralizer T := by
  obtain ⟨K,hXK,_,dK,_,hp⟩ := localCartan_centralizer_witness h hH hgen c hY d
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  obtain ⟨t,ht,hi⟩ := hinv
  exact (odd_inverted_mod_two_le (hoA.of_dvd_nat (card_dvd_of_le hEA))
    (hEz.trans (hp z hz hz1)) T.isPGroup' (hXK ht.2) hi).trans dK.component_le

/-- The original minus roots need only fix one nonidentity omega-point. -/
theorem localCartan_escape_of_minus_roots_fix_point
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hm : Odd (n/2))
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hc : ∀ x ∈ A, x^(2^(n/2)+1) = 1 → x ∈ centralizer ({z} : Set G)) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  obtain ⟨E,hEA,hDE,hEc,hroot,hi⟩ := d.exists_inverted_minus_torus h c hm
  have hEz : E ≤ centralizer ({z} : Set G) := fun x hx =>
    hc x (hroot x |>.mp hx).1 (hroot x |>.mp hx).2
  have hEC := localCartan_inverted_torus_centralizes_of_point
    h hH hgen c hY d hEA hz hz1 hEz hi
  have hn := localCartan_degree_two_of_minus_torus h hH hgen c hY d hEA hDE hEC hEc hi
  exact ⟨hn,localCartan_escape_of_minus_torus h hH hgen c hY d hEA hDE hEC hEc hi⟩

/-- On a genuine Hermitian subgroup the minus roots fix its intersection
with the ambient omega-center; the subgroup need not contain all of omega. -/
theorem hermitian_minus_root_fixes_omega_intersection
    {T : Sylow 2 G} {L U : Subgroup G} (s : ℕ) [NeZero s]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : IsConjugationModel L U (Representation.SL2.BinarySmall.hermitian s))
    {x z : G} (hx : x ∈ localBorel T L) (hp : x^(2^s+1)=1)
    (hzU : z ∈ U) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    x ∈ centralizer ({z} : Set G) := by
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let S := P.mapSurjective hq
  let xL : L := ⟨x,hx.1⟩
  let zU : U := ⟨z,hzU⟩
  have hfix (l : L) :
      Representation.SL2.BinarySmall.hermitian s (q l) (f zU).toAdd = (f zU).toAdd ↔
        (l : G)*z*(l : G)⁻¹ = z := by
    constructor
    · intro he
      have hh := hf l zU
      change (f.symm (Multiplicative.ofAdd
        (Representation.SL2.BinarySmall.hermitian s (q l) (f zU).toAdd)) : G) = _ at hh
      rw [he] at hh
      change (f.symm (f zU) : G) = _ at hh
      rw [f.symm_apply_apply] at hh
      exact hh.symm
    · intro he
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply U.subtype_injective
      change (f.symm (Multiplicative.ofAdd
        (Representation.SL2.BinarySmall.hermitian s (q l) (f zU).toAdd)) : G) =
          (f.symm (f zU) : G)
      rw [f.symm_apply_apply]
      exact (hf l zU).trans he
  have hnorm : q xL ∈ normalizer (S : Set SL(2,FiniteModel.Field s)) := by
    have hN : xL ∈ normalizer (P : Set L) := by
      have hh : (xL : G) ∈ (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype := by
        rwa [←localBorel_eq_map]
      have hh' : xL ∈ normalizer ((T : Subgroup G).subgroupOf L : Set L) :=
        (mem_map_iff_mem L.subtype_injective).mp hh
      change xL ∈ normalizer ((P : Subgroup L) : Set L)
      rw [hP]
      exact hh'
    exact (Subgroup.le_normalizer_map (H := (P : Subgroup L)) q) (mem_map_of_mem q hN)
  have hzS : (f zU).toAdd ∈ Representation.BinaryOffender.fixedSpace
      (Representation.SL2.BinarySmall.hermitian s) S := by
    intro g
    obtain ⟨l,hl,he⟩ := g.property
    change Representation.SL2.BinarySmall.hermitian s g.val (f zU).toAdd = _
    rw [←he]
    apply (hfix l).mpr
    have hlT : (l : G) ∈ (T : Subgroup G) := by
      change l ∈ (P : Subgroup L) at hl
      rwa [hP] at hl
    have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 l hlT
    rw [hc,mul_inv_cancel_right]
  have hpL : xL^(2^s+1)=1 := Subtype.ext hp
  have he := (hfix xL).mp (SylowTorus.minus_root_fixes s S (q xL) hnorm
    (by rw [←map_pow,hpL,map_one]) (f zU).toAdd hzS)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

/-- A single nonzero Sylow-invariant Hermitian subgroup suffices to conclude
for the whole original module. No omega-containment or splitting is assumed. -/
theorem localCartan_escape_of_hermitian_subgroup
    {T : Sylow 2 G} {L W H A B Y X D U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (s : ℕ) [NeZero s]
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥)
    (hm : IsConjugationModel L U (Representation.SL2.BinarySmall.hermitian s)) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  have hn := h.exponent_of_hermitian_model s hm
  have hhalf : n/2=s := by omega
  have hDC := (d.cubic_le.trans inf_le_right).trans (localCartan_centralizes h hH hgen c hY d)
  have ho := (hermitian_omega_torus s h.sylow_normalizes hU hUT hTU hU0
    ((d.cubic_le.trans inf_le_left).trans c.left_le) d.cubic_card hDC hm).1
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzU : (z : G) ∈ U := z.property.1
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    let := hU
    exact ⟨hUT hzU,elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) hzU,z.property.2.2⟩
  apply localCartan_escape_of_minus_roots_fix_point h hH hgen c hY d
    (hhalf ▸ ho) hzZ (fun he => hz1 (Subtype.ext he))
  intro x hx hp
  rw [hhalf] at hp
  exact hermitian_minus_root_fixes_omega_intersection s h.sylow_normalizes hm
    (c.left_le hx) hp hzU hzZ

/-- The whole FF branch is settled directly from Thompson movement. In the
natural row the original cubic would fix only the zero fixed kernel, contrary
to its fixing the nonzero intersection with omega. -/
theorem localCartan_escape_of_thompson_moves
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  have hn : n = 2 := by
    rcases h.borel_thompson_or_degree_two hj with hN | hn
    · have hDC := (d.cubic_le.trans inf_le_right).trans
        (localCartan_centralizes h hH hgen c hY d)
      have hDB := (d.cubic_le.trans inf_le_left).trans c.left_le
      have hfix := h.cubic_fixed_eq_of_normalizes_thompson hj
        (hDB.trans inf_le_left) d.cubic_card (hDB.trans (le_sup_left.trans hN))
      have hzero := h.reduced_fixed_eq_bot_of_outside_centralizes hH
        ((residual_le_omegaCentralizer_iff hH.1.1.2).mp
          (d.residual_le.trans (localCartan_centralizes h hH hgen c hY d)))
      have hW : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
      obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
        (inf_centerIn_ne_bot T.isPGroup' hW h.reduced_le_sylow
          (le_sup_right.trans (reduced_normalizes h.reduced)))
      have hzW : (z : G) ∈ W := z.property.1
      have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
        apply (mem_omegaOneCenterAmbient_iff _ _).mpr
        let := h.reduced.2.1
        exact ⟨h.reduced_le_sylow hzW,
          elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) hzW,z.property.2.2⟩
      have hzD : (z : G) ∈ centralizer (D : Set G) := (le_centralizer_iff.mp hDC) hzZ
      have hzbot : (z : G) ∈ (⊥ : Subgroup G) := hzero ▸ hfix ▸ ⟨hzW,hzD⟩
      exact (hz1 (Subtype.ext (mem_bot.mp hzbot))).elim
    · exact hn.1
  refine ⟨hn,?_⟩
  subst n
  exact localCartan_escape_of_witness_degree_two h hH hgen c hY d

/-- At higher degree Thompson centralizes both the original module and the
actual omega-span. This is a consequence of the original source hypotheses. -/
theorem localCartan_thompson_centralizes_of_degree_gt_two
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hn : 2 < n) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  constructor
  · by_contra hj
    have := (localCartan_escape_of_thompson_moves h hH hgen c hY d hj).1
    omega
  · by_contra hj
    have := (localCartan_escape_of_thompson_moves
      (localCartan_omega_span_input h hH hgen c hY d) hH hgen c hY d hj).1
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
