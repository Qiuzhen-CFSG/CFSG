module

public import CFSG.Quasithin.Chapter16.Section04To05.Fusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Basic
public import Theory.GroupTheory.DisjointCommutingProduct.Projections
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The linear endpoint of the Bender branch

Once the component is PSL₂(4), projection from L C_G(L) embeds the
faithful two-group R in L. The actual characteristic-two Sylow model shows
that R has exponent two. Transport through R = T_C^g then gives
T_C = Ω₁(T_C). If the O'Nan calculation gives |Ω₁(T_C)| = 2, source
16.4.4(2) identifies C_K(z) with T_C. Multiplication now constructs the
centralizer equivalence required by `IsJanko1Type`.

The linear identification, normalizer equality, O'Nan cardinality, and exact
earlier local results remain explicit premises. This is a conditional endpoint,
not a proof of Proposition 16.5.1 from its original hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1194–1195, Proposition 16.5.1, final paragraph. The PSL₂ Sylow computation
uses the existing upper-unipotent model and the characteristic-two central
quotient equivalence.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G]
/-- The actual field-four projective special linear group. -/
abbrev PSLFour := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

/-- Every two-subgroup of the actual PSL₂(4) has exponent dividing two. -/
theorem pslFour_two_subgroup_squares (P : Subgroup PSLFour) (hP : IsPGroup 2 P)
    (x : P) : x ^ 2 = 1 := by
  let e := Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 2)
  have hQ := hP.map e.symm.toMonoidHom
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  let y : S := ⟨e.symm x, hS (mem_map_of_mem _ x.property)⟩
  let f := Matrix.SpecialLinearGroup.sylowEquivAdditive (GaloisField 2 2) 2 S
  have hy : y ^ 2 = 1 := by
    apply f.symm.injective
    rw [map_pow, map_one]
    change 2 • (f.symm y).toAdd = 0
    exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
  apply Subtype.ext
  apply e.symm.injective
  have hy' : (e.symm (x : PSLFour)) ^ 2 = 1 := congrArg Subtype.val hy
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using hy'

/-- The trivial center of PSL₂(4) separates the two commuting factors. -/
theorem disjoint_component_centralizer_of_pslFour {L : Subgroup G}
    (e : L ≃* PSLFour) : Disjoint L (centralizer (L : Set G)) := by
  apply disjoint_def.mpr
  intro x hx hc
  have hz : (⟨x, hx⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hc y y.property)
  have he : e ⟨x, hx⟩ ∈ center PSLFour := by
    rw [mem_center_iff]
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hz a)
  rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] at he
  have hx1 : (⟨x, hx⟩ : L) = 1 := e.injective (he.trans e.map_one.symm)
  exact congrArg Subtype.val hx1

/-- Projection embeds the faithful inner actor into the component. -/
theorem faithful_inner_two_subgroup_squares {L R : Subgroup G}
    (e : L ≃* PSLFour) (hR : IsPGroup 2 R)
    (hinner : R ≤ L ⊔ centralizer (L : Set G))
    (hfaith : Disjoint R (centralizer (L : Set G))) : ∀ r ∈ R, r ^ 2 = 1 := by
  have hc : L ≤ centralizer (centralizer (L : Set G) : Set G) := by
    intro l hl k hk
    exact (mem_centralizer_iff.mp hk l hl).symm
  obtain ⟨f, _, hk, _, _⟩ := exists_left_projection_of_disjoint_of_commuting
    L (centralizer (L : Set G)) (disjoint_component_centralizer_of_pslFour e) hc
  let j := f.comp (inclusion hinner)
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply j.ker.eq_bot_iff_forall.mpr
    intro r hr
    have hf : inclusion hinner r ∈ f.ker := hr
    rw [hk] at hf
    exact Subtype.ext (disjoint_def.mp hfaith r.property hf)
  let k := e.toMonoidHom.comp j
  intro r hr
  have hp := pslFour_two_subgroup_squares k.range
    (hR.of_surjective k.rangeRestrict k.rangeRestrict_surjective) (k.rangeRestrict ⟨r, hr⟩)
  have hsq : k ((⟨r, hr⟩ : R) ^ 2) = k 1 := by
    have hp' : k ⟨r, hr⟩ ^ 2 = 1 := congrArg Subtype.val hp
    simpa only [map_pow, map_one] using hp'
  exact congrArg Subtype.val ((e.injective.comp hj) hsq)

/-- Transporting the exponent bound identifies T_C with its first omega subgroup. -/
theorem commutingSylow_eq_omega_of_pslFour {T : Sylow 2 G} {L R : Subgroup G} {g : G}
    (e : L ≃* PSLFour) (hR : IsPGroup 2 R)
    (hinner : R ≤ L ⊔ centralizer (L : Set G))
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hconj : R = (commutingSylow T L).conjBy g) :
    omegaOneAmbient (commutingSylow T L) = commutingSylow T L := by
  apply le_antisymm (omegaOneAmbient_le _)
  intro x hx
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl x hx
  have hh : MulAut.conj g x ∈ R := hconj ▸ mem_map_of_mem _ hx
  have hp := faithful_inner_two_subgroup_squares e hR hinner hfaith _ hh
  apply (MulAut.conj g).injective
  simpa only [map_pow, map_one] using hp

variable [Finite G]

/-- A centralizer element in LK has its K-coordinate in C_K(z). -/
theorem centralizer_eq_join {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) (e : L ≃* PSLFour)
    (hlocal : involutionCentralizer z ≤ normalizer (L : Set G))
    (hnorm : normalizer (L : Set G) = L ⊔ centralizer (L : Set G))
    (hCK : centralizer (L : Set G) ⊓ involutionCentralizer z = commutingSylow T L) :
    involutionCentralizer z = L ⊔ commutingSylow T L := by
  have hc : L ≤ centralizer (centralizer (L : Set G) : Set G) := by
    intro l hl k hk
    exact (mem_centralizer_iff.mp hk l hl).symm
  obtain ⟨f, hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    L (centralizer (L : Set G)) (disjoint_component_centralizer_of_pslFour e) hc
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ L ⊔ centralizer (L : Set G) := hnorm ▸ hlocal hx
    let a := f.symm ⟨x, hxprod⟩
    have hax : (a.1 : G) * (a.2 : G) = x := (hf a.1 a.2).symm.trans
      (congrArg Subtype.val (f.apply_symm_apply ⟨x, hxprod⟩))
    have hbz : (a.2 : G) ∈ involutionCentralizer z := by
      have hh := (involutionCentralizer z).mul_mem
        ((involutionCentralizer z).inv_mem (h.component.1 a.1.property)) hx
      rwa [← hax, inv_mul_cancel_left] at hh
    rw [← hax]
    exact mul_mem_sup a.1.property (hCK ▸ ⟨a.2.property, hbz⟩)
  · apply sup_le h.component.1
    exact inf_le_left.trans h.sylow_centralizes

/-- Construct the local J₁ recognition input, including the actual centralizer equivalence.
The cyclic-centralizer implication is precisely the used clause of 16.4.4(2). -/
theorem isJanko1Type_of_linear_endpoint {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (e : L ≃* PSLFour)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hconj : R = (commutingSylow T L).conjBy g)
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hlocal : involutionCentralizer z ≤ normalizer (L : Set G))
    (hnorm : normalizer (L : Set G) = L ⊔ centralizer (L : Set G))
    (hcyclic : IsCyclic (commutingSylow T L) →
      centralizer (L : Set G) ⊓ involutionCentralizer z = commutingSylow T L) :
    IsJanko1Type G := by
  have hinner : R ≤ L ⊔ centralizer (L : Set G) := by
    rw [← hnorm]
    exact h.le_sylow.trans h.sylow_normalizes
  have heq := commutingSylow_eq_omega_of_pslFour e h.sylow.isPGroup hinner hfaith hconj
  have hcard : Nat.card (commutingSylow T L) = 2 := by rwa [heq] at hUC
  have hC := hcyclic (isCyclic_of_prime_card hcard)
  have hprod := centralizer_eq_join h.toStandardSetup e hlocal hnorm hC
  have hd : Disjoint L (commutingSylow T L) :=
    (disjoint_component_centralizer_of_pslFour e).mono_right inf_le_right
  have hc : L ≤ centralizer (commutingSylow T L : Set G) := by
    intro l hl c hc
    exact (mem_centralizer_iff.mp hc.2 l hl).symm
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    L (commutingSylow T L) hd hc
  let c : commutingSylow T L ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hcard (by simp)
  refine ⟨⟨z, h.involution, T, h.mem_sylow, ?_, ?_⟩⟩
  · intro x hx
    exact (mem_centralizer_singleton_iff.mp (h.sylow_centralizes hx)).symm
  · exact ⟨(MulEquiv.subgroupCongr hprod).trans (f.symm.trans (e.prodCongr c))⟩
end CFSG.Quasithin.Chapter16.Intersections.Bender
