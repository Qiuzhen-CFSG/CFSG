module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMinusInversion
public import Theory.Representation.OrthogonalFourMinusRankOne.SylowTorus
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# The Hermitian branch of the original Cartan degree argument

An actual Hermitian action of L/O₂(L) identifies the original exponent
as twice the half-degree. A nonzero elementary T-invariant subgroup meets
Ω₁Z(T). The original cubic fixes that vector after the proved component
centralization, so the Hermitian Sylow-normalizer calculation forces odd
half-degree. The same calculation makes every minus-torus root fix omega
when the module contains omega. The existing inversion and exceptional
quotient spectra then force degree two.

Reselecting the literal L-span of omega supplies that containment without
altering the original W. The final theorem therefore gives the exceptional
conclusion for the original whole moved module, residual quotient and
relative component. It retains an actual Hermitian model as an explicit
branch premise. The exhaustive module alternatives and the initial
component-and-cubic sieve remain source obligations; this is not yet an
inhabitant of SourceLocalCartanEscape.

Source: Aschbacher--Smith 5.1.3 and the final paragraph of 5.1.13,
printed pp.630--631,638, refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

/-- Actual Hermitian coordinates turn cubic omega-fixation into odd half-degree,
and place the original minus roots in the omega-centralizer when the module
contains omega. All maps use the original two-core quotient. -/
theorem hermitian_omega_torus
    {T : Sylow 2 G} {L U D : Subgroup G} (s : ℕ) [NeZero s]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥)
    (hDB : D ≤ localBorel T L) (hDc : Nat.card D = 3)
    (hDC : D ≤ omegaCentralizer T)
    (hm : IsConjugationModel L U (Representation.SL2.BinarySmall.hermitian s)) :
    Odd s ∧ (omegaOneCenterAmbient (T : Subgroup G) ≤ U →
      ∀ x ∈ localBorel T L, x^(2^s+1)=1 → x ∈ omegaCentralizer T) := by
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let S := P.mapSurjective hq
  have hfixed (l : L) (u : U) :
      Representation.SL2.BinarySmall.hermitian s (q l) (f u).toAdd = (f u).toAdd ↔
        (l : G)*(u : G)*(l : G)⁻¹ = (u : G) := by
    constructor
    · intro he
      have hh := hf l u
      change (f.symm (Multiplicative.ofAdd
        (Representation.SL2.BinarySmall.hermitian s (q l) (f u).toAdd)) : G) = _ at hh
      rw [he] at hh
      change (f.symm (f u) : G) = _ at hh
      rw [f.symm_apply_apply] at hh
      exact hh.symm
    · intro he
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply U.subtype_injective
      change (f.symm (Multiplicative.ofAdd
        (Representation.SL2.BinarySmall.hermitian s (q l) (f u).toAdd)) : G) = (f.symm (f u) : G)
      rw [f.symm_apply_apply]
      exact (hf l u).trans he
  have hnorm (l : L) (hl : (l : G) ∈ localBorel T L) :
      q l ∈ normalizer (S : Set SL(2,FiniteModel.Field s)) := by
    have hN : l ∈ normalizer (P : Set L) := by
      have hh : (l : G) ∈ (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype := by
        rwa [←localBorel_eq_map]
      have hh' := (mem_map_iff_mem L.subtype_injective).mp hh
      change l ∈ normalizer ((P : Subgroup L) : Set L)
      rw [hP]
      exact hh'
    exact (Subgroup.le_normalizer_map (H := (P : Subgroup L)) q) (mem_map_of_mem q hN)
  have hSylow (u : U) (hu : (u : G) ∈ omegaOneCenterAmbient (T : Subgroup G)) :
      (f u).toAdd ∈ Representation.BinaryOffender.fixedSpace
        (Representation.SL2.BinarySmall.hermitian s) S := by
    intro g
    obtain ⟨l,hl,he⟩ := g.property
    change Representation.SL2.BinarySmall.hermitian s g.val (f u).toAdd = _
    rw [←he]
    apply (hfixed l u).mpr
    have hlT : (l : G) ∈ (T : Subgroup G) := by
      change l ∈ (P : Subgroup L) at hl
      rwa [hP] at hl
    have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp hu).2.2 l hlT
    rw [hc,mul_inv_cancel_right]
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzU : (z : G) ∈ U := z.property.1
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    let := hU
    exact ⟨hUT hzU,elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) hzU,z.property.2.2⟩
  let zU : U := ⟨z,hzU⟩
  have hz : (f zU).toAdd ≠ 0 := by
    intro he
    have h1 : zU = 1 := f.injective (he.trans f.map_one.symm)
    exact hz1 (Subtype.ext (congrArg (fun u : U => (u : G)) h1))
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hDc])
  let aL : L := ⟨a,(hDB.trans inf_le_left) a.property⟩
  have hao : orderOf aL = 3 := (Subgroup.orderOf_coe aL).symm.trans
    ((orderOf_injective D.subtype D.subtype_injective a).trans ha)
  have hqne : q aL ≠ 1 := by
    intro he
    have haQ : aL ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp
      (e.injective (he.trans e.map_one.symm))
    have hh := (pCore_isPGroup (p:=2) (G:=L)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨aL,haQ⟩ : pCore 2 L)
    rw [Subgroup.orderOf_mk,hao] at hh
    norm_num at hh
  have hqo : orderOf (q aL) = 3 := orderOf_eq_prime
    (by rw [←map_pow,←hao,pow_orderOf_eq_one,map_one]) hqne
  refine ⟨SylowTorus.half_degree_odd_of_cubic_fixed s S (q aL)
    (hnorm aL (hDB a.property)) hqo (f zU).toAdd (hSylow zU hzZ) hz ?_,?_⟩
  · apply (hfixed aL zU).mpr
    have hc : (a:G)*(z:G) = (z:G)*(a:G) := ((hDC a.property) z hzZ).symm
    change (a:G)*(z:G)*(a:G)⁻¹ = (z:G)
    rw [hc,mul_inv_cancel_right]
  · intro hZU x hx hp z hz
    let xL : L := ⟨x,hx.1⟩
    let zU : U := ⟨z,hZU hz⟩
    have hpL : xL^(2^s+1)=1 := Subtype.ext hp
    have hfix := SylowTorus.minus_root_fixes s S (q xL) (hnorm xL hx)
      (by rw [←map_pow,hpL,map_one]) (f zU).toAdd (hSylow zU hz)
    have he := (hfixed xL zU).mp hfix
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The actual Hermitian quotient marking determines the original field degree. -/
theorem Input.exponent_of_hermitian_model
    {T : Sylow 2 G} {L W U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L U (Representation.SL2.BinarySmall.hermitian s)) :
    n = 2*s := by
  obtain ⟨e,_,_⟩ := hm
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let a := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=F)).trans (f.symm.trans e)
  exact Matrix.SL2.field_degree_eq_of_equiv a (by decide) hF
    (GaloisField.card 2 (2*s) (Nat.mul_ne_zero (by decide) (NeZero.ne s)))

/-- A Hermitian model on an original reduced subgroup containing omega
supplies the two remaining torus premises and hence the full exceptional exit. -/
theorem localCartan_escape_of_hermitian
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L W (Representation.SL2.BinarySmall.hermitian s))
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ W) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  have hn := h.exponent_of_hermitian_model s hm
  have hhalf : n/2=s := by omega
  have hDC := (d.cubic_le.trans inf_le_right).trans (localCartan_centralizes h hH hgen c hY d)
  obtain ⟨ho,hc⟩ := hermitian_omega_torus s h.sylow_normalizes h.reduced.2.1
    h.reduced_le_sylow (le_sup_right.trans (reduced_normalizes h.reduced))
    (fun he => h.noncentral (by rw [he,commutator_bot_left]))
    ((d.cubic_le.trans inf_le_left).trans c.left_le) d.cubic_card hDC hm
  apply localCartan_escape_of_minus_roots_centralize h hH hgen c hY d
  · rwa [hhalf]
  · intro x hx hp
    rw [hhalf] at hp
    exact hc hZ x (c.left_le hx) hp

/-- After the proved component centralization, the actual omega-span is
another noncentral reduced input at the same original Sylow and field degree. -/
theorem localCartan_omega_span_input
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    Input KnownSimple.IsKnownSimple T L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  have hHC := (residual_le_omegaCentralizer_iff hH.1.1.2).mp
    (d.residual_le.trans (localCartan_centralizes h hH hgen c hY d))
  have hfixed := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  apply h.omega_span_input
  intro hLC
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
  have hzC := (le_centralizer_iff.mp hLC) hzZ
  have hzbot : (z : G) ∈ (⊥ : Subgroup G) := hfixed ▸ ⟨hzZ,hzC⟩
  exact hz1 (Subtype.ext (mem_bot.mp hzbot))

/-- The genuine orthogonal alternative on the source omega-span now forces
n=2 and the full exceptional conclusion for the original W. Neither odd
half-degree nor minus-torus fixation is an additional premise. The source
module classification must still supply this actual model or its other rows. -/
theorem localCartan_escape_of_hermitian_omega_span
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (Representation.SL2.BinarySmall.hermitian s)) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  have hs := localCartan_omega_span_input h hH hgen c hY d
  have hn := (localCartan_escape_of_hermitian hs hH hgen c hY d s hm
    (le_conjugateSpanBy _ _)).1
  refine ⟨hn,?_⟩
  subst n
  exact localCartan_escape_of_witness_degree_two h hH hgen c hY d

/-- Above degree two the orthogonal omega-span row is impossible. -/
theorem localCartan_not_hermitian_omega_span
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hn : 2 < n) (s : ℕ) [NeZero s] :
    ¬ IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (Representation.SL2.BinarySmall.hermitian s) := by
  intro hm
  have he := (localCartan_escape_of_hermitian_omega_span h hH hgen c hY d s hm).1
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
