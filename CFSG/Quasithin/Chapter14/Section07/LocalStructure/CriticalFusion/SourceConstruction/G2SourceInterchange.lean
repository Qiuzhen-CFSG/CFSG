module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourcePath
public import Theory.SpecificGroups.BinaryLinear.Parabolics

/-!
# Interchanging the original critical vertices

The full natural L action interchanges any two nonzero vectors of V. A
binary transvection gives this linear swap explicitly. When Zα lies in V,
apply it to the generators of V₁ and Zα. Their centralizers are the two
actual H-type vertices in the coset geometry, so the chosen element of L
interchanges those vertices. As it also normalizes V, the reciprocal span
contains V, and in particular contains V₁.

The same element interchanges the two spans and carries the reciprocal
two-core to O₂(H). Mapping relative indices gives equality of the literal
quotient orders, and hence of the two source ranks. This proves 14.7.58
from the original higher-rank hypothesis, actual critical path and its
placement in R₁. It does not assume Data or the degenerate legacy
CriticalSymmetryInput. The later symmetry after 14.7.61, where Zα is no
longer assumed to lie in V, remains a separate obligation.

Source: Aschbacher–Smith, 14.7.58, printed p.1067; the original critical
path and conjugation conventions are those of 14.7.1, printed p.1042.
-/

public noncomputable section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source

private theorem exists_linear_interchange {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (x y : W) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a : W ≃ₗ[ZMod 2] W, a x = y ∧ a y = x := by
  by_cases he : x = y
  · exact ⟨LinearEquiv.refl _ _,he,he.symm⟩
  have hn : x ∉ Submodule.span (ZMod 2) {x+y} := by
    intro hm
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha0 | ha1
    · rw [ha0,zero_smul] at ha
      exact hx ha.symm
    · rw [ha1,one_smul] at ha
      exact hy (add_left_cancel (ha.trans (add_zero x).symm))
  obtain ⟨f,hfx,hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hfx : f x = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hfx
  have hsum : f (x+y) = 0 := by
    have hm := Submodule.mem_map_of_mem (f := f) (Submodule.mem_span_singleton_self (x+y))
    rw [hf] at hm
    exact hm
  have hfy : f y = 1 := by
    have hh := hsum
    rw [map_add,hfx] at hh
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (f y) with hy0 | hy1
    · rw [hy0,add_zero] at hh
      exact (one_ne_zero hh).elim
    · exact hy1
  have hdouble (v : W) : v + v = 0 := by
    have hh := congrArg (fun r : ZMod 2 => r • v) (by decide : (1 : ZMod 2) + 1 = 0)
    simpa only [add_smul,one_smul,zero_smul] using hh
  refine ⟨BinaryLinear.transvection (x+y) f hsum,?_,?_⟩
  · change x + f x • (x+y) = y
    rw [hfx,one_smul,←add_assoc,hdouble,zero_add]
  · change y + f y • (x+y) = x
    rw [hfy,one_smul,add_comm x y,←add_assoc,hdouble,zero_add]

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem vector_interchange
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, l*x*l⁻¹=y ∧ l*y*l⁻¹=x := by
  let := h.chosen.elementary
  let x' : Additive V := Additive.ofMul ⟨x,hx⟩
  let y' : Additive V := Additive.ofMul ⟨y,hy⟩
  have hx0 : x' ≠ 0 := fun he => hx1 (congrArg (fun v : Additive V => (v.toMul:G)) he)
  have hy0 : y' ≠ 0 := fun he => hy1 (congrArg (fun v : Additive V => (v.toMul:G)) he)
  obtain ⟨a,hax,hay⟩ := exists_linear_interchange x' y' hx0 hy0
  obtain ⟨l,hl⟩ := h.naturalMarking.geometryAction.surjective a
  refine ⟨l,l.property,?_,?_⟩
  · have hc := h.naturalMarking.geometryAction.conjugation l x'
    rw [hl,hax] at hc
    exact hc.symm
  · have hc := h.naturalMarking.geometryAction.conjugation l y'
    rw [hl,hay] at hc
    exact hc.symm

open Subgroup.CosetGeometry.RankTwo

/-- The actual two H-type vertices are interchanged in the original coset
geometry when the reselected point lies in the natural seed. -/
theorem critical_vertex_interchange
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) :
    let Ω := geometryFamily (L := L) F
    let a := path.gammaConjugator * inclusion (le_sup_right : F.H ≤ GeometryGroup T L F) path.rechoice
    ∃ g : GeometryGroup T L F, (g : G) ∈ L ∧
      g • base Ω true = a⁻¹ • base Ω true ∧
      g • (a⁻¹ • base Ω true) = base Ω true := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let a : K := path.gammaConjugator * inclusion le_sup_right path.rechoice
  change ∃ g : K, (g:G) ∈ L ∧
    g • base Ω true = a⁻¹ • base Ω true ∧
    g • (a⁻¹ • base Ω true) = base Ω true
  obtain ⟨z,hz,he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hcenter := F.H_eq_centralizer (by decide) z he
  have hzV : z ∈ V := F.le_seed 1 (he.symm ▸ mem_zpowers z)
  let za : G := (a:G)⁻¹*z*(a:G)
  have hzaV : za ∈ V := by
    apply hc
    refine ⟨z,he.symm ▸ mem_zpowers z,?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl
  have hza : za ≠ 1 := by
    intro hh
    apply hz
    have hh' := congrArg (fun x : G => (a:G)*x*(a:G)⁻¹) hh
    simpa only [za,mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_one,mul_inv_cancel] using hh'
  obtain ⟨l,hl,hfirst,hsecond⟩ := vector_interchange h hzV hzaV hz hza
  let g : K := ⟨l,(le_sup_left : L ≤ L ⊔ (T:Subgroup G)).trans le_sup_left hl⟩
  have fix (k : K) (hk : k ∈ Ω true) : k • base Ω true = base Ω true := by
    have hh : k ∈ stabilizer Ω (base Ω true) := by
      simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hk
    exact hh
  have hag : a*g ∈ Ω true := by
    change (a:G)*l ∈ F.H
    rw [hcenter,mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      ((a:G)*l)*z*((a:G)*l)⁻¹ = (a:G)*(l*z*l⁻¹)*(a:G)⁻¹ := by group
      _ = (a:G)*za*(a:G)⁻¹ := by rw [hfirst]
      _ = z := by dsimp [za]; group
  have hga : g*a⁻¹ ∈ Ω true := by
    change l*(a:G)⁻¹ ∈ F.H
    rw [hcenter,mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (l*(a:G)⁻¹)*z*(l*(a:G)⁻¹)⁻¹ = l*za*l⁻¹ := by dsimp [za]; group
      _ = z := hsecond
  refine ⟨g,hl,?_,?_⟩
  · have hh := fix (a*g) hag
    rw [mul_smul] at hh
    calc
      g • base Ω true = a⁻¹ • (a • (g • base Ω true)) := (inv_smul_smul _ _).symm
      _ = a⁻¹ • base Ω true := congrArg (fun v => a⁻¹ • v) hh
  · simpa only [mul_smul] using fix (g*a⁻¹) hga

/-- When the reselected point is in V, the seed lies in the reciprocal span. -/
theorem seed_le_partner
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) : V ≤ path.Uα := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let a : K := path.gammaConjugator * inclusion le_sup_right path.rechoice
  obtain ⟨g,hg,hfirst,_⟩ := critical_vertex_interchange h path hc
  have hag : a*g ∈ Ω true := by
    have hh : a*g ∈ stabilizer Ω (base Ω true) := by
      change (a*g) • base Ω true = base Ω true
      rw [mul_smul,hfirst,smul_inv_smul]
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hgV : (g:G)⁻¹ ∈ normalizer (V : Set G) :=
    h.chosen.normalizes (L.inv_mem hg)
  intro v hv
  have hv' : (g:G)⁻¹*v*(g:G) ∈ V := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp hgV v).mp hv
  have hU : ((a:G)*(g:G))*((g:G)⁻¹*v*(g:G))*((a:G)*(g:G))⁻¹ ∈ F.U :=
    (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V F.H hag) _).mp
      (le_conjugateSpanBy V F.H hv')
  have hvU : (a:G)*v*(a:G)⁻¹ ∈ F.U := by
    convert hU using 1
    group
  change v ∈ F.U.map (MulAut.conj path.conjugator⁻¹).toMonoidHom
  refine ⟨(a:G)*v*(a:G)⁻¹,hvU,?_⟩
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv]
  have ha : path.conjugator = (a:G) := rfl
  rw [ha]
  group

/-- The containment in 14.7.58(2), obtained from the actual vertex swap. -/
theorem point_le_partner
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) : F.Vi 1 ≤ path.Uα :=
  (F.le_seed 1).trans (seed_le_partner h path hc)

private theorem interchange_multipliers
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) :
    ∃ g ∈ L, path.conjugator*g ∈ F.H ∧ g*path.conjugator⁻¹ ∈ F.H := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let a : K := path.gammaConjugator * inclusion le_sup_right path.rechoice
  obtain ⟨g,hg,hfirst,hsecond⟩ := critical_vertex_interchange h path hc
  have hag : a*g ∈ Ω true := by
    have hh : a*g ∈ stabilizer Ω (base Ω true) := by
      change (a*g) • base Ω true = base Ω true
      rw [mul_smul,hfirst,smul_inv_smul]
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hga : g*a⁻¹ ∈ Ω true := by
    have hh : g*a⁻¹ ∈ stabilizer Ω (base Ω true) := by
      change (g*a⁻¹) • base Ω true = base Ω true
      simpa only [mul_smul] using hsecond
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
  exact ⟨g,hg,hag,hga⟩

/-- The actual vertex interchange transports both spans and the reciprocal
 two-core. The conjugation in this statement is left conjugation. -/
theorem critical_span_core_interchange
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) :
    ∃ g ∈ L, F.U.conjBy g = path.Uα ∧ path.Uα.conjBy g = F.U ∧
      path.Qα.conjBy g = F.H.pCoreIn 2 := by
  obtain ⟨g,hg,hag,hga⟩ := interchange_multipliers h path hc
  have hn := le_normalizer_conjugateSpanBy V F.H
  have hfirst : F.U.conjBy g = path.Uα := by
    have hng : F.U.conjBy (path.conjugator*g) = F.U :=
      mem_normalizer_iff_map_conj_eq.mp (hn hag)
    calc
      F.U.conjBy g = F.U.conjBy (path.conjugator⁻¹*(path.conjugator*g)) := by
        congr 1
        group
      _ = (F.U.conjBy (path.conjugator*g)).conjBy path.conjugator⁻¹ := conjBy_mul _ _ _
      _ = F.U.conjBy path.conjugator⁻¹ := by rw [hng]
      _ = path.Uα := rfl
  have hsecond : path.Uα.conjBy g = F.U := by
    change (F.U.conjBy path.conjugator⁻¹).conjBy g = F.U
    rw [←conjBy_mul]
    exact mem_normalizer_iff_map_conj_eq.mp (hn hga)
  have hH : (conjugate F.H path.conjugator).conjBy g = F.H := by
    change (F.H.conjBy path.conjugator⁻¹).conjBy g = F.H
    rw [←conjBy_mul]
    exact mem_normalizer_iff_map_conj_eq.mp (F.H.le_normalizer hga)
  refine ⟨g,hg,hfirst,hsecond,?_⟩
  change ((conjugate F.H path.conjugator).pCoreIn 2).map (MulAut.conj g).toMonoidHom = _
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  change ((conjugate F.H path.conjugator).conjBy g).pCoreIn 2 = _
  rw [hH]

/-- The quotient orders in 14.7.58(2), using the literal H/O₂(H) map. -/
theorem critical_quotient_order_eq
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) (hAH : path.Uα ≤ F.H) :
    (F.U ⊓ path.Qα).relIndex F.U = Nat.card (star F path.Uα) := by
  obtain ⟨g,_,hU,_,hQ⟩ := critical_span_core_interchange h path hc
  have he := relIndex_map_map_of_injective
    (f := (MulAut.conj g).toMonoidHom) (F.U ⊓ path.Qα) F.U (MulAut.conj g).injective
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at he
  change (F.U.conjBy g ⊓ path.Qα.conjBy g).relIndex (F.U.conjBy g) = _ at he
  rw [hU,hQ,inf_comm] at he
  have hk : (starMap F).ker = (F.H.pCoreIn 2).subgroupOf F.H := by
    rw [starMap, QuotientGroup.ker_mk']
    change pCore 2 F.H = ((pCore 2 F.H).map F.H.subtype).comap F.H.subtype
    exact (comap_map_eq_self_of_injective F.H.subtype_injective _).symm
  rw [←he,inf_relIndex_right,←relIndex_subgroupOf hAH,←hk,relIndex_ker]
  rfl

/-- Taking binary logarithms gives the source rank equality. -/
theorem critical_rank_eq
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hc : path.Zα ≤ V) (hAH : path.Uα ≤ F.H) :
    Nat.log 2 ((F.U ⊓ path.Qα).relIndex F.U) = Nat.log 2 (Nat.card (star F path.Uα)) := by
  rw [critical_quotient_order_eq h path hc hAH]

/-- Source 14.7.58(2), with containment in H discharged by the placement
in R₁ from Notation 14.7.1. The quotients use their original two-cores. -/
theorem source_point_and_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (hc : path.Zα ≤ V) :
    F.Vi 1 ≤ path.Uα ∧
      Nat.log 2 ((F.U ⊓ path.Qα).relIndex F.U) = Nat.log 2 (Nat.card (star F path.Uα)) := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  exact ⟨point_le_partner h path hc,critical_rank_eq h path hc hAH⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
