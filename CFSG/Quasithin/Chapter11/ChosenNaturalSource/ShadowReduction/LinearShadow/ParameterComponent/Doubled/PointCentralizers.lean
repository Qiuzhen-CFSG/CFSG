module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SmallCentralizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.CriticalLine
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.SeedAutomizer

/-!
# Pointwise centralizers and the strict doubled r-bound

Restriction to each original complementary seed preserves prime orders.
An odd-prime actor would move at least 2n dimensions on each seed, impossible
at total corank at most 2n. Every nontrivial local pointwise image therefore
supplies an involution whose two fixed coranks are exactly n. Natural-module
recognition places a conjugate of the original flag plane in its fixed space.
The source line controls its centralizer. If the image is trivial, E.6.12
would force r=1, contrary to the already proved s=2n.

Thus r>2n on the original full module. The final theorems construct every
Geometry field and apply the literal reciprocal contradiction. The authorized
RankOneReduction input remains with qt-d-1222-shadow-parameter-component,
which absorbed qt-d-1222-shadow-rankone-recognition. G.1.6 is supplied by the
completed qt-d-1222-shadow-natural-recognition theorem.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace SmallCentralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

theorem source_conjugate_seed_kernel (d : Coordinates D S) {U : Subgroup G}
    (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree)
    (g : G) (hg : g ∈ normalizer (L : Set G)) :
    (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) =
      (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ⊓ centralizer (fullModule L V : Set G) := by
  have hgi := (normalizer (L : Set G)).inv_mem hg
  have hWg : (fullModule L V).map (MulAut.conj g).toMonoidHom = fullModule L V :=
    mem_normalizer_iff_map_conj_eq.mp (normalizes_fullModule (V := V) hg)
  have hWgi := mem_normalizer_iff_map_conj_eq.mp (normalizes_fullModule (V := V) hgi)
  have hMg : (normalizer (L : Set G)).map (MulAut.conj g).toMonoidHom = normalizer (L : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (L : Set G)).le_normalizer hg)
  have hUi : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ fullModule L V := by
    rw [←hWgi]
    exact map_mono hU
  have hh := source_seed_kernel d hUi
    (by rw [SeedPair.conjugate_corank g⁻¹ hgi]; exact hc)
  have hm := congrArg (fun B : Subgroup G => B.map (MulAut.conj g).toMonoidHom) hh
  have hmap (A : Subgroup G) : (centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) :=
    Theory.GroupTheory.map_centralizer_equiv _ _
  simp only [Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hmap,hMg,hWg] at hm
  have hcancel : (U.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = U := by
    simpa only [inv_inv] using offender_map_conj_inverse U g⁻¹
  rwa [hcancel] at hm

omit [Finite G] in
theorem automizer_zpowers (W : Subgroup G) {x : G} (hx : x ∈ normalizer (W : Set G)) :
    inducedAutomizer W (zpowers x) = zpowers (W.normalizerMonoidHom.rangeRestrict ⟨x,hx⟩) := by
  have he : (zpowers x).subgroupOf (normalizer (W : Set G)) =
      zpowers (⟨x,hx⟩ : normalizer (W : Set G)) := by
    apply (Subgroup.map_injective (normalizer (W : Set G)).subtype_injective)
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr hx),MonoidHom.map_zpowers]
    rfl
  rw [inducedAutomizer,he,MonoidHom.map_zpowers]

omit [Finite G] in
theorem automizer_eq_one_iff (W : Subgroup G) {x : G}
    (hx : x ∈ normalizer (W : Set G)) :
    W.normalizerMonoidHom.rangeRestrict ⟨x,hx⟩ = 1 ↔ x ∈ centralizer (W : Set G) := by
  change (⟨x,hx⟩ : normalizer (W : Set G)) ∈ W.normalizerMonoidHom.rangeRestrict.ker ↔ _
  rw [MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker]
  rfl

omit [Finite G] in
private theorem restriction_order (W B C : Subgroup G)
    (hB : B ≤ W) (hCW : C ≤ normalizer (W : Set G))
    (hCB : C ≤ normalizer (B : Set G))
    (hk : C ⊓ centralizer (B : Set G) = C ⊓ centralizer (W : Set G))
    {x : G} (hx : x ∈ C) {p : ℕ} (hp : p.Prime)
    (ho : orderOf (W.normalizerMonoidHom.rangeRestrict ⟨x,hCW hx⟩) = p) :
    orderOf (B.normalizerMonoidHom.rangeRestrict ⟨x,hCB hx⟩) = p := by
  let : Fact p.Prime := ⟨hp⟩
  let f := W.normalizerMonoidHom.rangeRestrict
  let j := B.normalizerMonoidHom.rangeRestrict
  have hxpow : x^p ∈ centralizer (W : Set G) := by
    apply (automizer_eq_one_iff W ((normalizer (W : Set G)).pow_mem (hCW hx) p)).mp
    change f ((⟨x,hCW hx⟩ : normalizer (W : Set G))^p) = 1
    rw [map_pow,←ho,pow_orderOf_eq_one]
  apply orderOf_eq_prime
  · rw [←map_pow]
    exact (automizer_eq_one_iff B ((normalizer (B : Set G)).pow_mem (hCB hx) p)).mpr
      (centralizer_le hB hxpow)
  · intro h1
    have hxB := (automizer_eq_one_iff B (hCB hx)).mp h1
    have hxW := ((hk.le ⟨hx,hxB⟩).2)
    have he := (automizer_eq_one_iff W (hCW hx)).mpr hxW
    rw [he,orderOf_one] at ho
    exact hp.ne_one ho.symm

/-- Every nonidentity prime-order source actor has that same order on each
of the original complementary seeds. -/
theorem seed_order (d : Coordinates D S) {U : Subgroup G}
    (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree)
    {x : G} (hx : x ∈ normalizer (L : Set G) ⊓ centralizer (U : Set G))
    {p : ℕ} (hp : p.Prime)
    (ho : orderOf ((fullModule L V).normalizerMonoidHom.rangeRestrict
      ⟨x,normalizes_fullModule hx.1⟩) = p) :
    orderOf (V.normalizerMonoidHom.rangeRestrict
      ⟨x,SeedPair.local_centralizer_normalizes d hc hx⟩) = p :=
  restriction_order (fullModule L V) V _ seed_le_fullModule
    (inf_le_left.trans normalizes_fullModule) (SeedPair.local_centralizer_normalizes d hc)
    (source_seed_kernel d hU hc) hx hp ho

private theorem conjugate_odd_lower
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (g : G) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (a : Automizer (V.map (MulAut.conj g).toMonoidHom)) (ha : orderOf a = p) :
    letI := D.elementary
    letI : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
      IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    2*S.field.degree ≤ fixedCodim
      (automizerRepresentation (V.map (MulAut.conj g).toMonoidHom)) (zpowers a) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let e := automizerMapEquiv V (MulAut.conj g)
  have ho : orderOf (e.symm a) = p := (e.symm.orderOf_eq a).trans ha
  have hh := LocalGeometry.WeakClosure.Parameters.FullAutomizer.sl3_odd_prime_lower D S m p hp hpodd (e.symm a) ho
  have he := fixedCodim_map_equivariant (automizerRepresentation V)
    (automizerRepresentation (V.map (MulAut.conj g).toMonoidHom)) e.toMonoidHom
    (automizerModuleEquiv V (MulAut.conj g))
    (automizerRepresentation_equivariant V (MulAut.conj g)) (zpowers (e.symm a))
  simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] at he
  exact he ▸ hh

/-- No odd-prime actor in the source pointwise local centralizer survives
on V_M: its faithful restrictions would move at least 2n dimensions on
both original complementary seeds, exceeding the available 2n. -/
theorem source_prime_actor_two (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {U : Subgroup G} (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree)
    {p : ℕ} (hp : p.Prime)
    (a : inducedAutomizer (fullModule L V)
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) (ha : orderOf a = p) : p = 2 := by
  by_contra hp2
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  let := fullModule_elementary d
  let := D.elementary
  let W := fullModule L V
  let C := normalizer (L : Set G) ⊓ centralizer (U : Set G)
  obtain ⟨x,hx,hxa⟩ := a.property
  change (x:G) ∈ normalizer (L : Set G) ⊓ centralizer (U : Set G) at hx
  have ho : orderOf (W.normalizerMonoidHom.rangeRestrict x) = p := by
    rw [hxa]
    exact (Subgroup.orderOf_coe a).trans ha
  have hCN := SeedPair.local_centralizer_normalizes d hc
  have hVord := seed_order d hU hc hx hp ho
  have hVlow := LocalGeometry.WeakClosure.Parameters.FullAutomizer.sl3_odd_prime_lower D S m p hp hpodd
    (V.normalizerMonoidHom.rangeRestrict ⟨x,hCN hx⟩) hVord
  have hVeq := fixedCodim_inducedAutomizer V (zpowers (x:G)) (zpowers_le.mpr (hCN hx))
  rw [automizer_zpowers V (hCN hx)] at hVeq
  rw [hVeq] at hVlow
  obtain ⟨g,hg,hd,hs,hn⟩ := SeedPair.local_centralizer_preserves_pair d hc
  let B := V.map (MulAut.conj g).toMonoidHom
  have hCB : C ≤ normalizer (B : Set G) := hn.trans inf_le_right
  have hBord := restriction_order W B C (SeedPair.conjugate_le g hg)
    (inf_le_left.trans normalizes_fullModule) hCB
    (source_conjugate_seed_kernel d hU hc g hg) hx hp ho
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hBlow := conjugate_odd_lower m g hp hpodd
    (B.normalizerMonoidHom.rangeRestrict ⟨x,hCB hx⟩) hBord
  have hBeq := fixedCodim_inducedAutomizer B (zpowers (x:G)) (zpowers_le.mpr (hCB hx))
  rw [automizer_zpowers B (hCB hx)] at hBeq
  rw [hBeq] at hBlow
  have hsum := SeedPair.fixed_corank_sum d hd hs
    (zpowers_le.mpr (hCN hx)) (zpowers_le.mpr (hCB hx))
  have hfix : U ≤ W ⊓ centralizer (zpowers (x:G) : Set G) :=
    le_inf hU (le_centralizer_iff.mpr (zpowers_le.mpr hx.2))
  have hb := (ChapterE.Section06.subgroupCorank_antitone hfix).trans hc
  change subgroupCorank (fullModule L V)
    (fullModule L V ⊓ centralizer (zpowers (x:G) : Set G)) ≤ 2*S.field.degree at hb
  change subgroupCorank (fullModule L V)
    (fullModule L V ⊓ centralizer (zpowers (x:G) : Set G)) =
      subgroupCorank V (V ⊓ centralizer (zpowers (x:G) : Set G)) +
        subgroupCorank B (B ⊓ centralizer (zpowers (x:G) : Set G)) at hsum
  rw [hsum] at hb
  have := S.field.degree_pos
  omega

/-- The original automizer of every subspace of corank at most 2n is a
two-group, with no full-normalizer or cubic-containment premise. -/
theorem source_local_centralizer_twoGroup (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {U : Subgroup G} (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) :
    IsPGroup 2 (inducedAutomizer (fullModule L V)
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) := by
  apply isPGroup_of_prime_order_eq_p 2
  intro a hp
  exact source_prime_actor_two d m hU hc hp a rfl

end SmallCentralizer
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace SmallCentralizer
open LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem conjugate_involution_lower
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) (g : G)
    (a : Automizer (V.map (MulAut.conj g).toMonoidHom)) (ha : orderOf a = 2) :
    letI := D.elementary
    letI : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
      IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    S.field.degree ≤ fixedCodim
      (automizerRepresentation (V.map (MulAut.conj g).toMonoidHom)) (zpowers a) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let e := automizerMapEquiv V (MulAut.conj g)
  have ho : orderOf (e.symm a) = 2 := (e.symm.orderOf_eq a).trans ha
  have hh := (natural_fixedCodimensions D S (.sl3 m)).involution_lower (e.symm a) ho
  have he := fixedCodim_map_equivariant (automizerRepresentation V)
    (automizerRepresentation (V.map (MulAut.conj g).toMonoidHom)) e.toMonoidHom
    (automizerModuleEquiv V (MulAut.conj g))
    (automizerRepresentation_equivariant V (MulAut.conj g)) (zpowers (e.symm a))
  simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] at he
  exact he ▸ hh

/-- A nontrivial pointwise local action at corank at most 2n forces an
actual conjugate of the original seed plane into the fixed subgroup. -/
theorem source_fixed_seed_plane (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    {U : Subgroup G} (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree)
    (hne : inducedAutomizer (fullModule L V)
      (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ≠ ⊥) :
    ∃ l : L, (f.Vi 1).map (MulAut.conj (l:G)).toMonoidHom ≤ U := by
  let := fullModule_elementary d
  let := D.elementary
  let W := fullModule L V
  let C := normalizer (L : Set G) ⊓ centralizer (U : Set G)
  let I := inducedAutomizer W C
  have hcard : Nat.card I ≠ 1 := (I.one_lt_card_iff_ne_bot.mpr hne).ne'
  let p := (Nat.card I).minFac
  have hp : p.Prime := Nat.minFac_prime hcard
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := I) p (Nat.minFac_dvd _)
  have hp2 := source_prime_actor_two d m hU hc hp a ha
  have ha2 : orderOf a = 2 := ha.trans hp2
  obtain ⟨x,hx,hxa⟩ := a.property
  change (x:G) ∈ normalizer (L : Set G) ⊓ centralizer (U : Set G) at hx
  have ho : orderOf (W.normalizerMonoidHom.rangeRestrict x) = 2 := by
    rw [hxa]
    exact (Subgroup.orderOf_coe a).trans ha2
  have hCN := SeedPair.local_centralizer_normalizes d hc
  have hVord := seed_order d hU hc hx Nat.prime_two ho
  have hmodel := natural_fixedCodimensions D S (.sl3 m)
  have hVlow := hmodel.involution_lower
    (V.normalizerMonoidHom.rangeRestrict ⟨x,hCN hx⟩) hVord
  have hVeq := fixedCodim_inducedAutomizer V (zpowers (x:G)) (zpowers_le.mpr (hCN hx))
  rw [automizer_zpowers V (hCN hx)] at hVeq
  rw [hVeq] at hVlow
  change S.field.degree ≤ subgroupCorank V (V ⊓ centralizer (zpowers (x:G) : Set G)) at hVlow
  obtain ⟨g,hg,hd,hs,hn⟩ := SeedPair.local_centralizer_preserves_pair d hc
  let B := V.map (MulAut.conj g).toMonoidHom
  have hCB : C ≤ normalizer (B : Set G) := hn.trans inf_le_right
  have hBord := restriction_order W B C (SeedPair.conjugate_le g hg)
    (inf_le_left.trans normalizes_fullModule) hCB
    (source_conjugate_seed_kernel d hU hc g hg) hx Nat.prime_two ho
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hBlow := conjugate_involution_lower m g
    (B.normalizerMonoidHom.rangeRestrict ⟨x,hCB hx⟩) hBord
  have hBeq := fixedCodim_inducedAutomizer B (zpowers (x:G)) (zpowers_le.mpr (hCB hx))
  rw [automizer_zpowers B (hCB hx)] at hBeq
  rw [hBeq] at hBlow
  have hsum := SeedPair.fixed_corank_sum d hd hs
    (zpowers_le.mpr (hCN hx)) (zpowers_le.mpr (hCB hx))
  change subgroupCorank W (W ⊓ centralizer (zpowers (x:G) : Set G)) =
    subgroupCorank V (V ⊓ centralizer (zpowers (x:G) : Set G)) +
      subgroupCorank B (B ⊓ centralizer (zpowers (x:G) : Set G)) at hsum
  have hfix : U ≤ W ⊓ centralizer (zpowers (x:G) : Set G) :=
    le_inf hU (le_centralizer_iff.mpr (zpowers_le.mpr hx.2))
  have hb := (subgroupCorank_antitone hfix).trans hc
  change subgroupCorank W (W ⊓ centralizer (zpowers (x:G) : Set G)) ≤ 2*S.field.degree at hb
  let P := V ⊓ centralizer (zpowers (x:G) : Set G)
  have hPcor : subgroupCorank V P = S.field.degree := by dsimp only [P]; omega
  have hUeq : U = W ⊓ centralizer (zpowers (x:G) : Set G) := by
    apply MinimalFixed.eq_of_le_of_corank_eq hfix inf_le_left
    have hu := subgroupCorank_antitone (V := W) hfix
    have hc' : subgroupCorank W U ≤ 2*S.field.degree := hc
    omega
  have hE := LocalGeometry.WeakClosure.Parameters.hypothesisE61_of_ti D S (LocalGeometry.Preliminary.seed_ti D S)
  have hPne : P ≠ ⊥ := by
    intro hz
    have hh := hmodel.dimension
    change 2*S.field.degree < subgroupCorank V ⊥ at hh
    rw [←hz,hPcor] at hh
    omega
  have hPN := hE.localCentralizer_le_normalizer hPne (show P ≤ V from inf_le_left)
  have hres : ¬ oddCentralizerCondition (normalizer (L : Set G)) V P := by
    intro hr
    have he := localCentralizer_eq_of_residual D S hmodel hE
      (show P ≤ V from inf_le_left)
      (by change subgroupCorank V P < 2*S.field.degree; rw [hPcor]; have := S.field.degree_pos; omega) hr
    have hxP : (x:G) ∈ normalizer (L : Set G) ⊓ centralizer (P : Set G) :=
      ⟨hx.1,le_centralizer_iff.mp (show P ≤ centralizer (zpowers (x:G) : Set G) from inf_le_right)
        (mem_zpowers (x:G))⟩
    have hxV : (x:G) ∈ centralizer (V : Set G) := (he ▸ hxP).2
    have he1 := (automizer_eq_one_iff V (hCN hx)).mpr hxV
    rw [he1,orderOf_one] at hVord
    omega
  obtain ⟨l,hl⟩ := MinimalFixed.sl3_minimal_fixed D S m f hmodel
    (show P ≤ V from inf_le_left) hPcor hPN hres
  refine ⟨l,hl.le.trans ?_⟩
  rw [hUeq]
  exact inf_le_inf seed_le_fullModule le_rfl

/-- All small-corank centralizers lie in the original M. The zero-action
case uses E.6.12, and the nonzero case contains a conjugate source line. -/
theorem source_small_centralizer (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (hline : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  let := fullModule_elementary d
  let W := fullModule L V
  let M := normalizer (L : Set G)
  let I := inducedAutomizer W (M ⊓ centralizer (U : Set G))
  by_cases hz : I = ⊥
  · have hC : M ⊓ centralizer (U : Set G) = M ⊓ centralizer (W : Set G) :=
      le_antisymm (le_inf inf_le_left
        ((inducedAutomizer_eq_bot_iff (inf_le_left.trans normalizes_fullModule)).mp hz))
        (inf_le_inf_left M (centralizer_le hU))
    by_contra he
    have hUne : U ≠ ⊥ := by
      intro hu
      exact SeedPair.seed_inter_ne_bot d hc (by rw [hu,inf_bot_eq])
    have hE := doubled_hypothesisE61 d
    obtain ⟨_,_,_,_,_,hr⟩ := hE.hyperplane_escape_of_maximal_action
      (fun A hA hmax hn => maximal_escape_action_knownSimple hE hA hmax hn)
      hUne hU hC he
    have hb := globalS_le_globalR W
    rw [LocalMinimum.globalS_eq d,hr] at hb
    have hn : (1:ℕ∞) < (2*S.field.degree:ℕ) := by
      apply ENat.natCast_lt_natCast.mpr
      have := S.field.degree_pos
      omega
    exact hn.not_ge hb
  · obtain ⟨l,hl⟩ := source_fixed_seed_plane d m f hU hc hz
    have hp : (f.Vi 0).map (MulAut.conj (l:G)).toMonoidHom ≤ U :=
      (map_mono (f.Vi_mono (by decide : (0:Fin 3) ≤ 1))).trans hl
    apply (centralizer_le hp).trans
    have hmap : (centralizer (f.Vi 0 : Set G)).map (MulAut.conj (l:G)).toMonoidHom =
        centralizer ((f.Vi 0).map (MulAut.conj (l:G)).toMonoidHom : Set G) :=
      Theory.GroupTheory.map_centralizer_equiv _ _
    rw [←hmap]
    have hh := map_mono (f := (MulAut.conj (l:G)).toMonoidHom) hline
    have hm : M.map (MulAut.conj (l:G)).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (L.le_normalizer l.property))
    exact hh.trans hm.le

/-- The strict source r-bound on the original doubled module. -/
theorem source_globalR_gt (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (hline : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :
    (2*S.field.degree:ℕ∞) < globalR (fullModule L V) := by
  have hh : ((2*S.field.degree+1:ℕ):ℕ∞) ≤ globalR (fullModule L V) := by
    apply le_iInf
    intro U
    apply le_iInf
    rintro ⟨hU,he⟩
    by_cases hc : 2*S.field.degree+1 ≤ subgroupCorank (fullModule L V) U
    · exact_mod_cast hc
    exact (he ((source_small_centralizer d m f hline hU (by omega)).trans
      normalizes_fullModule)).elim
  exact (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self _)).trans_le hh

end SmallCentralizer

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The original source hypotheses construct every field of the doubled geometry. -/
theorem source_geometry (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (hpoint : (LocalGeometry.Coordinates.sl3 m).binarySubspace (f.space 0) = U₁) :
    Geometry d H := by
  have hN := line_normalizer_le_of_counterexample h p hc
    (Or.inl ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.groupEquiv⟩⟩)
  have hp : f.Vi 0 = D.centralQuotientPreimage U₁ := congrArg D.centralQuotientPreimage hpoint
  have hline : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) := by
    rw [hp]
    exact ((Subgroup.centralizer_le_normalizer _).trans hN).trans
      (LocalGeometry.WeakClosure.seed_normalizer_le D S)
  exact ⟨source_weak_escape h p hc d m f hpoint,LocalMinimum.globalS_eq d,
    SmallCentralizer.source_globalR_gt d m f hline,LocalMinimum.automizer_rank d⟩

/-- The doubled branch of 11.3.6 is impossible under its literal preceding
upper bound. All local geometric and reciprocal-action inputs are constructed. -/
theorem source_doubled_contradiction (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : LocalGeometry.InvariantFlag (.sl3 m))
    (hpoint : (LocalGeometry.Coordinates.sl3 m).binarySubspace (f.space 0) = U₁)
    (r : RankOneReduction S H) (hu : generationParameter H ≤ 2*S.field.degree) : False :=
  source_contradiction_of_geometry h p hc d (source_geometry h p hc d m f hpoint) r hu

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
