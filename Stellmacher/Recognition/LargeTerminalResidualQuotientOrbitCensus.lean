module

public import Stellmacher.Recognition.LargeTerminalResidualQuotientAction
public import Stellmacher.Recognition.LargeTerminalFixedLayerKernel
public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Theory.GroupAction.Order512FiveInvolutionCosets
public import Theory.GroupAction.FiveFourSixteenOrbitCensus
public import Theory.GroupTheory.SemidirectFaithfulInjection

/-!
# Small native residual orbits have involutory lifts

The second local group acts on the residual abelianization with nonidentity
orbits of sizes five and ten. Its two-core Q acts trivially because Q′ = R′.
The action therefore descends through the actual Frobenius quotient C₅ ⋊ C₄.
Coprime fixed-point lifting shows that the original five-action on R/R′ is
nontrivial. This makes the descended action faithful on C₅, hence on the
whole faithful semidirect product, and the elementary-sixteen census applies.

The terminal module supplies an involution in R outside R′. The intrinsic
order-512 census gives exactly five nonidentity residual cosets admitting
square-one lifts. This set is invariant under the native second-local action,
so it is precisely the five-point orbit. Every orbit of size less than ten
therefore admits such lifts.

Source: Thompson, N-groups VI, PDF p.59, printed p.630; the intrinsic
order-512 and five-four orbit results follow Parrott's 1972 Lemma 4.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
open scoped commutatorElement
universe u

private theorem core_acts_trivially
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    pCore 2 ctx.second ≤ ctx.residualQuotientAction.ker := by
  intro g hg
  apply MulEquiv.ext
  intro w
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (commutator ctx.firstResidual) w
  let s : ctx.firstResidual := ⟨(g : G) * (r : G) * (g : G)⁻¹,
    (mem_normalizer_iff.mp (ctx.second_le_residual_normalizer g.property) r).mp r.property⟩
  rw [ctx.residualQuotientAction_apply_mk g r s rfl]
  change QuotientGroup.mk' (commutator ctx.firstResidual) s =
    QuotientGroup.mk' (commutator ctx.firstResidual) r
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply (mem_map_iff_mem ctx.firstResidual.subtype_injective).mp
  change (↑(s / r) : G) ∈ DerivedAmbient ctx.firstResidual
  rw [← ctx.second_core_derived_eq, show DerivedAmbient (twoCoreIn ctx.second) =
    ⁅twoCoreIn ctx.second, twoCoreIn ctx.second⁆ from map_subtype_commutator _]
  have hgQ : (g : G) ∈ twoCoreIn ctx.second := mem_map_of_mem ctx.second.subtype hg
  have hRQ : ctx.firstResidual ≤ twoCoreIn ctx.second :=
    ctx.derived_centralizer_supplement.1 ▸ le_sup_right
  simpa only [s, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
    commutatorElement_def, div_eq_mul_inv, Subtype.coe_mk]
    using commutator_mem_commutator hgQ (hRQ r.property)

private theorem exists_projection
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ∃ (φ : C4 →* MulAut C5), Function.Injective φ ∧
      ∃ π : ctx.second →* SemidirectProduct C5 C4 φ,
        Function.Surjective π ∧ π.ker = pCore 2 ctx.second := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  let P := GAt ctx.terminal.Γ cp.firstStep
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  let e : P ≃* ctx.second :=
    (P.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨φ, hφ, projection, hsurj, hk⟩ :=
    ten_one_large_first_frobenius tenCtx middle hpath ctx.noTransvections
  have hk' : projection.ker = pCore 2 P := by
    rw [hk]
    change (tenCtx.Γ.twoCoreAt tenCtx.criticalPath.firstStep).subgroupOf
      (GAt tenCtx.Γ tenCtx.criticalPath.firstStep) =
      pCore 2 (GAt tenCtx.Γ tenCtx.criticalPath.firstStep)
    rw [tenCtx.Γ.twoCoreAt_def]
    exact comap_map_eq_self_of_injective
      (GAt tenCtx.Γ tenCtx.criticalPath.firstStep).subtype_injective _
  refine ⟨φ, hφ, projection.comp e.symm.toMonoidHom,
    hsurj.comp e.symm.surjective, ?_⟩
  ext g
  change e.symm g ∈ projection.ker ↔ g ∈ pCore 2 ctx.second
  rw [hk', ← pCore_map_iso 2 e]
  exact (mem_map_equiv).symm

private theorem five_action_nontrivial
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    ∃ a : A, ctx.residualQuotientAction (inclusion hAP a) ≠ 1 := by
  classical
  let R := ctx.firstResidual
  let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
  have hfixed' : FixedPoints.subgroup A R ≤ center R := by
    intro r hr
    apply hfixed
    change (r : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have he := congrArg R.subtype (hr ⟨a, ha⟩)
    change a * (r : G) * a⁻¹ = r at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := 9) ctx.first_residual_structure.1
  let _ : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨_, _, _, hUpper, _, _⟩ := Theory.GroupAction.parrott_twoGroup_structure
    hR ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge hA hfixed'
  have hZ : center R ≤ commutator R := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono R (show 1 ≤ 2 by decide)
  let _ : MulDistribMulAction A (R ⧸ commutator R) :=
    quotientMulDistribMulAction _ (isInvariant_of_characteristic _)
  have hfix : FixedPoints.subgroup A (R ⧸ commutator R) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable R)
      (by rw [hA, ctx.first_residual_structure.1]; decide)
      (commutator R) (isInvariant_of_characteristic _), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hfixed'.trans hZ
  by_contra! hh
  have htriv (w : R ⧸ commutator R) : w = 1 := by
    apply mem_bot.mp
    rw [← hfix]
    intro a
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (commutator R) w
    have he := ctx.residualQuotientAction_apply_mk (inclusion hAP a) r (a • r) rfl
    rw [hh a] at he
    exact he.symm
  have hcard : Nat.card (R ⧸ commutator R) = 16 := by
    rw [ctx.first_residual_frattini_structure.1]
    exact ctx.first_residual_frattini_structure.2
  let _ : Subsingleton (R ⧸ commutator R) := ⟨fun x y => (htriv x).trans (htriv y).symm⟩
  have hc := Nat.card_unique (α := R ⧸ commutator R)
  omega

private theorem faithful_factor
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    ∃ (φ : C4 →* MulAut C5), Function.Injective φ ∧
      ∃ (π : ctx.second →* SemidirectProduct C5 C4 φ)
        (f : SemidirectProduct C5 C4 φ →* MulAut (ctx.firstResidual ⧸ commutator ctx.firstResidual)),
        Function.Surjective π ∧ Function.Injective f ∧
          ∀ g, f (π g) = ctx.residualQuotientAction g := by
  classical
  obtain ⟨φ, hφ, π, hπ, hker⟩ := exists_projection ctx
  have hle : π.ker ≤ ctx.residualQuotientAction.ker :=
    hker ▸ core_acts_trivially ctx
  let f := π.liftOfSurjective hπ ⟨ctx.residualQuotientAction, hle⟩
  have hf (g : ctx.second) : f (π g) = ctx.residualQuotientAction g :=
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨ctx.residualQuotientAction, hle⟩ g
  refine ⟨φ, hφ, π, f, hπ, ?_, hf⟩
  apply SemidirectProduct.injective_of_left_injective hφ f
  apply (MonoidHom.ker_eq_bot_iff _).mp
  let _ : Fact (Nat.card C5).Prime := ⟨by norm_num [C5]⟩
  rcases (f.comp SemidirectProduct.inl).ker.eq_bot_or_eq_top_of_prime_card with hk | hk
  · exact hk
  have hleft (a : C5) : f (SemidirectProduct.inl a) = 1 := by
    exact show a ∈ (f.comp SemidirectProduct.inl).ker from hk ▸ mem_top a
  let r : A →* C4 := (SemidirectProduct.rightHom.comp π).comp (inclusion hAP)
  have hr : r.range = ⊥ := by
    apply Subgroup.card_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 5 4 by decide)
    · simpa only [hA] using card_range_dvd r
    · simpa [C4] using r.range.card_subgroup_dvd_card
  obtain ⟨a, ha⟩ := five_action_nontrivial ctx A hA hAP hAN hfixed
  apply (ha ?_).elim
  rw [← hf]
  have hra : (π (inclusion hAP a)).right = 1 :=
    mem_bot.mp (hr ▸ (show r a ∈ r.range from ⟨a, rfl⟩))
  have he : π (inclusion hAP a) = SemidirectProduct.inl (π (inclusion hAP a)).left := by
    ext <;> simp [hra]
  rw [he, hleft]

private theorem five_subgroup
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ∃ A : Subgroup G, Nat.card A = 5 ∧ A ≤ ctx.second ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤ center ctx.firstResidual := by
  obtain ⟨A, hA, hAE, hAN, hfixed⟩ := ctx.exists_five_subgroup_fixed_center
  refine ⟨A, hA, ?_, hAN, hfixed⟩
  have hEP : EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep ≤
      GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep := by
    rw [show EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep =
      twoResidualIn (GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep) from
        ctx.terminal.Γ.twoResidualAt_def _]
    exact twoResidualIn_le _
  have hmap := (nine_two_ambient_setup
    (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  exact hAE.trans ((map_mono hEP).trans_eq hmap)

/-- The native second-local action has a five-point and a ten-point orbit
covering all nonidentity residual cosets. -/
public theorem LargeTerminalContext.residual_quotient_orbit_census
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ∃ x y : ctx.firstResidual ⧸ commutator ctx.firstResidual,
      x ≠ 1 ∧ y ≠ 1 ∧
      (Set.range (fun g : ctx.second => ctx.residualQuotientAction g x)).ncard = 5 ∧
      (Set.range (fun g : ctx.second => ctx.residualQuotientAction g y)).ncard = 10 ∧
      ∀ w : ctx.firstResidual ⧸ commutator ctx.firstResidual, w ≠ 1 →
        w ∈ Set.range (fun g : ctx.second => ctx.residualQuotientAction g x) ∪
          Set.range (fun g : ctx.second => ctx.residualQuotientAction g y) := by
  let R := ctx.firstResidual
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := 9) ctx.first_residual_structure.1
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 R) := ⟨hR⟩
  let _ : IsElementaryAbelian 2 (R ⧸ commutator R) := by
    refine {
      toIsMulCommutative := (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := commutator R)).mpr le_rfl
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro v
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (commutator R) v
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (N := commutator R) _).mpr
    rw [ctx.first_residual_frattini_structure.1]
    exact pth_power_mem_frattini_of_isPGroup (p := 2) r
  have hcard : Nat.card (R ⧸ commutator R) = 16 := by
    rw [ctx.first_residual_frattini_structure.1]
    exact ctx.first_residual_frattini_structure.2
  obtain ⟨A, hA, hAP, hAN, hfixed⟩ := five_subgroup ctx
  obtain ⟨φ, hφ, π, f, hπ, hf, hfactor⟩ := faithful_factor ctx A hA hAP hAN hfixed
  have horbit (w : R ⧸ commutator R) :
      Set.range (fun g => f g w) =
        Set.range (fun g : ctx.second => ctx.residualQuotientAction g w) := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨p, rfl⟩ := hπ g
      exact ⟨p, by simp only [hfactor]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨π g, by simp only [hfactor]⟩
  obtain ⟨x, y, hx, hy, hxc, hyc, hcover⟩ :=
    Theory.GroupAction.five_four_sixteen_orbit_census hcard φ hφ f hf
  simp only [horbit] at hxc hyc hcover
  exact ⟨x, y, hx, hy, hxc, hyc, hcover⟩

/-- Every nonidentity residual coset in a native orbit of size less than ten
has a square-one representative in the residual. -/
public theorem LargeTerminalContext.residual_quotient_small_orbit_lifts
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S)
    (w : ctx.firstResidual ⧸ commutator ctx.firstResidual) (hw : w ≠ 1)
    (hsmall : (Set.range (fun g : ctx.second => ctx.residualQuotientAction g w)).ncard < 10) :
    ∃ f : ctx.firstResidual, f ^ 2 = 1 ∧
      QuotientGroup.mk' (commutator ctx.firstResidual) f = w := by
  classical
  let R := ctx.firstResidual
  let q := QuotientGroup.mk' (commutator R)
  let T : Set (R ⧸ commutator R) := {v | v ≠ 1 ∧ ∃ f : R, f ^ 2 = 1 ∧ q f = v}
  obtain ⟨b, _, hbR, _, hbC, hb⟩ := ctx.exists_terminal_module_outer_involution
  let bR : R := ⟨b, hbR⟩
  have hb2 : bR ^ 2 = 1 := Subtype.ext (hb ▸ pow_orderOf_eq_one b)
  have hbD : bR ∉ commutator R := by
    intro hh
    apply hbC
    let _ := ctx.derived_residual_elementary
    exact le_centralizer (DerivedAmbient R) (mem_map_of_mem R.subtype hh)
  have hqb : q bR ≠ 1 := fun h => hbD ((QuotientGroup.eq_one_iff bR).mp h)
  have hT : T.ncard = 5 := by
    obtain ⟨A, hA, _, hAN, hfixed⟩ := five_subgroup ctx
    let _ := conjMulDistribMulActionOfLeNormalizer A R hAN
    have hfixed' : FixedPoints.subgroup A R ≤ center R := by
      intro r hr
      apply hfixed
      change (r : G) ∈ centralizer (A : Set G)
      rw [mem_centralizer_iff]
      intro a ha
      have he := congrArg R.subtype (hr ⟨a, ha⟩)
      change a * (r : G) * a⁻¹ = r at he
      exact mul_inv_eq_iff_eq_mul.mp he
    exact (Theory.GroupAction.parrott_involutory_derived_coset_census
      (IsPGroup.of_card (p := 2) (n := 9) ctx.first_residual_structure.1)
      ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge
      hA hfixed' bR hb2 hbD).1
  let _ : MulDistribMulAction ctx.second (R ⧸ commutator R) :=
    MulDistribMulAction.compHom _ ctx.residualQuotientAction
  have hOT : MulAction.orbit ctx.second (q bR) ⊆ T := by
    rintro v ⟨g, rfl⟩
    let e : MulAut R := R.normalizerMonoidHom
      ⟨g, ctx.second_le_residual_normalizer g.property⟩
    refine ⟨?_, e bR, ?_, ?_⟩
    · exact fun h => hqb ((ctx.residualQuotientAction g).map_eq_one_iff.mp h)
    · rw [← map_pow, hb2, map_one]
    · exact (ctx.residualQuotientAction_apply_mk g bR (e bR) rfl).symm
  obtain ⟨x, y, hx, hy, hxc, hyc, hcover⟩ := ctx.residual_quotient_orbit_census
  change (MulAction.orbit ctx.second x).ncard = 5 at hxc
  change (MulAction.orbit ctx.second y).ncard = 10 at hyc
  have hbx : q bR ∈ MulAction.orbit ctx.second x := by
    rcases hcover (q bR) hqb with h | h
    · exact h
    · have heq := MulAction.orbit_eq_iff.mpr h
      have hh := Set.ncard_le_ncard hOT
      rw [heq, hyc, hT] at hh
      omega
  have hwx : w ∈ MulAction.orbit ctx.second x := by
    rcases hcover w hw with h | h
    · exact h
    · have heq := MulAction.orbit_eq_iff.mpr h
      change (MulAction.orbit ctx.second w).ncard < 10 at hsmall
      rw [heq, hyc] at hsmall
      omega
  have hwT : w ∈ T := by
    apply hOT
    rwa [MulAction.orbit_eq_iff.mpr hbx]
  exact hwT.2

end Stellmacher.Recognition
