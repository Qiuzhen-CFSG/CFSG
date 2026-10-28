module

public import Stellmacher.Recognition.LargeTerminalReeActionCoordinates
public import Stellmacher.Recognition.LargeTerminalFirstCoreSecondCenter
public import Theory.SpecificGroups.ReeTwo.FixingNonstandardFirstCore
public import Theory.SpecificGroups.ReeTwo.FixingModelSplitTwo

/-!
# Selecting the standard fixing action in the actual terminal geometry

An actual split squaring actor and the second core generate a local Sylow
subgroup. A nonstandard census entry would identify its intrinsic first core
with the split base-two first core. Marked Sylow conjugacy transports that
identification to the original neighboring core. A fixed-mark certificate
for base two then contradicts the neighboring parabolic's action on the mark.
The finite base-two certificate is proved in `FixingModelSplitTwo` and
discharges the remaining premise of the actual-coordinate selection.

Source: Thompson VI, pp.629–630; Shinoda (1975), pp.81–83. The actual-group
transport follows `LargeTerminalReeNonsplitExclusion`, with a different model
obstruction: here the fourth power is already one.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- The neighboring parabolic excludes every nonstandard split census
action, provided the split base-two fixed-mark certificate. -/
public theorem LargeTerminalContext.ree_census_standard_of_two_certificate
    (htwo : ∀ b : MulAut (ReeTwo.FixingModel.firstCore 2 false),
      b (ReeTwo.FixingModel.centralInvolution 2 false) =
        ReeTwo.FixingModel.centralInvolution 2 false)
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (z : G) (hz : orderOf z = 2)
    (hzgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (e : twoCoreIn ctx.second ≃* ReeTwo.Core) (c a : ctx.second) (k : Fin 20)
    (hez : (e.symm (ReeTwo.Core.root 9) : G) = z)
    (hcA : zpowers (c : G) = A) (ha4 : a ^ 4 = 1)
    (hac : a * c * a⁻¹ = c ^ 2)
    (ha : ctx.reeCoreAction e a = ReeTwo.Core.FixingActionCensus.representative k) :
    ReeTwo.Core.FixingActionCensus.IsStandard k := by
  by_contra hk
  have hacG : (a : G) * (c : G) * (a : G)⁻¹ = (c : G) ^ 2 :=
    congrArg Subtype.val hac
  have hsa : ∀ x ∈ A, (a : G) * x * (a : G)⁻¹ = x ^ 2 := by
    intro x hx
    obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hcA ▸ hx)
    rw [← conj_pow, hacG, ← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  have hsA : (a : G) ∈ normalizer (A : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      change (a : G) * x * (a : G)⁻¹ ∈ A
      rw [hsa x hx]
      exact A.pow_mem hx 2
    · rw [card_map_of_injective (MulAut.conj (a : G)).injective]
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers a) := by
    apply (isPGroup_iff_card_dvd_pow).mpr
    exact ⟨2, by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one ha4⟩
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have haT : a ∈ T := hT (mem_zpowers a)
  have hQT : ∀ q : twoCoreIn ctx.second,
      (⟨(q : G), twoCoreIn_le ctx.second q.property⟩ : ctx.second) ∈ T := by
    intro q
    obtain ⟨qP, hqP, he⟩ := q.property
    have hqT := (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal T hqP
    have heq : (⟨(q : G), twoCoreIn_le ctx.second q.property⟩ : ctx.second) = qP :=
      Subtype.ext he.symm
    rw [heq]
    exact hqT
  let i : T →* G := ctx.second.subtype.comp T.toSubgroup.subtype
  have hi : Function.Injective i := ctx.second.subtype_injective.comp T.toSubgroup.subtype_injective
  let j : ReeTwo.Core →* T :=
    { toFun := fun q => ⟨⟨(e.symm q : G), twoCoreIn_le ctx.second (e.symm q).property⟩,
        hQT (e.symm q)⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun q : twoCoreIn ctx.second => (q : G)) e.symm.map_one
      map_mul' := fun x y => by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun q : twoCoreIn ctx.second => (q : G)) (e.symm.map_mul x y) }
  let aT : T := ⟨a, haT⟩
  have hj : ∀ q, i (j q) = (e.symm q : G) := fun _ => rfl
  have hjz : i (j (ReeTwo.Core.root 9)) = z := hez
  have hgen : j.range ⊔ zpowers aT = ⊤ := by
    apply Subgroup.map_injective hi
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    have hrange : j.range.map i = twoCoreIn ctx.second := by
      rw [← MonoidHom.range_comp]
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        exact (e.symm q).property
      · intro hx
        exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
    rw [hrange]
    have hs4Q : (a : G) ^ 4 ∈ twoCoreIn ctx.second := by
      rw [← coe_pow, ha4, coe_one]
      exact one_mem _
    have hG := ctx.local_sylow_generated_by_squaring_lift
      hS A hA hAP a a.property hsA hsa hs4Q T haT
    change twoCoreIn ctx.second ⊔ zpowers (a : G) = (⊤ : Subgroup T).map i
    rw [hG, ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype]
  have hcardT : Nat.card T = 4096 := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    exact (Nat.card_congr ((T.equiv (S.subtype hSP)).trans
      (subgroupOfEquivOfLe hSP)).toEquiv).trans hS
  have hjconj : ∀ q, aT * j q * aT⁻¹ =
      j (ReeTwo.Core.FixingActionCensus.representative k q) := by
    intro q
    apply hi
    rw [map_mul, map_mul, map_inv, hj, hj]
    change (a : G) * (e.symm q : G) * (a : G)⁻¹ = _
    have hh := ctx.reeCoreAction_apply e a (e.symm q)
    simpa only [e.apply_symm_apply, ha] using hh.symm
  have hjfour : aT ^ 4 = 1 := Subtype.ext ha4
  obtain ⟨hzK, hfixed⟩ :=
    ReeTwo.FixingExtension.nonstandard_firstCore_obstruction_of_two_certificate
      htwo hcardT j aT k hk hgen hjconj hjfour
  obtain ⟨hzS, eS, heS⟩ := ctx.marked_equiv_local_sylow T z hz hzgen
    ⟨hez ▸ twoCoreIn_le ctx.second (e.symm (ReeTwo.Core.root 9)).property,
      by simpa only [← hez] using hQT (e.symm (ReeTwo.Core.root 9))⟩
  have hfirst := ctx.first_core_eq_second_center_centralizer hS e
  have hcoreS : twoCoreIn ctx.first ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.first :=
      ctx.terminal.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
    rintro x ⟨p, hp, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.first)).le_sylow_of_normal (S.subtype hSP) hp
  let eK : twoCoreIn ctx.first ≃* ReeTwo.FixingExtension.firstCore T :=
    (subgroupOfEquivOfLe hcoreS).symm.trans
      ((MulEquiv.subgroupCongr hfirst).trans (centralizerUpperCentralSeriesEquiv eS 2))
  let zK : ReeTwo.FixingExtension.firstCore T := ⟨j (ReeTwo.Core.root 9), hzK⟩
  apply ctx.first_core_not_equiv_fixed_involution
    ⟨z, ctx.central_involution_mem_first_core z hzgen⟩ hz hzgen zK hfixed
  refine ⟨eK, ?_⟩
  apply Subtype.ext
  apply hi
  exact heS.trans hjz.symm

/-- The complete actual-coordinate selection, conditional only on the
independent split base-two certificate. All original markings are retained. -/
public theorem LargeTerminalContext.exists_ree_standard_census_action_of_two_certificate
    (htwo : ∀ b : MulAut (ReeTwo.FixingModel.firstCore 2 false),
      b (ReeTwo.FixingModel.centralInvolution 2 false) =
        ReeTwo.FixingModel.centralInvolution 2 false)
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ (e : twoCoreIn ctx.second ≃* ReeTwo.Core) (c a : ctx.second) (i : Fin 20),
      (e.symm (ReeTwo.Core.root 9) : G) = z ∧
      zpowers (e.symm (ReeTwo.Core.root 2) : G) =
        twoCoreIn ctx.second ⊓ centralizer (A : Set G) ∧
      zpowers (c : G) = A ∧ c ^ 5 = 1 ∧ a ^ 4 = 1 ∧
      a * c * a⁻¹ = c ^ 2 ∧
      ctx.reeCoreAction e c = ReeTwo.Core.c ∧
      ctx.reeCoreAction e a = ReeTwo.Core.FixingActionCensus.representative i ∧
      ReeTwo.Core.FixingActionCensus.IsStandard i := by
  obtain ⟨e, c, a, i, hez, het, hcA, hc5, ha4, hac, hc, ha⟩ :=
    ctx.exists_ree_census_action_of_cyclic hS A hA hAP hAN hcard hcyc hfixed z hz hgen
  exact ⟨e, c, a, i, hez, het, hcA, hc5, ha4, hac, hc, ha,
    ctx.ree_census_standard_of_two_certificate htwo hS A hA hAP z hz hgen
      e c a i hez hcA ha4 hac ha⟩

/-- Standard fixing coordinates for the actual terminal core. The root-nine
mark, cyclic fixed subgroup at root two, and order-five subgroup are retained. -/
public theorem LargeTerminalContext.exists_ree_standard_census_action_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ (e : twoCoreIn ctx.second ≃* ReeTwo.Core) (c a : ctx.second) (i : Fin 20),
      (e.symm (ReeTwo.Core.root 9) : G) = z ∧
      zpowers (e.symm (ReeTwo.Core.root 2) : G) =
        twoCoreIn ctx.second ⊓ centralizer (A : Set G) ∧
      zpowers (c : G) = A ∧ c ^ 5 = 1 ∧ a ^ 4 = 1 ∧
      a * c * a⁻¹ = c ^ 2 ∧
      ctx.reeCoreAction e c = ReeTwo.Core.c ∧
      ctx.reeCoreAction e a = ReeTwo.Core.FixingActionCensus.representative i ∧
      ReeTwo.Core.FixingActionCensus.IsStandard i := by
  exact ctx.exists_ree_standard_census_action_of_two_certificate
    ReeTwo.FixingModel.two_false_fixed hS A hA hAP hAN hcard hcyc hfixed z hz hgen

end Stellmacher.Recognition
