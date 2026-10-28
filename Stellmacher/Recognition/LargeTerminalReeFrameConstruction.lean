module

public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Stellmacher.Recognition.LargeTerminalFiveFixedConjugateGeometry
public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Stellmacher.Recognition.LargeTerminalFiveLocalAutomorphisms
public import Theory.GroupAction.Order512FiveOrbit
public import Theory.SpecificGroups.ReeTwo.CoreFrame
public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionFrame
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# A normalized Ree frame in the terminal core

The cyclic five-fixed subgroup supplies a root t with prescribed square z.
The terminal module supplies an involution b in the first residual R outside
its derived subgroup D. Parrott's irreducible five-action shows that the
conjugates of b under the actual five-subgroup generate R. At the upper
endpoint R has index two in the core Q, so t and this orbit generate Q.
The fixed root centralizes D, with C_R(t) = D and [R,⟨t⟩] = D.
The first forced tail [b,t] is a nontrivial involution commuting with b and t.
The full local five-normalizer supplies an additional symmetry: it squares
the five-subgroup and sends the cyclic fixed root to itself or its inverse.
This retains the native local action needed to distinguish cyclic extensions
of the same residual; the five-action alone does not select that extension.

The final theorem transports these intrinsic data into the second core and
applies semilinear normalization to construct `ReeTwo.FrameCoordinates`.
It preserves the designated central involution and the cyclic fixed root.
The frame elements may lie outside the residual; no frame or presentation
is assumed.

Sources: Thompson VI, pp.629–630; Parrott (1972), Lemma 1 and its subsequent
properties on pp.672–674; Shinoda (1975), (2.3), pp.81–82 for the intended
normalized coordinates. Cyclicity of the fixed subgroup is an explicit input.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped commutatorElement

private theorem conjugate_order_four_generator
    {G : Type*} [Group G] [Finite G] (t s : G) (ht : orderOf t = 4)
    (hs : s ∈ normalizer (zpowers t : Set G)) :
    s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t⁻¹ := by
  classical
  have ht4 : t ^ 4 = 1 := ht ▸ pow_orderOf_eq_one t
  have hmem : s * t * s⁻¹ ∈ zpowers t := (hs t).mp (mem_zpowers t)
  have horder : orderOf (s * t * s⁻¹) = 4 := (MulAut.conj s).orderOf_eq t |>.trans ht
  rw [mem_zpowers_iff_mem_range_orderOf, ht] at hmem
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hmem
  have hn4 := Finset.mem_range.mp hn
  interval_cases n
  · simp only [pow_zero] at he
    rw [← he, orderOf_one] at horder
    contradiction
  · exact Or.inl (by simpa only [pow_one] using he.symm)
  · have htwo : (s * t * s⁻¹) ^ 2 = 1 := by
      rw [← he, ← pow_mul]
      exact ht4
    have hd := orderOf_dvd_of_pow_eq_one htwo
    rw [horder] at hd
    norm_num at hd
  · apply Or.inr
    rw [← he]
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using ht4

/-- The native local action supplies a squaring symmetry of every chosen
cyclic fixed root. No order-four lift or pointwise fixation of the root is
assumed: the symmetry may invert the root. Both the residual and the full
core are preserved, so this symmetry acts on all their characteristic layers. -/
public theorem LargeTerminalContext.exists_five_squaring_root_symmetry
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (t : G) (ht : orderOf t = 4)
    (hgen : zpowers t = twoCoreIn ctx.second ⊓ centralizer (A : Set G)) :
    ∃ s : G, s ∈ ctx.second ∧
      s ∈ normalizer (ctx.firstResidual : Set G) ∧
      s ∈ normalizer (twoCoreIn ctx.second : Set G) ∧
      s ∈ normalizer (A : Set G) ∧
      (∀ c ∈ A, s * c * s⁻¹ = c ^ 2) ∧
      (s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t⁻¹) := by
  obtain ⟨s, hsP, hsA, hs⟩ := ctx.exists_five_squaring_element hS A hA hAP
  have hsQ : s ∈ normalizer (twoCoreIn ctx.second : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.second)).mp
      (twoCoreIn_normal ctx.second)) hsP
  have hsF : s ∈ normalizer (zpowers t : Set G) := by
    rw [hgen]
    exact inf_normalizer_le_normalizer_inf
      ⟨hsQ, normalizer_le_normalizer_centralizer A hsA⟩
  exact ⟨s, hsP, ctx.second_le_residual_normalizer hsP, hsQ, hsA, hs,
    conjugate_order_four_generator t s ht hsF⟩

/-- The squaring symmetry acts on the actual second core and intertwines
the supplied five-action with its square. This is the additional intrinsic
automorphism input for normalizing the residual's cyclic extension. -/
public theorem LargeTerminalContext.exists_five_squaring_core_automorphism
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (t : twoCoreIn ctx.second) (ht : orderOf (t : G) = 4)
    (hgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G)) :
    ∃ (ρ : A →* MulAut (twoCoreIn ctx.second)) (σ : MulAut (twoCoreIn ctx.second)),
      (∀ a q, (ρ a q : G) = (a : G) * (q : G) * (a : G)⁻¹) ∧
      (∀ a, σ * ρ a * σ⁻¹ = ρ (a ^ 2)) ∧
      (∀ a, ρ a t = t) ∧
      (σ t = t ∨ σ t = t⁻¹) ∧
      (∀ q, (σ q : G) ∈ ctx.firstResidual ↔ (q : G) ∈ ctx.firstResidual) := by
  let Q := twoCoreIn ctx.second
  have hPN : ctx.second ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.second)).mp
      (twoCoreIn_normal ctx.second)
  let f : ctx.second →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hPN)
  let ρ : A →* MulAut Q := f.comp (inclusion hAP)
  obtain ⟨s, hsP, hsR, _, _, hs, hst⟩ :=
    ctx.exists_five_squaring_root_symmetry hS A hA hAP t ht hgen
  let sP : ctx.second := ⟨s, hsP⟩
  let σ := f sP
  have htA : (t : G) ∈ centralizer (A : Set G) :=
    (hgen.le (mem_zpowers (t : G))).2
  refine ⟨ρ, σ, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro a
    have he : sP * inclusion hAP a * sP⁻¹ = inclusion hAP (a ^ 2) :=
      Subtype.ext (hs a a.property)
    change f sP * f (inclusion hAP a) * (f sP)⁻¹ = f (inclusion hAP (a ^ 2))
    rw [← map_inv, ← map_mul, ← map_mul, he]
  · intro a
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp htA a a.property)
  · rcases hst with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · intro q
    exact ((mem_normalizer_iff.mp hsR) (q : G)).symm

/-- Every element outside the derived residual has a five-orbit generating the
literal ambient residual. The action is conjugation by the supplied subgroup. -/
public theorem LargeTerminalContext.five_orbit_generates_first_residual
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (b : ctx.firstResidual) (hb : b ∉ commutator ctx.firstResidual) :
    closure (Set.range (fun a : A => (a : G) * (b : G) * (a : G)⁻¹)) =
      ctx.firstResidual := by
  let R := ctx.firstResidual
  let _ : MulDistribMulAction A R := conjMulDistribMulActionOfLeNormalizer A R hAN
  have hfix : FixedPoints.subgroup A R ≤ center R := by
    intro r hr
    apply hfixed
    apply mem_centralizer_iff.mpr
    intro a ha
    have hh := congrArg (fun x : R => (x : G)) (hr ⟨a, ha⟩)
    change a * (r : G) * a⁻¹ = (r : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hgen := Theory.GroupAction.parrott_orbit_closure_eq_top
    (IsPGroup.of_card (n := 9) ctx.first_residual_structure.1)
    ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge
    hA hfix b hb
  have hm := congrArg (Subgroup.map R.subtype) hgen
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- At the upper endpoint, any core element outside the residual supplements it.
In particular this applies to the generator of the cyclic five-fixed subgroup. -/
public theorem LargeTerminalContext.first_residual_sup_zpowers_eq_second_core
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second) (htR : t ∉ ctx.firstResidual) :
    ctx.firstResidual ⊔ zpowers t = twoCoreIn ctx.second := by
  let R := ctx.firstResidual
  let Q := twoCoreIn ctx.second
  let H := R ⊔ zpowers t
  have hRQ : R ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  have hHQ : H ≤ Q := sup_le hRQ (zpowers_le.mpr htQ)
  have hRH : R ≤ H := le_sup_left
  have hQS : Q ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hQcard : Nat.card Q = 1024 := by
    have hh := ctx.local_character_core_card hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at hh
  have hRcard : Nat.card R = 512 := ctx.first_residual_structure.1
  have hne : R ≠ H := by
    intro he
    apply htR
    change t ∈ R
    rw [he]
    exact (show zpowers t ≤ H from le_sup_right) (mem_zpowers t)
  have hlarge : 512 < Nat.card H := by
    by_contra hn
    exact hne (eq_of_le_of_card_ge hRH (by omega))
  obtain ⟨k, hk⟩ := card_dvd_of_le hRH
  rw [hRcard] at hk
  apply eq_of_le_of_card_ge hHQ
  rw [hQcard]
  omega

/-- Construct a fixed cyclic root and an actual residual involution whose
five-orbit generates the residual and, together with the root, the whole core.
This is input to the coordinate normalization, not a claim of frame existence. -/
public theorem LargeTerminalContext.exists_ree_generating_seed_of_cyclic
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : twoCoreIn ctx.second) (hz : orderOf (z : G) = 2)
    (hgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G)) :
    ∃ (t : twoCoreIn ctx.second) (b : ctx.firstResidual),
      (t : G) ∈ centralizer (A : Set G) ∧ t ^ 2 = z ∧
      zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G) ∧
      (t : G) ∉ ctx.firstResidual ∧ orderOf t = 4 ∧
      (t : G) ∈ centralizer (DerivedAmbient ctx.firstResidual : Set G) ∧
      ctx.firstResidual ⊓ centralizer ({(t : G)} : Set G) =
        DerivedAmbient ctx.firstResidual ∧
      ⁅ctx.firstResidual, zpowers (t : G)⁆ = DerivedAmbient ctx.firstResidual ∧
      (b : G) ∈ ctx.terminalModule ∧ orderOf b = 2 ∧
      b ∉ commutator ctx.firstResidual ∧
      closure (Set.range (fun a : A => (a : G) * (b : G) * (a : G)⁻¹)) =
        ctx.firstResidual ∧
      closure (Set.range (fun a : A => (a : G) * (b : G) * (a : G)⁻¹)) ⊔
        zpowers (t : G) = twoCoreIn ctx.second := by
  obtain ⟨t, htQ, htA, htR, ht4, ht2, htgen⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  obtain ⟨b, hbE, hbR, _, hbC, hb2⟩ := ctx.exists_terminal_module_outer_involution
  let bR : ctx.firstResidual := ⟨b, hbR⟩
  let tQ : twoCoreIn ctx.second := ⟨t, htQ⟩
  have hbD : bR ∉ commutator ctx.firstResidual := by
    intro h
    apply hbC
    let _ := ctx.derived_residual_elementary
    exact le_centralizer (DerivedAmbient ctx.firstResidual)
      (mem_map_of_mem ctx.firstResidual.subtype h)
  refine ⟨tQ, bR, htA, Subtype.ext ht2, htgen, htR, ?_,
    ctx.five_fixed_centralizes_derived A hA hAN hfixed t htQ htA,
    ctx.five_fixed_residual_centralizer_eq_derived A hA hAN hfixed t htQ htA htR,
    ctx.five_fixed_residual_commutator_eq_derived A hA hAN hfixed t htQ htA htR,
    hbE, ?_, hbD,
    ctx.five_orbit_generates_first_residual A hA hAN hfixed bR hbD, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact ht4
  · rw [← Subgroup.orderOf_coe]
    exact hb2
  · rw [ctx.five_orbit_generates_first_residual A hA hAN hfixed bR hbD]
    exact ctx.first_residual_sup_zpowers_eq_second_core hS t htQ htR

/-- The first forced tail root is an involution commuting with both its
involutory seed and the fixed root. All elements here are actual group elements. -/
public theorem LargeTerminalContext.ree_seed_tail_involution
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t : twoCoreIn ctx.second) (htA : (t : G) ∈ centralizer (A : Set G))
    (htR : (t : G) ∉ ctx.firstResidual)
    (b : ctx.firstResidual) (hb : b ∉ commutator ctx.firstResidual) (hb2 : b ^ 2 = 1) :
    ReeTwo.rightComm (b : G) (t : G) ∈ DerivedAmbient ctx.firstResidual ∧
      orderOf (ReeTwo.rightComm (b : G) (t : G)) = 2 ∧
      ReeTwo.rightComm (t : G) (ReeTwo.rightComm (b : G) (t : G)) = 1 ∧
      ReeTwo.rightComm (b : G) (ReeTwo.rightComm (b : G) (t : G)) = 1 := by
  let d := ReeTwo.rightComm (b : G) (t : G)
  have hRQ : ctx.firstResidual ≤ twoCoreIn ctx.second :=
    ctx.derived_centralizer_supplement.1 ▸ le_sup_right
  have hd : d ∈ DerivedAmbient ctx.firstResidual := by
    rw [← ctx.second_core_derived_eq]
    change d ∈ (commutator (twoCoreIn ctx.second)).map (twoCoreIn ctx.second).subtype
    rw [map_subtype_commutator]
    simpa only [d, ReeTwo.rightComm, commutatorElement_def, inv_inv] using
      commutator_mem_commutator
      ((twoCoreIn ctx.second).inv_mem (hRQ b.property))
      ((twoCoreIn ctx.second).inv_mem t.property)
  have hdne : d ≠ 1 := by
    intro he
    have hc : Commute (b : G)⁻¹ (t : G)⁻¹ :=
      commutatorElement_eq_one_iff_commute.mp (by
        simpa only [d, ReeTwo.rightComm, commutatorElement_def, inv_inv] using he)
    have hc' : Commute (b : G) (t : G) := by
      simpa only [inv_inv] using hc.inv_inv
    have hbD : (b : G) ∈ DerivedAmbient ctx.firstResidual := by
      rw [← ctx.five_fixed_residual_centralizer_eq_derived A hA hAN hfixed
        t t.property htA htR]
      exact ⟨b.property, mem_centralizer_singleton_iff.mpr hc'⟩
    obtain ⟨r, hr, heq⟩ := hbD
    have hrb : r = b := Subtype.ext heq
    exact hb (hrb ▸ hr)
  let _ := ctx.derived_residual_elementary
  have hd2 : d ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian
    (p := 2) d hd
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hd, orderOf_eq_prime hd2 hdne, ?_, ?_⟩
  · have htd : Commute (t : G) d :=
      (mem_centralizer_iff.mp (ctx.five_fixed_centralizes_derived
        A hA hAN hfixed t t.property htA) d hd).symm
    simpa only [d, ReeTwo.rightComm, commutatorElement_def, inv_inv] using
      commutatorElement_eq_one_iff_commute.mpr htd.inv_inv
  · have hbG : (b : G) ^ 2 = 1 := congrArg (fun r : ctx.firstResidual => (r : G)) hb2
    have hbInv : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hbG)
    have hdInv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hd2)
    have hbb : (b : G) * b = 1 := by simpa only [pow_two] using hbG
    have hc : (b : G) * d = d * b := by
      calc
        (b : G) * d = (t : G)⁻¹ * b * t := by dsimp [d, ReeTwo.rightComm]; group
        _ = ((t : G)⁻¹ * (b : G)⁻¹ * t) * ((b : G) * b) := by rw [hbInv, hbb, mul_one]
        _ = d⁻¹ * b := by dsimp [d, ReeTwo.rightComm]; group
        _ = _ := by rw [hdInv]
    change (b : G)⁻¹ * d⁻¹ * b * d = 1
    calc
      _ = (d * b)⁻¹ * ((b : G) * d) := by group
      _ = 1 := by rw [hc, inv_mul_cancel]

private theorem frame_map_relative_centralizer
    {K L : Type*} [Group K] [Group L] (U V : Subgroup K) (f : K →* L)
    (hf : Function.Injective f) :
    (U ⊓ centralizer (V : Set K)).map f =
      U.map f ⊓ centralizer (V.map f : Set L) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_map_of_mem f hx.1, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx.2 v hv)
  · rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
    refine mem_map_of_mem f ⟨hx, mem_centralizer_iff.mpr ?_⟩
    intro v hv
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f v) (mem_map_of_mem f hv)

/-- The actual terminal geometry supplies a normalized four-element Ree frame,
with the prescribed central involution and a generator of the cyclic fixed four. -/
public theorem LargeTerminalContext.exists_ree_frame_of_cyclic
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : twoCoreIn ctx.second) (hz : orderOf (z : G) = 2)
    (hgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G)) :
    ∃ (t : twoCoreIn ctx.second) (a : Fin 4 → twoCoreIn ctx.second),
      (t : G) ∈ centralizer (A : Set G) ∧ t ^ 2 = z ∧
      zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G) ∧
      ReeTwo.FrameCoordinates a t z := by
  obtain ⟨t, b, htA, ht2, htgen, htR, ht4, htD, htC, htcomm,
    _, hb2, hbD, hborbit, hgenerate⟩ :=
    ctx.exists_ree_generating_seed_of_cyclic hS A hA hAN hcard hcyc hfixed z hz hgen
  obtain ⟨ρ, σ, hρ, hσsq, hρt, hσt, hσR⟩ :=
    ctx.exists_five_squaring_core_automorphism hS A hA hAP t
      (by simpa only [orderOf_submonoid] using ht4) htgen
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := twoCoreIn ctx.second
  let R := ctx.firstResidual.subgroupOf Q
  have hRQ : ctx.firstResidual ≤ Q := by
    change ctx.firstResidual ≤ twoCoreIn ctx.second
    rw [ctx.derived_centralizer_supplement.1]
    exact le_sup_right
  let e : R ≃* ctx.firstResidual := subgroupOfEquivOfLe hRQ
  let bR : R := e.symm b
  let D := (commutator R).map R.subtype
  let Z := (center R).map R.subtype
  have hRmap : R.map Q.subtype = ctx.firstResidual := map_subgroupOf_eq_of_le hRQ
  have hecomp : ctx.firstResidual.subtype.comp e.toMonoidHom = Q.subtype.comp R.subtype := rfl
  have hcomm_e : (commutator R).map e.toMonoidHom = commutator ctx.firstResidual := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hcenter_e : (center R).map e.toMonoidHom = center ctx.firstResidual := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e ⟨y, hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
  have hDmap : D.map Q.subtype = DerivedAmbient ctx.firstResidual := by
    change ((commutator R).map R.subtype).map Q.subtype =
      (commutator ctx.firstResidual).map ctx.firstResidual.subtype
    rw [← hcomm_e, map_map, map_map, hecomp]
  have hZmap : Z.map Q.subtype = CenterAmbient ctx.firstResidual := by
    change ((center R).map R.subtype).map Q.subtype =
      (center ctx.firstResidual).map ctx.firstResidual.subtype
    rw [← hcenter_e, map_map, map_map, hecomp]
  have hDsub : D = (DerivedAmbient ctx.firstResidual).subgroupOf Q := by
    rw [← hDmap]
    exact (comap_map_eq_self_of_injective Q.subtype_injective D).symm
  have hZsub : Z = (CenterAmbient ctx.firstResidual).subgroupOf Q := by
    rw [← hZmap]
    exact (comap_map_eq_self_of_injective Q.subtype_injective Z).symm
  have hQcard : Nat.card Q = 1024 := by
    obtain ⟨w, _, _, heq, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← heq]
    exact (card_map_of_injective (centralizer ({w} : Set G)).subtype_injective).trans hc
  have hRcard : Nat.card R = 512 :=
    (Nat.card_congr e.toEquiv).trans ctx.first_residual_structure.1
  have hRtwo : IsPGroup 2 R := IsPGroup.of_card (n := 9) hRcard
  let _ : Group.IsNilpotent R := hRtwo.isNilpotent
  let _ : Group.IsNilpotent ctx.firstResidual := (hRtwo.of_equiv e).isNilpotent
  have hclass : Group.nilpotencyClass R = 3 := by
    have hlo := Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective
    have hhi := Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective
    rw [ctx.first_residual_structure.2.2.2.2.2] at hlo hhi
    omega
  have hCZ : centralizer (R : Set Q) = Z := by
    apply map_injective Q.subtype_injective
    rw [← top_inf_eq (centralizer (R : Set Q)), frame_map_relative_centralizer _ _ _ Q.subtype_injective,
      ← MonoidHom.range_eq_map, Q.range_subtype, hRmap, hZmap]
    exact ctx.core_inf_residual_centralizer
  have hzZ : z ∈ Z := by
    rw [hZsub]
    change (z : G) ∈ CenterAmbient ctx.firstResidual
    rw [ctx.first_residual_center_eq_omegaOneCenter, ← hgen]
    exact mem_zpowers _
  have hzcenter : z ∈ center Q := by
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen
        (ctx.second_le_residual_normalizer (twoCoreIn_le ctx.second q.property)))
  have hZcyclic : Z = zpowers z := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hzZ) ?_).symm
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hz,
      card_map_of_injective R.subtype_injective]
    exact ((Nat.card_congr (centerCongr e).toEquiv).trans
      ctx.first_residual_structure.2.2.2.1).le
  have hdata : ReeTwo.SemilinearExtensionData ρ R t z bR σ := by
    refine {
      actor_card := hA
      core_card := hQcard
      residual_card := hRcard
      residual_normal := normal_subgroupOf_of_le_normalizer
        ((twoCoreIn_le ctx.second).trans ctx.second_le_residual_normalizer)
      residual_class := hclass
      invariant := ?_
      center_card := ?_
      derived_card := ?_
      derived_elementary := ?_
      derived_eq := ?_
      derived_commutator := ?_
      center_eq := ?_
      residual_derived_centralizer := ?_
      residual_centralizer := hCZ
      fixed_central := ?_
      root_outside := htR
      central_mem := hzZ
      central_order := by simpa only [orderOf_submonoid] using hz
      root_square := ht2
      root_fixed := hρt
      root_centralizes := ?_
      root_generates := ?_
      root_centralizer := ?_
      root_commutator := ?_
      seed_square := ?_
      seed_outside := ?_
      seed_generates := ?_
      symmetry_invariant := hσR
      symmetry_squares := hσsq
      symmetry_root := hσt }
    · intro a x
      change (ρ a x : G) ∈ ctx.firstResidual ↔ (x : G) ∈ ctx.firstResidual
      rw [hρ]
      exact ((mem_normalizer_iff.mp (hAN a.property)) (x : G)).symm
    · rw [card_map_of_injective R.subtype_injective]
      exact (Nat.card_congr (centerCongr e).toEquiv).trans ctx.first_residual_structure.2.2.2.1
    · rw [card_map_of_injective R.subtype_injective,
        ← card_map_of_injective (f := e.toMonoidHom) (K := commutator R) e.injective, hcomm_e]
      exact ctx.first_residual_structure.2.2.2.2.1
    · change IsElementaryAbelian 2 D
      rw [hDsub]
      let _ := ctx.derived_residual_elementary
      exact IsElementaryAbelian.subgroupOf ((map_subtype_le _).trans hRQ)
    · apply map_injective Q.subtype_injective
      exact hDmap.trans ctx.second_core_derived_eq.symm
    · apply map_injective Q.subtype_injective
      rw [map_commutator, hDmap, hZmap, ← MonoidHom.range_eq_map, Q.range_subtype]
      exact ctx.derived_commutator_second_core
    · change center Q = Z
      apply le_antisymm
      · rw [← hCZ]
        intro x hx
        apply mem_centralizer_iff.mpr
        intro r _
        exact mem_center_iff.mp hx r
      · rw [hZcyclic]
        exact zpowers_le.mpr hzcenter
    · apply map_injective Q.subtype_injective
      rw [frame_map_relative_centralizer _ _ _ Q.subtype_injective, hRmap, hDmap]
      have hh := ctx.derived_centralizer_supplement.2
      change (Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)) ⊓
        ctx.firstResidual = DerivedAmbient ctx.firstResidual at hh
      rw [inf_right_comm, inf_eq_right.mpr hRQ] at hh
      exact hh
    · intro x hx
      have hex : e x ∈ center ctx.firstResidual := by
        apply hfixed
        apply mem_centralizer_iff.mpr
        intro a ha
        have hh := congrArg (fun q : Q => (q : G)) (hx ⟨a, ha⟩)
        rw [hρ] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      exact (centerCongr e.symm ⟨e x, hex⟩).property
    · apply mem_centralizer_iff.mpr
      intro d hd
      apply Subtype.ext
      exact mem_centralizer_iff.mp htD d (hDmap ▸ mem_map_of_mem Q.subtype hd)
    · apply map_injective Q.subtype_injective
      rw [Subgroup.map_sup, hRmap, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Q.range_subtype]
      rw [hborbit] at hgenerate
      exact hgenerate
    · apply map_injective Q.subtype_injective
      rw [map_inf _ _ _ Q.subtype_injective, hRmap,
        map_subtype_centralizer_singleton, hDmap, ← inf_assoc, inf_eq_left.mpr hRQ]
      exact htC
    · apply map_injective Q.subtype_injective
      rw [map_commutator, hRmap, MonoidHom.map_zpowers, hDmap]
      exact htcomm
    · apply e.injective
      simpa only [map_pow, map_one, e.apply_symm_apply] using
        (hb2 ▸ pow_orderOf_eq_one b)
    · intro hb
      apply hbD
      rw [← hcomm_e]
      exact ⟨bR, hb, e.apply_symm_apply b⟩
    · apply map_injective Q.subtype_injective
      rw [MonoidHom.map_closure, ← Set.range_comp, hRmap]
      have hf : Q.subtype ∘ (fun a : A => ρ a (bR : Q)) =
          (fun a : A => (a : G) * (b : G) * (a : G)⁻¹) := by
        funext a
        exact hρ a bR
      rw [hf]
      exact hborbit
  obtain ⟨a, ha⟩ := hdata.exists_frameCoordinates
  exact ⟨t, a, htA, ht2, htgen, ha⟩

end Stellmacher.Recognition
