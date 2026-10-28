module

public import Stellmacher.Recognition.LargeTerminalFiveFixedInvolution
public import Stellmacher.Recognition.LargeTerminalLargeCore

/-!
# Local input to the four-fixed odd-local exclusions

The first residual has center equal to the order-two omega-center of the
prescribed Sylow. Consequently its normalizer centralizes that involution,
and the original five-subgroup lies in its full centralizer. The full
centralizer core can be identified using this specified involution. The second
local group has order 20480; normalizer confinement there therefore upgrades
the five-subgroup to an ambient Sylow subgroup and gives the nonfusion conclusion.

These are local reductions for the odd-local arguments in Thompson VI,
printed p.630. Ambient normalizer confinement is a separate assertion;
normalizing the residual is not assumed for the normalizer of the
five-subgroup.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

universe u

/-- The residual normalizer fixes the unique nonidentity element of its center. -/
public theorem LargeTerminalContext.residual_normalizer_le_involution_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    normalizer (ctx.firstResidual : Set G) ≤ centralizer ({z} : Set G) := by
  let R := ctx.firstResidual
  have hNC : normalizer (R : Set G) ≤ normalizer (centralizer (R : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (R : Set G))).mp
      inferInstance
  have hNZ : normalizer (R : Set G) ≤ normalizer (CenterAmbient R : Set G) := by
    rw [SectionEight.eight_six_centerAmbient_eq_inf_centralizer]
    exact (le_inf le_rfl hNC).trans inf_normalizer_le_normalizer_inf
  have hcenter : CenterAmbient R = zpowers z :=
    ctx.first_residual_center_eq_omegaOneCenter.trans hgen.symm
  rw [hcenter] at hNZ
  have hAut : Nat.card (MulAut (zpowers z)) = 1 := by
    rw [IsCyclic.card_mulAut, Nat.card_zpowers, hz]
    decide
  let _ : Subsingleton (MulAut (zpowers z)) := (Nat.card_eq_one_iff_unique.mp hAut).1
  intro g hg
  have he : (zpowers z).normalizerMonoidHom ⟨g, hNZ hg⟩ = 1 := Subsingleton.elim _ _
  have hv := congrArg (fun a : MulAut (zpowers z) => (a ⟨z, mem_zpowers z⟩ : G)) he
  change g * z * g⁻¹ = z at hv
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hv)

/-- The second local group normalizes the first residual, as inherited
from the characteristic two-core of its two-residual. -/
public theorem LargeTerminalContext.second_le_residual_normalizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ctx.second ≤ normalizer (ctx.firstResidual : Set G) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let P := GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  let E := EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  have hE : E = twoResidualIn P := ctx.terminal.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : twoCoreIn E ≤ P := (twoCoreIn_le E).trans hEP
  have hPN : P ≤ normalizer (twoCoreIn E : Set K) :=
    (normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  rw [← hmap]
  exact (map_mono hPN).trans (le_normalizer_map K.subtype)

/-- The actual residual has a four-dimensional Frattini quotient. This
intrinsic conclusion does not require it to be the full centralizer core. -/
public theorem LargeTerminalContext.first_residual_frattini_structure
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    commutator ctx.firstResidual = frattini ctx.firstResidual ∧
      Nat.card (ctx.firstResidual ⧸ frattini ctx.firstResidual) = 16 := by
  let R := ctx.firstResidual
  obtain ⟨A, hA, _, hAN, hfixed⟩ := ctx.exists_five_subgroup_fixed_center
  let _ : MulDistribMulAction A R :=
    conjMulDistribMulActionOfLeNormalizer A R hAN
  have hfixed' : FixedPoints.subgroup A R ≤ center R := by
    intro r hr
    apply hfixed
    change (r : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have heq := congrArg R.subtype (hr ⟨a, ha⟩)
    change a * (r : G) * a⁻¹ = (r : G) at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  have hR : Nat.card R = 512 := ctx.first_residual_structure.1
  have htwo : IsPGroup 2 R := IsPGroup.of_card (n := 9) (by simpa using hR)
  have hclass : 3 ≤ Group.nilpotencyClass R :=
    ctx.first_residual_structure.2.2.2.2.2.ge
  obtain ⟨_, _, hPhi, _, _, hD⟩ :=
    Theory.GroupAction.parrott_twoGroup_structure htwo hR hclass hA hfixed'
  refine ⟨hPhi, ?_⟩
  have hPhiCard : Nat.card (frattini R) = 32 := hPhi ▸ hD
  have hcount := (frattini R).card_mul_index
  rw [hPhiCard, hR, index_eq_card] at hcount
  change Nat.card (R ⧸ frattini R) = 16
  omega

/-- The order-1024 second core has Frattini quotient of order at most 32:
its Frattini subgroup contains the order-32 derived residual. -/
public theorem LargeTerminalContext.second_core_frattini_quotient_card_le
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    Nat.card (twoCoreIn ctx.second ⧸ frattini (twoCoreIn ctx.second)) ≤ 32 := by
  let Q := twoCoreIn ctx.second
  let R := ctx.firstResidual
  have htwo : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := ctx.second)).map _
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  obtain ⟨_, _, _, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  have hRQ : R ≤ Q := hlow.trans hhigh
  let f : R →* Q := inclusion hRQ
  have hDPhi : (commutator R).map f ≤ frattini Q := by
    rw [map_commutator_eq]
    exact (commutator_mono le_top le_top).trans
      (commutator_le_frattini_of_isPGroup (p := 2))
  have hDcard : Nat.card ((commutator R).map f) = 32 :=
    (card_map_of_injective (inclusion_injective hRQ)).trans
      ctx.first_residual_structure.2.2.2.2.1
  have hlower : 32 ≤ Nat.card (frattini Q) := hDcard ▸ card_le_of_le hDPhi
  obtain ⟨z, _, _, hcore, hcard⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
  have hQcard : Nat.card Q = 1024 := by
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← hcore]
    exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hcard
  have hcount := (frattini Q).card_mul_index
  rw [hQcard, index_eq_card] at hcount
  change Nat.card (Q ⧸ frattini Q) ≤ 32
  nlinarith

/-- The second local group has order five times the prescribed Sylow order. -/
public theorem LargeTerminalContext.second_card_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    Nat.card ctx.second = 20480 := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  let P := GAt ctx.terminal.Γ cp.firstStep
  let Q := QAt ctx.terminal.Γ cp.firstStep
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hratio := SectionTen.ten_one_large_sylow_card tenCtx middle hpath ctx.noTransvections
  have hT : Nat.card ((S : Subgroup G).subgroupOf K) = 4096 :=
    (Nat.card_congr (subgroupOfEquivOfLe ctx.terminal.sylow_le_join).toEquiv).trans hS
  have hQcard : Nat.card Q = 1024 := by
    change Nat.card ((S : Subgroup G).subgroupOf K) = 4 * Nat.card Q at hratio
    rw [hT] at hratio
    omega
  obtain ⟨φ, _, projection, hsurj, hker⟩ :=
    SectionTen.ten_one_large_first_frobenius tenCtx middle hpath ctx.noTransvections
  have hmodel : Nat.card (SemidirectProduct C5 C4 φ) = 20 := by
    rw [SemidirectProduct.card]
    simp [C5, C4]
  have hQP : Q ≤ P := by
    change ctx.terminal.Γ.twoCoreAt _ ≤ P
    rw [ctx.terminal.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hkcard : Nat.card projection.ker = 1024 := by
    rw [hker]
    change Nat.card (Q.subgroupOf P) = 1024
    rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv, hQcard]
  have hi : projection.ker.index = 20 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top, hmodel]
  have hPcard : Nat.card P = 20480 := by
    have hc := projection.ker.card_mul_index
    rw [hkcard, hi] at hc
    exact hc.symm
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  rw [← hmap, card_map_of_injective K.subtype_injective, hPcard]

/-- The supplied five-subgroup centralizes the omega-central involution by
its given residual normalization; this does not assert ambient Sylow status. -/
public theorem LargeTerminalContext.five_le_involution_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    A ≤ centralizer ({z} : Set G) :=
  hAN.trans (ctx.residual_normalizer_le_involution_centralizer z hz hgen)

/-- The upper-endpoint core equality holds for the specified generator,
not just the existential generator in the earlier core theorem. -/
public theorem LargeTerminalContext.involution_centralizer_core_eq_at_generator
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    twoCoreIn (centralizer ({z} : Set G)) = twoCoreIn ctx.second ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G))) = 1024 := by
  obtain ⟨w, _, hw, hcore, hcard⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
  have heq : centralizer ({w} : Set G) = centralizer ({z} : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure, hw,
      ← hgen, zpowers_eq_closure, centralizer_closure]
  exact ⟨heq ▸ hcore, heq ▸ hcard⟩

/-- Normalizer confinement upgrades the order-five subgroup to an ambient
Sylow subgroup. The key input is the normalizer congruence modulo 25. -/
public theorem LargeTerminalContext.exists_sylow_five_of_normalizer_le_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second) :
    ∃ P : Sylow 5 G, (P : Subgroup G) = A := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hNcard : Nat.card (normalizer (A : Set G)) ∣ 20480 :=
    ctx.second_card_of_large_card hS ▸ card_dvd_of_le hN
  have hmod : Nat.card (normalizer (A : Set G)) ≡ Nat.card G [MOD 25] :=
    Sylow.card_normalizer_modEq_card (p := 5) (n := 1) (by simpa using hA)
  have h25 : ¬ 25 ∣ Nat.card G := by
    intro h
    have hbad := ((hmod.dvd_iff (dvd_refl 25)).mpr h).trans hNcard
    norm_num at hbad
  have hindex : ¬ 5 ∣ A.index := by
    intro h
    apply h25
    have hc := A.card_mul_index
    rw [hA] at hc
    rw [← hc]
    exact Nat.mul_dvd_mul_left 5 h
  exact ⟨(IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)).toSylow hindex, rfl⟩

/-- The source's nonfusion conclusion follows once the ambient five-normalizer
is confined to the actual second local group. -/
public theorem LargeTerminalContext.not_isConj_of_five_normalizer_le_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hN : normalizer (A : Set G) ≤ ctx.second)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ¬ IsConj z y := by
  obtain ⟨P, hP⟩ := ctx.exists_sylow_five_of_normalizer_le_second hS A hA hN
  have hPC : normalizer (P : Set G) ≤ centralizer ({z} : Set G) := by
    change normalizer ((P : Subgroup G) : Set G) ≤ _
    rw [hP]
    exact hN.trans (ctx.second_le_residual_normalizer.trans
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen))
  apply ctx.not_isConj_of_five_sylow_normalizer P z hgen hPC y _ hyR
  change y ∈ centralizer ((P : Subgroup G) : Set G)
  rwa [hP]

/-- The noncyclic fixed group, as an actual ambient subgroup, is a four-group
containing the distinguished line. Its intersection with the residual is exactly
that line, and its normalizer is a solvable two-local group of characteristic two.
This supplies local data; no invariance under the full five-centralizer is asserted. -/
public theorem LargeTerminalContext.five_fixed_four_ambient_data
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    let F := twoCoreIn ctx.second ⊓ centralizer (A : Set G)
    IsKleinFour F ∧ omegaOneCenter (S : Subgroup G) ≤ F ∧
      F ⊓ ctx.firstResidual = omegaOneCenter (S : Subgroup G) ∧
      IsTwoLocal (normalizer (F : Set G)) ∧
      Group.IsSolvable (normalizer (F : Set G)) ∧
      IsCharacteristicTwoType (normalizer (F : Set G)) := by
  let Q := twoCoreIn ctx.second
  let C := centralizer (A : Set G)
  let F := Q ⊓ C
  let FQ := C.subgroupOf Q
  let e : FQ ≃* F :=
    (FQ.equivMapOfInjective Q.subtype Q.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [subgroupOf_map_subtype, inf_comm]))
  have hFcard : Nat.card F = 4 := (Nat.card_congr e.toEquiv).symm.trans hcard
  have hFncyc : ¬ IsCyclic F := by
    intro h
    let _ := h
    exact hncyc (isCyclic_of_injective e.toMonoidHom e.injective)
  have hFfour : IsKleinFour F :=
    ⟨hFcard, (not_isCyclic_iff_exponent_eq_prime Nat.prime_two hFcard).mp hFncyc⟩
  have hFtwo : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by simpa only [Nat.reducePow] using hFcard)
  have hFne : F ≠ ⊥ := by
    intro h
    simp [h] at hFcard
  have hlocal : IsTwoLocal (normalizer (F : Set G)) := ⟨F, hFne, hFtwo, rfl⟩
  obtain ⟨z, hz, hgen, hlo, hhi, _⟩ := ctx.involution_centralizer_core
  have hZR : omegaOneCenter (S : Subgroup G) ≤ ctx.firstResidual := by
    rw [← ctx.first_residual_center_eq_omegaOneCenter]
    exact map_subtype_le _
  have hZC : omegaOneCenter (S : Subgroup G) ≤ C := by
    have hAC := ctx.five_le_involution_centralizer A hAN z hz hgen
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen] at hAC
    exact le_centralizer_iff.mp hAC
  have hZF : omegaOneCenter (S : Subgroup G) ≤ F :=
    le_inf (hZR.trans (hlo.trans hhi)) hZC
  have hFR : F ⊓ ctx.firstResidual = omegaOneCenter (S : Subgroup G) := by
    apply le_antisymm _ (le_inf hZF hZR)
    intro x hx
    rw [← ctx.first_residual_center_eq_omegaOneCenter]
    exact mem_map.mpr ⟨⟨x, hx.2⟩, hfixed hx.1.2, rfl⟩
  exact ⟨hFfour, hZF, hFR, hlocal, ctx.localStructure _ hlocal⟩

end Stellmacher.Recognition
