module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData

/-!
# Local centralizers for the five-fixed involution

The first residual is self-centralizing modulo its center inside the second
local core. For an involution y outside that residual and fixed by the five-group,
orbit counting bounds its residual centralizer by 32 and its local-core
centralizer by 64. The core has index four in the prescribed Sylow subgroup,
so the centralizer in that Sylow has order at most 256.

These are bounds inside the given local subgroups. They do not identify those
subgroups with the two-core of the full ambient centralizer of y, and do not
assert a bound on that core's Frattini quotient.

Source: Stellmacher (10.1)(20) and Thompson VI, printed p.630.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup

universe u

private theorem relative_centralizer_map
    {K L : Type*} [Group K] [Group L] (R V : Subgroup K) (f : K →* L)
    (hf : Function.Injective f) :
    (R ⊓ centralizer (V : Set K)).map f =
      R.map f ⊓ centralizer (V.map f : Set L) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_map_of_mem f hx.1, ?_⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨v, hv, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx.2 v hv)
  · rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
    refine mem_map_of_mem f ⟨hx, ?_⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f v) (mem_map_of_mem f hv)

/-- The residual centralizer inside the actual second core is its center. -/
public theorem LargeTerminalContext.core_inf_residual_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    twoCoreIn ctx.second ⊓ centralizer (ctx.firstResidual : Set G) =
      CenterAmbient ctx.firstResidual := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hC := ten_one_large_residual_core_centralizer tenCtx middle hpath ctx.noTransvections
    (ten_one_large_first_residual_five tenCtx middle hpath ctx.noTransvections)
  change QAt Γ cp.a' ⊓ centralizer (twoCoreIn (EAt Γ cp.a') : Set K) =
    ZAt Γ cp.a' at hC
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  obtain ⟨mover, hmove⟩ := (lemma_seven_one tenCtx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
  change Γ.act (mover : K) cp.a' = cp.firstStep at hmove
  let e := MulAut.conj (mover : K)⁻¹
  have hPmap : (GAt Γ cp.a').map e.toMonoidHom = GAt Γ cp.firstStep := by
    change conjugateBy (stabilizer Γ cp.a') (mover : K)⁻¹ = stabilizer Γ cp.firstStep
    rw [← stabilizer_act, hmove]
  have hEmap : (EAt Γ cp.a').map e.toMonoidHom = EAt Γ cp.firstStep := by
    change (Γ.twoResidualAt cp.a').map _ = Γ.twoResidualAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def, ← twoResidualIn_map_equiv]
    exact congrArg twoResidualIn hPmap
  have hRmap : (twoCoreIn (EAt Γ cp.a')).map e.toMonoidHom =
      twoCoreIn (EAt Γ cp.firstStep) := by
    rw [← twoCoreIn_map_equiv, hEmap]
  let f : K →* G := K.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.injective
  have hRimage : (twoCoreIn (EAt Γ cp.a')).map f = ctx.firstResidual := by
    change (_ : Subgroup K).map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hRmap]
    rfl
  have hZmap : (ZAt Γ cp.a').map e.toMonoidHom = ZAt Γ cp.firstStep := by
    change (z Γ cp.a').map _ = z Γ cp.firstStep
    rw [← z_act, hmove]
  have hZimage : (ZAt Γ cp.a').map f = CenterAmbient ctx.firstResidual := by
    rw [ctx.first_residual_structure.2.1]
    change (_ : Subgroup K).map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hZmap]
  have hPimage : (GAt Γ cp.a').map f = ctx.second := by
    change (_ : Subgroup K).map (K.subtype.comp e.toMonoidHom) = _
    rw [← map_map, hPmap]
    exact (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
  have hQimage : (QAt Γ cp.a').map f = twoCoreIn ctx.second := by
    change (Γ.twoCoreAt cp.a').map f = _
    rw [Γ.twoCoreAt_def]
    change (twoCoreIn (GAt Γ cp.a')).map f = _
    let j := (GAt Γ cp.a').equivMapOfInjective f hf
    have hj := pCore_map_iso 2 j
    have hc : (twoCoreIn (GAt Γ cp.a')).map f =
        twoCoreIn ((GAt Γ cp.a').map f) := by
      change ((pCore 2 (GAt Γ cp.a')).map (GAt Γ cp.a').subtype).map f =
        (pCore 2 ((GAt Γ cp.a').map f)).map ((GAt Γ cp.a').map f).subtype
      rw [← hj, map_map, map_map]
      rfl
    rw [hc, hPimage]
  have hCimage := relative_centralizer_map (QAt Γ cp.a')
    (twoCoreIn (EAt Γ cp.a')) f hf
  rw [hQimage, hRimage] at hCimage
  have hh := congrArg (fun U : Subgroup K => U.map f) hC
  rw [hCimage, hZimage] at hh
  exact hh

/-- A five-fixed element outside the residual has a small residual centralizer.
Only the given local normalizer and fixed-point hypotheses are needed. -/
public theorem LargeTerminalContext.fixed_residual_centralizer_card_le_thirtytwo
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    Nat.card (ctx.firstResidual ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 32 := by
  let R := ctx.firstResidual
  let C := centralizer ({y} : Set G)
  let D := R ⊓ C
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hyA a ha)
  have hAD : A ≤ normalizer (D : Set G) :=
    (le_inf hAN (hAC.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let _ : MulDistribMulAction A D := conjMulDistribMulActionOfLeNormalizer A D hAD
  let F := FixedPoints.subgroup A D
  have hFZ : F.map D.subtype ≤ CenterAmbient R := by
    rintro x ⟨d, hd, rfl⟩
    refine mem_map.mpr ⟨⟨(d : G), d.property.1⟩, hfixed ?_, rfl⟩
    change (d : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have hh := congrArg (fun t : D => (t : G)) (hd ⟨a, ha⟩)
    change a * (d : G) * a⁻¹ = (d : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hFbound : Nat.card F ≤ 2 := by
    have hh := card_le_of_le hFZ
    rw [card_map_of_injective D.subtype_injective] at hh
    have hZ : Nat.card (CenterAmbient R) = 2 := by
      change Nat.card ((center R).map R.subtype) = 2
      rw [card_map_of_injective R.subtype_injective]
      exact ctx.first_residual_structure.2.2.2.1
    rwa [hZ] at hh
  obtain ⟨z, hz, hgen, _, _, _⟩ := ctx.involution_centralizer_core
  have hcenter : CenterAmbient R = zpowers z :=
    ctx.first_residual_center_eq_omegaOneCenter.trans hgen.symm
  have hzR : z ∈ R := by
    have : z ∈ CenterAmbient R := hcenter ▸ mem_zpowers z
    exact map_subtype_le _ this
  have hzA : z ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact (mem_centralizer_singleton_iff.mp
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen (hAN ha)))
  have hQS : twoCoreIn ctx.second ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hzC : z ∈ C := by
    have hzS : z ∈ CenterAmbient (S : Subgroup G) :=
      omegaOneCenter_le_centerAmbient _ (hgen ▸ mem_zpowers z)
    exact mem_centralizer_singleton_iff.mpr
      ((centerAmbient_le_centralizer _ hzS) y (hQS hyQ)).symm
  let zD : D := ⟨z, hzR, hzC⟩
  have hzF : zD ∈ F := by
    intro a
    apply Subtype.ext
    change (a : G) * z * (a : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hzA a a.property)
  have hzDne : zD ≠ 1 := by
    intro hh
    have hz1 : z = 1 := congrArg (fun d : D => (d : G)) hh
    simp [hz1] at hz
  have hFne : F ≠ ⊥ := by
    intro hbot
    exact hzDne (mem_bot.mp (hbot ▸ hzF))
  have hFcard : Nat.card F = 2 := by
    have hh := (one_lt_card_iff_ne_bot F).mpr hFne
    omega
  have hdiv : Nat.card D ∣ 2 ^ 9 := by
    have hh := card_dvd_of_le (show D ≤ R from inf_le_left)
    rw [ctx.first_residual_structure.1] at hh
    exact hh
  have hproper : Nat.card D ≠ 512 := by
    intro hh
    have heq : D = R := eq_of_le_of_card_ge inf_le_left
      (by rw [hh, ctx.first_residual_structure.1])
    have hyCent : y ∈ centralizer (R : Set G) := by
      rw [mem_centralizer_iff]
      intro r hr
      exact mem_centralizer_singleton_iff.mp ((heq.ge hr).2)
    have hyZ : y ∈ CenterAmbient R :=
      ctx.core_inf_residual_centralizer ▸ (show y ∈ twoCoreIn ctx.second ⊓
        centralizer (R : Set G) from ⟨hyQ, hyCent⟩)
    exact hyR (map_subtype_le _ hyZ)
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfive : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hfive.card_modEq_card_fixedPoints D
  change Nat.card D % 5 = Nat.card F % 5 at hmod
  rw [hFcard] at hmod
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  change Nat.card D ≤ 32
  interval_cases n <;> norm_num only [Nat.reducePow] at hcard <;> omega

/-- The centralizer in the second local core has order at most 64: intersect
with the index-two residual and apply the residual bound. -/
public theorem LargeTerminalContext.fixed_core_centralizer_card_le_sixtyfour
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    Nat.card (twoCoreIn ctx.second ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 64 := by
  let R := ctx.firstResidual
  let Q := twoCoreIn ctx.second
  let C := centralizer ({y} : Set G)
  let D := Q ⊓ C
  let E := R ⊓ C
  obtain ⟨_, _, _, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  have hRQ : R ≤ Q := hlow.trans hhigh
  have hQcard : Nat.card Q = 1024 := by
    obtain ⟨z, _, _, heq, hc⟩ := ctx.involution_centralizer_core_eq_of_large_card hS
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← heq]
    exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans hc
  have hindex : R.relIndex Q = 2 := by
    have hh := (R.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv,
      ctx.first_residual_structure.1, hQcard] at hh
    change R.relIndex Q * 512 = 1024 at hh
    omega
  have hED : E ≤ D := inf_le_inf_right C hRQ
  have hEeq : E = R ⊓ D := by
    dsimp [E, D]
    rw [← inf_assoc, inf_eq_left.mpr hRQ]
  have hindexD : E.relIndex D ≤ 2 := by
    rw [hEeq, inf_relIndex_right]
    exact (relIndex_le_of_le_right (H := R) (show D ≤ Q from inf_le_left)
      (by rw [hindex]; decide)).trans_eq hindex
  have hcardE : Nat.card E ≤ 32 :=
    ctx.fixed_residual_centralizer_card_le_thirtytwo A hA hAN hfixed y hyQ hyA hyR
  have hh := (E.subgroupOf D).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hED).toEquiv] at hh
  change E.relIndex D * Nat.card E = Nat.card D at hh
  change Nat.card D ≤ 64
  calc
    Nat.card D = E.relIndex D * Nat.card E := hh.symm
    _ ≤ 2 * 32 := Nat.mul_le_mul hindexD hcardE
    _ = 64 := rfl

/-- The prescribed Sylow centralizer has order at most 256. This is a bound
on the intersection with the prescribed Sylow, without asserting that this
intersection is Sylow in the full involution centralizer. -/
public theorem LargeTerminalContext.fixed_sylow_centralizer_card_le
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    Nat.card ((S : Subgroup G) ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 256 := by
  let Q := twoCoreIn ctx.second
  let C := centralizer ({y} : Set G)
  let T := (S : Subgroup G) ⊓ C
  let D := Q ⊓ C
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hQS : Q ≤ (S : Subgroup G) := by
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hQcard : Nat.card Q = 1024 := by
    have hh := ctx.local_character_core_card hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at hh
  have hindex : Q.relIndex (S : Subgroup G) = 4 := by
    have hh := (Q.subgroupOf (S : Subgroup G)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv, hQcard] at hh
    change Q.relIndex (S : Subgroup G) * 1024 = Nat.card S at hh
    rw [hS] at hh
    omega
  have hDT : D ≤ T := inf_le_inf_right C hQS
  have hDeq : D = Q ⊓ T := by
    dsimp [D, T]
    rw [← inf_assoc, inf_eq_left.mpr hQS]
  have hindexT : D.relIndex T ≤ 4 := by
    rw [hDeq, inf_relIndex_right]
    exact (relIndex_le_of_le_right (H := Q)
      (show T ≤ (S : Subgroup G) from inf_le_left)
      (by rw [hindex]; decide)).trans_eq hindex
  have hcardD : Nat.card D ≤ 64 :=
    ctx.fixed_core_centralizer_card_le_sixtyfour hS A hA hAN hfixed y hyQ hyA hyR
  have hh := (D.subgroupOf T).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hDT).toEquiv] at hh
  change D.relIndex T * Nat.card D = Nat.card T at hh
  change Nat.card T ≤ 256
  calc
    Nat.card T = D.relIndex T * Nat.card D := hh.symm
    _ ≤ 4 * 64 := Nat.mul_le_mul hindexT hcardD
    _ = 256 := rfl

/-- The full involution-centralizer core cannot be placed inside the
residual: it contains the involution, which is outside the residual. -/
public theorem LargeTerminalContext.fixed_involution_core_not_le_residual
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (y : G) (hy : orderOf y = 2)
    (hyR : y ∉ ctx.firstResidual) :
    ¬ twoCoreIn (centralizer ({y} : Set G)) ≤ ctx.firstResidual := by
  intro h
  apply hyR
  apply h
  exact central_involution_mem_twoCore _ y
    (mem_centralizer_singleton_iff.mpr rfl) le_rfl
    (by rw [← hy]; exact pow_orderOf_eq_one y)
end Stellmacher.Recognition
