module

public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalFourFixedCoreFrattini
public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Theory.GroupAction.FourthPowerFixedCard
public import Theory.GroupTheory.C5C4NormalTwoSubgroup

/-!
# The two-core of the actual fixed-four centralizer

Let Q be the second local core, R the first residual, and V = C_Q(A)
the noncyclic fixed group of order four. We identify O₂(C_G(V)) with
W = C_Q(R′), the derived centralizer of order 64.

Parrott's residual structure makes R′ elementary abelian of order 32.
An involution fixed by A has at least square-root many fixed points on R′.
The central fixed line and orbit counting modulo five force it to fix all
of R′. Also W is abelian: its central subgroup R′ has index two. Thus W
centralizes V, and the existing upper bound 64 gives C_Q(V) = W.

The distinguished line in V confines C_G(V) to the second local group.
In its faithful C5 semidirect C4 quotient, no nontrivial two-subgroup is
normalized by a five-subgroup. The image of O₂(C_G(V)) is therefore trivial.
Finally W is normal in the second local group, which gives the reverse
core containment. No ambient Sylow-five or odd-local hypothesis is used.

Source: Thompson VI, printed p.630, the noncyclic four-fixed alternative;
Parrott's order-512 residual calculation is supplied by
`Theory.GroupAction.Order512FiveStructure`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

private theorem derived_structure
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    IsElementaryAbelian 2 (DerivedAmbient ctx.firstResidual) ∧
      CenterAmbient ctx.firstResidual ≤ DerivedAmbient ctx.firstResidual := by
  let R := ctx.firstResidual
  obtain ⟨A, hA, _, hAN, hfixed⟩ := ctx.exists_five_subgroup_fixed_center
  let _ : MulDistribMulAction A R := conjMulDistribMulActionOfLeNormalizer A R hAN
  have hfixed' : FixedPoints.subgroup A R ≤ center R := by
    intro r hr
    apply hfixed
    change (r : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have heq := congrArg R.subtype (hr ⟨a, ha⟩)
    change a * (r : G) * a⁻¹ = (r : G) at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  have htwo : IsPGroup 2 R := IsPGroup.of_card (n := 9)
    (by simpa using ctx.first_residual_structure.1)
  obtain ⟨_, _, _, hupper, helem, _⟩ := Theory.GroupAction.parrott_twoGroup_structure
    htwo ctx.first_residual_structure.1 ctx.first_residual_structure.2.2.2.2.2.ge hA hfixed'
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := helem
  change IsElementaryAbelian 2 ((commutator R).map R.subtype) ∧
    (center R).map R.subtype ≤ (commutator R).map R.subtype
  refine ⟨IsElementaryAbelian.map R.subtype, map_mono ?_⟩
  rw [hupper, ← Subgroup.upperCentralSeries_one R]
  exact Subgroup.upperCentralSeries_mono R (by decide)

/-- Every five-fixed involution in the second core centralizes the derived residual. -/
public theorem LargeTerminalContext.five_fixed_involution_centralizes_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hy : orderOf y = 2) :
    y ∈ centralizer (DerivedAmbient ctx.firstResidual : Set G) := by
  let R := ctx.firstResidual
  let D := DerivedAmbient R
  let E := D ⊓ centralizer ({y} : Set G)
  obtain ⟨hDel, hZD⟩ := derived_structure ctx
  let _ : IsElementaryAbelian 2 D := hDel
  have hDcard : Nat.card D = 32 := by
    change Nat.card ((commutator R).map R.subtype) = 32
    rw [card_map_of_injective R.subtype_injective]
    exact ctx.first_residual_structure.2.2.2.2.1
  have hDR : D ≤ R := map_subtype_le _
  have hND : normalizer (R : Set G) ≤ normalizer (D : Set G) :=
    normalizer_le_normalizer_characteristic_image R (commutator R)
  have hyN : y ∈ normalizer (D : Set G) :=
    hND (ctx.second_le_residual_normalizer (twoCoreIn_le ctx.second hyQ))
  let a : MulAut D := D.normalizerMonoidHom ⟨y, hyN⟩
  have ha : a ^ 2 = 1 := by
    have hh : (⟨y, hyN⟩ : normalizer (D : Set G)) ^ 2 = 1 := by
      apply Subtype.ext
      exact hy ▸ pow_orderOf_eq_one y
    exact (map_pow D.normalizerMonoidHom _ 2).symm.trans (by rw [hh, map_one])
  have hEcard : Nat.card (FixedPoints.subgroup (zpowers a) D) = Nat.card E := by
    have heq : FixedPoints.subgroup (zpowers a) D =
        (centralizer ({y} : Set G)).subgroupOf D := by
      ext d
      rw [MulAut.mem_fixed_zpowers_iff]
      rw [mem_subgroupOf, mem_centralizer_singleton_iff]
      rw [Subtype.ext_iff]
      change y * (d : G) * y⁻¹ = (d : G) ↔ (d : G) * y = y * (d : G)
      exact mul_inv_eq_iff_eq_mul.trans eq_comm
    rw [heq, ← card_map_of_injective (f := D.subtype)
      (K := (centralizer ({y} : Set G)).subgroupOf D) D.subtype_injective, subgroupOf_map_subtype, inf_comm]
  have hbound := MulAut.card_le_fixed_card_sq_of_square_eq_one a ha
  rw [hEcard, hDcard] at hbound
  have hAC : A ≤ centralizer ({y} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hyA b hb)
  have hAE : A ≤ normalizer (E : Set G) :=
    (le_inf (hAN.trans hND) (hAC.trans (centralizer ({y} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let _ : MulDistribMulAction A E := conjMulDistribMulActionOfLeNormalizer A E hAE
  let F := FixedPoints.subgroup A E
  have hFZ : F.map E.subtype ≤ CenterAmbient R := by
    rintro x ⟨d, hd, rfl⟩
    refine mem_map.mpr ⟨⟨(d : G), hDR d.property.1⟩, hfixed ?_, rfl⟩
    change (d : G) ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro b hb
    have hh := congrArg (fun t : E => (t : G)) (hd ⟨b, hb⟩)
    change b * (d : G) * b⁻¹ = (d : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hFbound : Nat.card F ≤ 2 := by
    have hh := card_le_of_le hFZ
    rw [card_map_of_injective E.subtype_injective] at hh
    have hZ : Nat.card (CenterAmbient R) = 2 := by
      change Nat.card ((center R).map R.subtype) = 2
      rw [card_map_of_injective R.subtype_injective]
      exact ctx.first_residual_structure.2.2.2.1
    rwa [hZ] at hh
  obtain ⟨z, hz, hgen, _, _, _⟩ := ctx.involution_centralizer_core
  have hzZ : z ∈ CenterAmbient R := by
    rw [ctx.first_residual_center_eq_omegaOneCenter, ← hgen]
    exact mem_zpowers z
  have hzA : z ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro b hb
    exact mem_centralizer_singleton_iff.mp
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen (hAN hb))
  have hQS : twoCoreIn ctx.second ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hzC : z ∈ centralizer ({y} : Set G) := by
    have hzS : z ∈ CenterAmbient (S : Subgroup G) :=
      omegaOneCenter_le_centerAmbient _ (hgen ▸ mem_zpowers z)
    exact mem_centralizer_singleton_iff.mpr
      ((centerAmbient_le_centralizer _ hzS) y (hQS hyQ)).symm
  let zE : E := ⟨z, hZD hzZ, hzC⟩
  have hzF : zE ∈ F := by
    intro b
    apply Subtype.ext
    change (b : G) * z * (b : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hzA b b.property)
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hz1 : z = 1 := congrArg (fun d : E => (d : G)) (mem_bot.mp (hbot ▸ hzF))
    simp [hz1] at hz
  have hFcard : Nat.card F = 2 := by
    have hh := (one_lt_card_iff_ne_bot F).mpr hFne
    omega
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfive : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hfive.card_modEq_card_fixedPoints E
  change Nat.card E % 5 = Nat.card F % 5 at hmod
  rw [hFcard] at hmod
  have hdiv : Nat.card E ∣ 2 ^ 5 := by
    simpa only [hDcard, Nat.reducePow] using card_dvd_of_le (show E ≤ D from inf_le_left)
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hneTwo : Nat.card E ≠ 2 := by
    intro hh
    rw [hh] at hbound
    norm_num at hbound
  have hcardE : Nat.card E = 32 := by
    interval_cases n <;> norm_num only [Nat.reducePow] at hcard <;> omega
  have heq : E = D := eq_of_le_of_card_ge inf_le_left (by rw [hcardE, hDcard])
  rw [mem_centralizer_iff]
  intro d hd
  exact mem_centralizer_singleton_iff.mp (heq.ge hd).2

private theorem derived_centralizer_commutative
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    IsMulCommutative (twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G) : Subgroup G) := by
  let D := DerivedAmbient ctx.firstResidual
  let W := twoCoreIn ctx.second ⊓ centralizer (D : Set G)
  have hDW : D ≤ W := by
    change DerivedAmbient ctx.firstResidual ≤ _
    rw [← ctx.derived_centralizer_supplement.2]
    exact inf_le_left
  let T := D.subgroupOf W
  have hTcenter : T ≤ center W := by
    intro d hd
    rw [mem_center_iff]
    intro w
    apply Subtype.ext
    exact (mem_centralizer_iff.mp w.property.2 d hd).symm
  let _ : T.Normal := ⟨fun d hd w => by
    simpa only [mem_center_iff.mp (hTcenter hd) w, mul_inv_cancel_right] using hd⟩
  have hTcard : Nat.card T = 32 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDW).toEquiv]
    change Nat.card ((commutator ctx.firstResidual).map ctx.firstResidual.subtype) = 32
    rw [card_map_of_injective ctx.firstResidual.subtype_injective]
    exact ctx.first_residual_structure.2.2.2.2.1
  have hWcard : Nat.card W = 64 := (ctx.derived_centralizer_card_and_index hS).1
  have hquot : Nat.card (W ⧸ T) = 2 := by
    have hh := T.card_mul_index
    rw [hTcard, hWcard, index_eq_card] at hh
    omega
  let _ : IsCyclic (W ⧸ T) := isCyclic_of_prime_card hquot
  exact (QuotientGroup.mk' T).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rwa [QuotientGroup.ker_mk'])

/-- Inside the second core the fixed-four centralizer is exactly the derived centralizer. -/
public theorem LargeTerminalContext.five_fixed_four_core_centralizer_eq
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    twoCoreIn ctx.second ⊓ centralizer
      (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) =
        twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G) := by
  let Q := twoCoreIn ctx.second
  let V := Q ⊓ centralizer (A : Set G)
  let W := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  have hVfour : IsKleinFour V := (ctx.five_fixed_four_ambient_data A hAN hcard hncyc hfixed).1
  have hVW : V ≤ W := by
    intro v hv
    refine ⟨hv.1, ?_⟩
    by_cases h1 : v = 1
    · exact h1 ▸ (centralizer (DerivedAmbient ctx.firstResidual : Set G)).one_mem
    have hpow : v ^ 2 = 1 := by
      have hh := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
      rw [hVfour.2] at hh
      exact congrArg V.subtype hh
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ctx.five_fixed_involution_centralizes_derived A hA hAN hfixed v hv.1 hv.2
      (orderOf_eq_prime hpow h1)
  let _ : IsMulCommutative W := derived_centralizer_commutative ctx hS
  have hWC : W ≤ Q ⊓ centralizer (V : Set G) := by
    refine le_inf inf_le_left ?_
    intro w hw
    rw [mem_centralizer_iff]
    intro v hv
    exact congrArg W.subtype (IsMulCommutative.is_comm.comm (⟨v, hVW hv⟩ : W) ⟨w, hw⟩)
  obtain ⟨y, hyQ, hyA, hyR, _⟩ :=
    ctx.exists_five_fixed_involution_of_not_cyclic A hcard hfixed hncyc
  have hbound : Nat.card (Q ⊓ centralizer (V : Set G) : Subgroup G) ≤ 64 :=
    (card_le_of_le (inf_le_inf_left Q
      (centralizer_le (Set.singleton_subset_iff.mpr (show y ∈ V from ⟨hyQ, hyA⟩))))).trans
        (ctx.fixed_core_centralizer_card_le_sixtyfour hS A hA hAN hfixed y hyQ hyA hyR)
  exact (eq_of_le_of_card_ge hWC
    (by rwa [(ctx.derived_centralizer_card_and_index hS).1])).symm


/-- A subgroup of the second local group containing a five-subgroup has its
 two-core inside the second local core. -/
public theorem LargeTerminalContext.five_overgroup_core_le_second_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A H : Subgroup G) (hA : Nat.card A = 5)
    (hAH : A ≤ H) (hHP : H ≤ ctx.second) :
    twoCoreIn H ≤ twoCoreIn ctx.second := by
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
  let e : P ≃* ctx.second := (P.equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  obtain ⟨φ, hφ, projection, _, hker⟩ :=
    ten_one_large_first_frobenius tenCtx middle hpath ctx.noTransvections
  let π := projection.comp e.symm.toMonoidHom
  have hkerP : projection.ker = pCore 2 P := by
    rw [hker]
    change (ctx.terminal.Γ.twoCoreAt cp.firstStep).subgroupOf P = pCore 2 P
    rw [ctx.terminal.Γ.twoCoreAt_def]
    exact subgroupOf_map_subtype_eq _
  have hπ : π.ker = pCore 2 ctx.second := by
    ext x
    change e.symm x ∈ projection.ker ↔ x ∈ pCore 2 ctx.second
    rw [hkerP, ← pCore_map_iso 2 e, mem_map_equiv]
    rfl
  let B := A.subgroupOf ctx.second
  have hAP : A ≤ ctx.second := hAH.trans hHP
  have hBcard : Nat.card B = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv).trans hA
  have hBfive : IsPGroup 5 B := IsPGroup.of_card (n := 1) (by simpa using hBcard)
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hdis : Disjoint π.ker B := by
    rw [hπ]
    exact IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup hBfive
  have hBimage : Nat.card (B.map π) = 5 := by
    have hh := relIndex_ker B π
    change (π.ker.subgroupOf B).index = Nat.card (B.map π) at hh
    rw [subgroupOf_eq_bot.mpr hdis, index_bot, hBcard] at hh
    exact hh.symm
  let U := twoCoreIn H
  have hUH : U ≤ H := twoCoreIn_le H
  have hUP : U ≤ ctx.second := hUH.trans hHP
  let T := U.subgroupOf ctx.second
  have hTtwo : IsPGroup 2 T :=
    ((pCore_isPGroup (p := 2) (G := H)).map H.subtype).of_equiv (subgroupOfEquivOfLe hUP).symm
  have hAU : A ≤ normalizer (U : Set G) :=
    hAH.trans ((normal_subgroupOf_iff_le_normalizer hUH).mp (twoCoreIn_normal H))
  have hBT : B ≤ normalizer (T : Set ctx.second) := by
    rw [← subgroupOf_normalizer_eq hUP]
    exact fun b hb => hAU hb
  have himage : T.map π = ⊥ :=
    SemidirectProduct.two_subgroup_eq_bot_of_five_normalizes φ hφ (B.map π) (T.map π)
      hBimage (hTtwo.map π) ((map_mono hBT).trans (le_normalizer_map π))
  intro x hx
  let xP : ctx.second := ⟨x, hUP hx⟩
  have hmem : π xP ∈ T.map π := mem_map_of_mem π hx
  have hxker : xP ∈ π.ker := mem_bot.mp (himage ▸ hmem)
  rw [hπ] at hxker
  exact mem_map_of_mem ctx.second.subtype hxker

/-- The two-core of the full fixed-four centralizer is the order-64
 derived centralizer in the second local core. -/
public theorem LargeTerminalContext.five_fixed_four_centralizer_core_eq
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (_hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    twoCoreIn (centralizer
      (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G)) =
        twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G) := by
  let Q := twoCoreIn ctx.second
  let V := Q ⊓ centralizer (A : Set G)
  let C := centralizer (V : Set G)
  let W := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  have hCW : Q ⊓ C = W :=
    ctx.five_fixed_four_core_centralizer_eq hS A hA hAN hcard hncyc hfixed
  obtain ⟨_, hZV, _⟩ := ctx.five_fixed_four_ambient_data A hAN hcard hncyc hfixed
  obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
  have hzV : z ∈ V := hZV (hgen ▸ mem_zpowers z)
  have hCP : C ≤ ctx.second :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzV)).trans_eq
      (ctx.involution_centralizer_eq_second hS z hz hgen)
  have hAC : A ≤ C := le_centralizer_iff.mpr (show V ≤ centralizer (A : Set G) from inf_le_right)
  have hCQ : twoCoreIn C ≤ Q := ctx.five_overgroup_core_le_second_core A C hA hAC hCP
  change twoCoreIn C = W
  apply le_antisymm
  · rw [← hCW]
    exact le_inf hCQ (twoCoreIn_le C)
  · have hWC : W ≤ C := hCW ▸ inf_le_right
    have hWtwo : IsPGroup 2 W := ((pCore_isPGroup (p := 2) (G := ctx.second)).map ctx.second.subtype).to_le inf_le_left
    have hNW : C ≤ normalizer (W : Set G) :=
      hCP.trans (ctx.derived_centralizer_normalizer_local_data hS).2.1
    have hWnormal : (W.subgroupOf C).Normal :=
      (normal_subgroupOf_iff_le_normalizer hWC).mpr hNW
    have hle : W.subgroupOf C ≤ pCore 2 C :=
      le_sSup ⟨hWnormal, hWtwo.of_equiv (subgroupOfEquivOfLe hWC).symm⟩
    rw [← map_subgroupOf_eq_of_le hWC]
    exact map_mono hle

end Stellmacher.Recognition
