module

public import Stellmacher.Recognition.LargeTerminalFixedLayerKernel
public import Stellmacher.Recognition.LargeTerminalFourFixedCoreFrattini
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.CommutatorOrbitCard
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Stellmacher.SectionTen.TenOneLargeFirstCoreContainment
public import Theory.GroupTheory.IndexTwoConjugateSelection

/-!
# Five-fixed elements and conjugate derived layers

Write Q for the second core, R for the first residual, D for its derived
subgroup and Z for its center. The relation [D,Q] = Z and coprime splitting
show that every five-fixed element of Q centralizes D. Indeed the
three-subgroups lemma makes it centralize [D,A], and the remaining fixed
factor is contained in Z.

A middle-stabilizer element swaps the two endpoints and constructs one
conjugate D* with |D ∩ D*| = 8 and |R ∩ D*| = 16. The residual fixed-point
bound gives C_R(y) = D. Orbit counting and the five-action then give
[R,⟨y⟩] = D. The same endpoint construction supplies C_Q(D) ≤ DQ* and
[DQ*:Q*] = 2, with D not contained in Q*. If every R-conjugate of y
missed Q*, their quotients with y would force [R,⟨y⟩] ≤ Q*, a contradiction.
Conjugating the entire endpoint configuration back by the selected residual
element preserves both intersections and places y in its conjugate core.
Transport of [D,Q] = Z now gives [R ∩ D*,⟨y⟩] ≤ Z* for this one witness.
An element of R ∩ D* outside D supplies a nontrivial central displacement.

A point of D* moved nontrivially into Z* enlarges the common fixed eight
to a layer of order at least sixteen fixed modulo Z*.

Source: Thompson VI, printed p.630, the paragraph beginning “Now Y ∈ C(Z*)”,
and Stellmacher (10.1)(18)--(20) for the local commutator structure.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
open scoped commutatorElement

universe u

/-- The first derived residual has central commutators with the whole second core. -/
public theorem LargeTerminalContext.derived_commutator_second_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ⁅DerivedAmbient ctx.firstResidual, twoCoreIn ctx.second⁆ =
      CenterAmbient ctx.firstResidual := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let P := GAt Γ cp.firstStep
  have hP : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  have hQ : (QAt Γ cp.firstStep).map K.subtype = twoCoreIn ctx.second := by
    let e := P.equivMapOfInjective K.subtype K.subtype_injective
    have h := pCore_map_iso 2 e
    have hh : (twoCoreIn P).map K.subtype = twoCoreIn (P.map K.subtype) := by
      change ((pCore 2 P).map P.subtype).map K.subtype =
        (pCore 2 (P.map K.subtype)).map (P.map K.subtype).subtype
      rw [← h, map_map, map_map]
      rfl
    change (Γ.twoCoreAt _).map K.subtype = _
    rw [Γ.twoCoreAt_def]
    change (twoCoreIn P).map K.subtype = _
    rw [hh, hP]
  have hlength : cp.length = 3 := ctx.length_three
  have hshort : 1 < cp.length := by omega
  have h := (nine_next_center_commutator_and_kernel
    (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext
    hshort cp.firstStep ⟨1, Γ.act_one _⟩).2.1
  rw [ctx.first_residual_structure.2.2.1, ctx.first_residual_structure.2.1, ← hQ,
    ← map_commutator]
  exact congrArg (fun H : Subgroup K => H.map K.subtype) h

/-- A five-fixed element of the second core centralizes the derived residual.
Only the actual residual fixed-center hypothesis is needed. -/
public theorem LargeTerminalContext.five_fixed_centralizes_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second) (hyA : y ∈ centralizer (A : Set G)) :
    y ∈ centralizer (DerivedAmbient ctx.firstResidual : Set G) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := ctx.firstResidual
  let D := DerivedAmbient R
  let Z := CenterAmbient R
  let Y := zpowers y
  have hDR : D ≤ R := map_subtype_le _
  have hZC : Z ≤ centralizer (A : Set G) := by
    have hZcard : Nat.card Z = 2 :=
      (card_map_of_injective R.subtype_injective).trans ctx.first_residual_structure.2.2.2.1
    have hNZ : A ≤ normalizer (Z : Set G) := by
      have hNC : normalizer (R : Set G) ≤ normalizer (centralizer (R : Set G) : Set G) :=
        (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (R : Set G))).mp
          inferInstance
      change A ≤ normalizer (CenterAmbient R : Set G)
      rw [SectionEight.eight_six_centerAmbient_eq_inf_centralizer]
      exact (le_inf hAN (hAN.trans hNC)).trans inf_normalizer_le_normalizer_inf
    have hAut : Nat.card (MulAut Z) = 1 := by
      let _ : IsCyclic Z := isCyclic_of_prime_card hZcard
      rw [IsCyclic.card_mulAut, hZcard]
      decide
    let _ : Subsingleton (MulAut Z) := (Nat.card_eq_one_iff_unique.mp hAut).1
    apply le_centralizer_iff.mpr
    intro a ha
    apply mem_centralizer_iff.mpr
    intro z hz
    have he := Subsingleton.elim (Z.normalizerMonoidHom ⟨a, hNZ ha⟩) 1
    have hh := congrArg (fun f : MulAut Z => (f ⟨z, hz⟩ : G)) he
    change a * z * a⁻¹ = z at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hYQ : Y ≤ twoCoreIn ctx.second := zpowers_le.mpr hyQ
  have hYCA : Y ≤ centralizer (A : Set G) := zpowers_le.mpr hyA
  have hDY : ⁅D, Y⁆ ≤ Z :=
    (commutator_mono le_rfl hYQ).trans_eq ctx.derived_commutator_second_core
  have hZA : ⁅Z, A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hZC
  have hYA : ⁅Y, A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hYCA
  have hrot : ⁅⁅Y, D⁆, A⁆ = ⊥ := by
    rw [commutator_comm Y D]
    exact bot_unique ((commutator_mono hDY le_rfl).trans hZA.le)
  have hDAY : ⁅⁅D, A⁆, Y⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by rw [commutator_comm A Y, hYA]; simp) hrot
  have hAD : A ≤ normalizer (D : Set G) := by
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [show D = ⁅R, R⁆ from map_subtype_commutator _, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hAN ha)]
  have hDcard : Nat.card D = 32 :=
    (card_map_of_injective R.subtype_injective).trans ctx.first_residual_structure.2.2.2.2.1
  have hDtwo : IsPGroup 2 D := IsPGroup.of_card (n := 5) hDcard
  let _ : Group.IsNilpotent D := hDtwo.isNilpotent
  have hsplit : D = ⁅D, A⁆ ⊔ (D ⊓ centralizer (A : Set G)) :=
    eq_commutator_sup_centralizer_of_solvable_coprime D A hAD inferInstance
      (by rw [hA, hDcard]; decide)
  have hfixedZ : D ⊓ centralizer (A : Set G) ≤ Z := by
    rintro d ⟨hdD, hdA⟩
    exact mem_map_of_mem R.subtype (hfixed (show (⟨d, hDR hdD⟩ : R) ∈
      (centralizer (A : Set G)).subgroupOf R from hdA))
  have hYZ : Y ≤ centralizer (Z : Set G) := by
    have hYS : Y ≤ (S : Subgroup G) := by
      have hSP : (S : Subgroup G) ≤ ctx.second :=
        ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
      rintro t ht
      obtain ⟨q, hq, rfl⟩ := hYQ ht
      exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
        (S.subtype hSP) hq
    rw [show Z = omegaOneCenter (S : Subgroup G) from
      ctx.first_residual_center_eq_omegaOneCenter]
    exact hYS.trans (le_centralizer_iff.mpr
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)))
  have hDCY : D ≤ centralizer (Y : Set G) := by
    rw [hsplit]
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hDAY)
      (hfixedZ.trans (le_centralizer_iff.mp hYZ))
  exact (le_centralizer_iff.mp hDCY) (mem_zpowers y)

/-- The residual fixed by a five-fixed element outside it is exactly its
 derived subgroup. The lower containment is coprime splitting; the upper
 containment follows from the checked fixed-point count. -/
public theorem LargeTerminalContext.five_fixed_residual_centralizer_eq_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ctx.firstResidual ⊓ centralizer ({y} : Set G) =
      DerivedAmbient ctx.firstResidual := by
  have hyD := ctx.five_fixed_centralizes_derived A hA hAN hfixed y hyQ hyA
  have hle : DerivedAmbient ctx.firstResidual ≤
      ctx.firstResidual ⊓ centralizer ({y} : Set G) := by
    refine le_inf (map_subtype_le _) ?_
    intro d hd
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hyD d hd)
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hcard : Nat.card (DerivedAmbient ctx.firstResidual) = 32 :=
    (card_map_of_injective ctx.firstResidual.subtype_injective).trans
      ctx.first_residual_structure.2.2.2.2.1
  rw [hcard]
  exact ctx.fixed_residual_centralizer_card_le_thirtytwo A hA hAN hfixed y hyQ hyA hyR

/-- The residual commutators with a five-fixed element outside it generate
its whole derived group: orbit counting gives at least sixteen points,
and the five-action with its central fixed line forces order thirty-two. -/
public theorem LargeTerminalContext.five_fixed_residual_commutator_eq_derived
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ⁅ctx.firstResidual, zpowers y⁆ = DerivedAmbient ctx.firstResidual := by
  let R := ctx.firstResidual
  let D := DerivedAmbient R
  let H := ⁅R, zpowers y⁆
  let Q := twoCoreIn ctx.second
  have hRQ : R ≤ Q := (ctx.derived_centralizer_supplement.1 ▸ le_sup_right :
    ctx.firstResidual ≤ twoCoreIn ctx.second)
  have hHD : H ≤ D := by
    have hh := commutator_mono hRQ (zpowers_le.mpr hyQ)
    rw [← map_subtype_commutator Q] at hh
    change H ≤ DerivedAmbient (twoCoreIn ctx.second) at hh
    rw [ctx.second_core_derived_eq] at hh
    exact hh
  have hHR : H ≤ R := hHD.trans (map_subtype_le _)
  have hDcard : Nat.card D = 32 :=
    (card_map_of_injective R.subtype_injective).trans ctx.first_residual_structure.2.2.2.2.1
  have hCcard : Nat.card ((centralizer ({y} : Set G)).subgroupOf R) = 32 := by
    have heq : (centralizer ({y} : Set G)).subgroupOf R = D.subgroupOf R := by
      ext r
      have hh := ctx.five_fixed_residual_centralizer_eq_derived A hA hAN hfixed y hyQ hyA hyR
      change R ⊓ centralizer ({y} : Set G) = D at hh
      change (r : G) ∈ centralizer ({y} : Set G) ↔ (r : G) ∈ D
      rw [← hh]
      simp only [mem_inf, r.property, true_and]
    rw [heq, Nat.card_congr (subgroupOfEquivOfLe (show D ≤ R from map_subtype_le _)).toEquiv]
    exact hDcard
  have hHlow : 16 ≤ Nat.card H := by
    have hh := card_le_commutator_card_mul_centralizer R y
    rw [ctx.first_residual_structure.1, hCcard] at hh
    change 16 ≤ Nat.card (⁅R, zpowers y⁆ : Subgroup G)
    omega
  have hAH : A ≤ normalizer (H : Set G) := by
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hya : MulAut.conj a y = y :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hyA a ha)
    change H.map (MulAut.conj a).toMonoidHom = H
    dsimp only [H]
    rw [map_commutator, show R.map (MulAut.conj a).toMonoidHom = R from
      mem_normalizer_iff_map_conj_eq.mp (hAN ha),
      MonoidHom.map_zpowers]
    change ⁅R, zpowers (MulAut.conj a y)⁆ = ⁅R, zpowers y⁆
    rw [hya]
  let _ : MulDistribMulAction A H := conjMulDistribMulActionOfLeNormalizer A H hAH
  let F := FixedPoints.subgroup A H
  have hFZ : F.map H.subtype ≤ CenterAmbient R := by
    rintro x ⟨d, hd, rfl⟩
    refine mem_map.mpr ⟨⟨(d : G), hHR d.property⟩, hfixed ?_, rfl⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    have hh := congrArg (fun t : H => (t : G)) (hd ⟨a, ha⟩)
    change a * (d : G) * a⁻¹ = (d : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hFbound : Nat.card F ≤ 2 := by
    have hh := card_le_of_le hFZ
    rw [card_map_of_injective H.subtype_injective] at hh
    have hZ : Nat.card (CenterAmbient R) = 2 :=
      (card_map_of_injective R.subtype_injective).trans ctx.first_residual_structure.2.2.2.1
    rwa [hZ] at hh
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 R) := ⟨IsPGroup.of_card (n := 9) ctx.first_residual_structure.1⟩
  let _ : (H.subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hHR).mpr (normalizer_commutator_ge_left R (zpowers y))
  have hHnative : Nat.card (H.subgroupOf R) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hHR).toEquiv
  let _ : Nontrivial (H.subgroupOf R) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hHnative]; omega)
  obtain ⟨w, hwne, hwZ⟩ := exists_nontrivial_center_mem_normal (H.subgroupOf R) (p := 2)
  let wH : H := ⟨((w : R) : G), w.property⟩
  obtain ⟨z, hz, hgen, _, _, _⟩ := ctx.involution_centralizer_core
  have hAZ : A ≤ centralizer (CenterAmbient R : Set G) := by
    rw [show CenterAmbient R = zpowers z from
      ctx.first_residual_center_eq_omegaOneCenter.trans hgen.symm,
      zpowers_eq_closure, centralizer_closure]
    exact hAN.trans (ctx.residual_normalizer_le_involution_centralizer z hz hgen)
  have hwF : wH ∈ F := by
    intro a
    apply Subtype.ext
    change (a : G) * (wH : G) * (a : G)⁻¹ = (wH : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp (hAZ a.property) _ (mem_map_of_mem R.subtype hwZ)).symm
  have hFne : F ≠ ⊥ := by
    intro hb
    have hh : wH = 1 := hb.le hwF
    apply hwne
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun h : H => (h : G)) hh
  have hFcard : Nat.card F = 2 := by
    have hh := (one_lt_card_iff_ne_bot F).mpr hFne
    omega
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod := (IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)).card_modEq_card_fixedPoints H
  change Nat.card H % 5 = Nat.card F % 5 at hmod
  rw [hFcard] at hmod
  have hdiv : Nat.card H ∣ 2 ^ 5 := by
    have hh := card_dvd_of_le hHD
    rwa [hDcard] at hh
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hHcard : Nat.card H = 32 := by
    interval_cases n <;> norm_num only [Nat.reducePow] at hcard <;> omega
  exact eq_of_le_of_card_ge hHD (by rw [hDcard, hHcard])

private theorem residual_conjugate_mem_seed_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hy : orderOf y = 2) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (N : Subgroup G)
    (hCN : twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G) ≤
      DerivedAmbient ctx.firstResidual ⊔ N)
    (hindex : N.relIndex (DerivedAmbient ctx.firstResidual ⊔ N) = 2)
    (hout : ¬ DerivedAmbient ctx.firstResidual ≤ N) :
    ∃ r ∈ ctx.firstResidual, MulAut.conj r y ∈ N := by
  let R := ctx.firstResidual
  let D := DerivedAmbient R
  let Q := twoCoreIn ctx.second
  let C := Q ⊓ centralizer (D : Set G)
  have hRQ : R ≤ Q := (ctx.derived_centralizer_supplement.1 ▸ le_sup_right :
    ctx.firstResidual ≤ twoCoreIn ctx.second)
  have hQN : Q ≤ normalizer (D : Set G) := by
    intro q hq
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [show D = ⁅R, R⁆ from map_subtype_commutator _, map_commutator]
    have hr : R.map (MulAut.conj q).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp
        (ctx.second_le_residual_normalizer (twoCoreIn_le ctx.second hq))
    change ⁅R.map (MulAut.conj q).toMonoidHom, R.map (MulAut.conj q).toMonoidHom⁆ = ⁅R, R⁆
    rw [hr]
  have hCC : Q ≤ normalizer (C : Set G) :=
    (le_inf Q.le_normalizer (hQN.trans (normalizer_le_normalizer_centralizer D))).trans
      inf_normalizer_le_normalizer_inf
  have hyC : y ∈ C := ⟨hyQ, ctx.five_fixed_centralizes_derived A hA hAN hfixed y hyQ hyA⟩
  apply exists_conj_mem_of_index_two_commutator_not_le R (D ⊔ N) N hindex y hy
  · intro r hr
    exact hCN ((mem_normalizer_iff.mp (hCC (hRQ hr)) y).mp hyC)
  · rw [ctx.five_fixed_residual_commutator_eq_derived A hA hAN hfixed y hyQ hyA hyR]
    exact hout

private theorem derived_conjugate_seed_geometry
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ g : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 ∧
      Nat.card (ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 16 ∧
      (twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G) ≤
        DerivedAmbient ctx.firstResidual ⊔
          (twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom) ∧
      ((twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom).relIndex
        (DerivedAmbient ctx.firstResidual ⊔
          (twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom) = 2 ∧
      ¬ DerivedAmbient ctx.firstResidual ≤
        (twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  obtain ⟨_, hfirst, hterminal, hends⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  obtain ⟨mover, _, hmove, hreturn⟩ := ten_one_neighbor_pair_alignment
    tenCtx middle hpath hterminal hfirst hends.symm
  change Γ.act mover cp.firstStep = cp.a' at hmove
  change Γ.act mover cp.a' = cp.firstStep at hreturn
  let e := MulAut.conj (mover : K)⁻¹
  let g : G := ((mover : K) : G)⁻¹
  have hf : (MulAut.conj g).toMonoidHom.comp K.subtype =
      K.subtype.comp e.toMonoidHom := by ext x; rfl
  have hVmap : (VAt Γ cp.firstStep).map e.toMonoidHom = VAt Γ cp.a' := by
    change (v Γ cp.firstStep).map _ = v Γ cp.a'
    rw [← v_act, hmove]
  have hZmap : (ZAt Γ cp.firstStep).map e.toMonoidHom = ZAt Γ cp.a' := by
    change (Γ.z cp.firstStep).map _ = Γ.z cp.a'
    rw [← z_act, hmove]
  have hDg : (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom =
      (VAt Γ cp.a').map K.subtype := by
    rw [ctx.first_residual_structure.2.2.1, map_map, hf, ← map_map, hVmap]
  have hZg : (CenterAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom =
      (ZAt Γ cp.a').map K.subtype := by
    rw [ctx.first_residual_structure.2.1, map_map, hf, ← map_map, hZmap]
  have hz : z ∈ CenterAmbient ctx.firstResidual := by
    rw [ctx.first_residual_center_eq_omegaOneCenter, ← hgen]
    exact mem_zpowers z
  have hZZ : ZAt Γ cp.a' ≤ ZAt Γ middle := by
    have hsplit : ZAt Γ middle = ZAt Γ cp.firstStep ⊔ ZAt Γ cp.a' :=
      (sectionTenOpeningData tenCtx middle hpath).center_direct_product.1
    rw [hsplit]
    exact le_sup_right
  have hZD : (ZAt Γ cp.a').map K.subtype ≤ DerivedAmbient ctx.firstResidual := by
    rw [ctx.first_residual_structure.2.2.1]
    exact map_mono (hZZ.trans
      (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hfirst)))
  have hPreturn : (GAt Γ cp.a').map e.toMonoidHom = GAt Γ cp.firstStep := by
    change conjugateBy (stabilizer Γ cp.a') mover⁻¹ = stabilizer Γ cp.firstStep
    rw [← stabilizer_act, hreturn]
  have hRreturn : (twoCoreIn (EAt Γ cp.a')).map e.toMonoidHom =
      twoCoreIn (EAt Γ cp.firstStep) := by
    rw [← twoCoreIn_map_equiv]
    change twoCoreIn ((Γ.twoResidualAt cp.a').map e.toMonoidHom) =
      twoCoreIn (Γ.twoResidualAt cp.firstStep)
    rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def, ← twoResidualIn_map_equiv]
    exact congrArg (fun P => twoCoreIn (twoResidualIn P)) hPreturn
  have hseed : Nat.card (VAt Γ cp.firstStep ⊓ twoCoreIn (EAt Γ cp.a') : Subgroup K) = 16 := by
    have hh := (ten_one_large_first_residual_index tenCtx middle hpath ctx.noTransvections).1
    change Nat.card (VAt Γ cp.firstStep) = 2 *
      Nat.card (VAt Γ cp.firstStep ⊓ twoCoreIn (EAt Γ cp.a') : Subgroup K) at hh
    have hfirstcard : Nat.card (VAt Γ cp.firstStep) = 32 := by
      rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hVmap]
      exact (ten_one_large_terminal_structure tenCtx middle hpath ctx.noTransvections).2.1
    rw [hfirstcard] at hh
    omega
  have hseedReturn : Nat.card (twoCoreIn (EAt Γ cp.firstStep) ⊓ VAt Γ cp.a' : Subgroup K) = 16 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, map_inf _ _ _ e.injective,
      hVmap, hRreturn] at hseed
    rwa [inf_comm] at hseed
  refine ⟨g, hZD (hZg ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hz), ?_, ?_, ?_⟩
  · rw [hDg, ctx.first_residual_structure.2.2.1,
      ← map_inf _ _ K.subtype K.subtype_injective, card_map_of_injective K.subtype_injective]
    exact (ten_one_large_terminal_structure tenCtx middle hpath ctx.noTransvections).2.2
  · rw [hDg]
    change Nat.card ((twoCoreIn (EAt Γ cp.firstStep)).map K.subtype ⊓
      (VAt Γ cp.a').map K.subtype : Subgroup G) = 16
    rw [← map_inf _ _ K.subtype K.subtype_injective, card_map_of_injective K.subtype_injective]
    exact hseedReturn

  · have hQfirst : (QAt Γ cp.firstStep).map K.subtype = twoCoreIn ctx.second := by
      let P := GAt Γ cp.firstStep
      have hP : P.map K.subtype = ctx.second :=
        (nine_two_ambient_setup tenCtx.toAmbientSectionNineContext).2.2.1
      let j := P.equivMapOfInjective K.subtype K.subtype_injective
      have hj := pCore_map_iso 2 j
      have hh : (twoCoreIn P).map K.subtype = twoCoreIn (P.map K.subtype) := by
        change ((pCore 2 P).map P.subtype).map K.subtype =
          (pCore 2 (P.map K.subtype)).map (P.map K.subtype).subtype
        rw [← hj, map_map, map_map]
        rfl
      change (Γ.twoCoreAt _).map K.subtype = _
      rw [Γ.twoCoreAt_def]
      exact hh.trans (congrArg twoCoreIn hP)
    have hQmap : (QAt Γ cp.firstStep).map e.toMonoidHom = QAt Γ cp.a' := by
      change (q Γ cp.firstStep).map _ = q Γ cp.a'
      rw [← q_act, hmove]
    have hQreturn : (QAt Γ cp.a').map e.toMonoidHom = QAt Γ cp.firstStep := by
      change (q Γ cp.a').map _ = q Γ cp.firstStep
      rw [← q_act, hreturn]
    have hVreturn : (VAt Γ cp.a').map e.toMonoidHom = VAt Γ cp.firstStep := by
      change (v Γ cp.a').map _ = v Γ cp.firstStep
      rw [← v_act, hreturn]
    have hQg : (twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom =
        (QAt Γ cp.a').map K.subtype := by
      rw [← hQfirst, map_map, hf, ← map_map, hQmap]
    have hrelative {X Y : Type u} [Group X] [Group Y]
        (U V : Subgroup X) (f : X →* Y) (hi : Function.Injective f) :
        (U ⊓ centralizer (V : Set X)).map f =
          U.map f ⊓ centralizer (V.map f : Set Y) := by
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
        apply hi
        simpa only [map_mul] using mem_centralizer_iff.mp hc (f v) (mem_map_of_mem f hv)
    have hcontain : QAt Γ cp.firstStep ⊓ centralizer (VAt Γ cp.firstStep : Set K) ≤
        VAt Γ cp.firstStep ⊔ QAt Γ cp.a' := by
      have hh := map_mono (f := e.toMonoidHom)
        (ten_one_large_first_core_containment tenCtx middle hpath ctx.noTransvections)
      change (QAt Γ cp.a' ⊓ centralizer (VAt Γ cp.a' : Set K)).map e.toMonoidHom ≤
        (VAt Γ cp.a' ⊔ QAt Γ cp.firstStep).map e.toMonoidHom at hh
      rw [hrelative _ _ _ e.injective, Subgroup.map_sup, hQreturn, hVreturn, hQmap] at hh
      exact hh
    have hidx : (QAt Γ cp.a').relIndex (VAt Γ cp.firstStep) = 2 := by
      rw [← hQmap, ← hVreturn, relIndex_map_map_of_injective _ _ e.injective]
      exact ten_one_large_terminal_first_core_relIndex tenCtx middle hpath ctx.noTransvections
    have hnorm : VAt Γ cp.firstStep ≤ normalizer (QAt Γ cp.a' : Set K) :=
      (lemma_seven_four tenCtx.sectionSeven Γ cp).first_containment.2.trans
        (stabilizer_le_normalizer_q Γ _)
    let J := VAt Γ cp.firstStep ⊔ QAt Γ cp.a'
    have hNJ : QAt Γ cp.a' ≤ J := le_sup_right
    let _ : ((QAt Γ cp.a').subgroupOf J).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le hnorm (QAt Γ cp.a').le_normalizer)
    have hidxJ : (QAt Γ cp.a').relIndex J = 2 := by
      have hh := relIndex_sup_right ((VAt Γ cp.firstStep).subgroupOf J)
        ((QAt Γ cp.a').subgroupOf J)
      rw [← subgroupOf_sup le_sup_left le_sup_right,
        relIndex_subgroupOf le_rfl, relIndex_subgroupOf (show VAt Γ cp.firstStep ≤ J from le_sup_left)] at hh
      exact hh.trans hidx
    rw [hQg, ctx.first_residual_structure.2.2.1, ← Subgroup.map_sup]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hQfirst, ← hrelative _ _ K.subtype K.subtype_injective]
      exact map_mono hcontain
    · rw [relIndex_map_map_of_injective _ _ K.subtype_injective]
      exact hidxJ
    · intro hh
      have hn := (map_le_map_iff_of_injective K.subtype_injective).mp hh
      have he : (QAt Γ cp.a').relIndex (VAt Γ cp.firstStep) = 1 := relIndex_eq_one.mpr hn
      omega

/-- A single middle-stabilizer conjugate has a common derived eight and
 a residual intersection of order sixteen, and carries the central
 involution into the original derived subgroup. -/
public theorem LargeTerminalContext.exists_derived_conjugate_residual_sixteen
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ g : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 ∧
      Nat.card (ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 16 := by
  obtain ⟨g, hz, hI, hJ, _, _, _⟩ := derived_conjugate_seed_geometry ctx z hgen
  exact ⟨g, hz, hI, hJ⟩

private theorem conjugate_geometry_residual_transport
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z y g₀ r : G) (hr : r ∈ ctx.firstResidual)
    (hzD : MulAut.conj g₀ z ∈ DerivedAmbient ctx.firstResidual)
    (hI : Nat.card (DerivedAmbient ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g₀).toMonoidHom : Subgroup G) = 8)
    (hJ : Nat.card (ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g₀).toMonoidHom : Subgroup G) = 16)
    (hyQ : MulAut.conj r y ∈ (twoCoreIn ctx.second).map (MulAut.conj g₀).toMonoidHom) :
    ∃ g : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 ∧
      Nat.card (ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 16 ∧
      y ∈ (twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom := by
  let R := ctx.firstResidual
  let D := DerivedAmbient R
  let e := MulAut.conj r⁻¹
  let g := r⁻¹ * g₀
  have hcompose : (MulAut.conj g).toMonoidHom =
      e.toMonoidHom.comp (MulAut.conj g₀).toMonoidHom := by
    ext x
    simp [g, e, MulAut.conj_apply, mul_assoc]
  have hRmap : R.map e.toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer (R.inv_mem hr))
  have hDmap : D.map e.toMonoidHom = D := by
    rw [show D = ⁅R, R⁆ from map_subtype_commutator _, map_commutator, hRmap]
  have hDg : D.map (MulAut.conj g).toMonoidHom =
      (D.map (MulAut.conj g₀).toMonoidHom).map e.toMonoidHom := by
    rw [hcompose, map_map]
  have hz : MulAut.conj g z = e (MulAut.conj g₀ z) := by
    exact congrArg (fun f : G →* G => f z) hcompose
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · change MulAut.conj g z ∈ D
    rw [hz, ← hDmap]
    exact mem_map_of_mem e.toMonoidHom hzD
  · change Nat.card (D ⊓ D.map (MulAut.conj g).toMonoidHom : Subgroup G) = 8
    have hi : (D ⊓ D.map (MulAut.conj g₀).toMonoidHom).map e.toMonoidHom =
        D ⊓ (D.map (MulAut.conj g₀).toMonoidHom).map e.toMonoidHom := by
      rw [map_inf _ _ _ e.injective, hDmap]
    rw [hDg, ← hi, card_map_of_injective e.injective]
    exact hI
  · change Nat.card (R ⊓ D.map (MulAut.conj g).toMonoidHom : Subgroup G) = 16
    rw [hDg, ← hRmap, ← map_inf _ _ _ e.injective, card_map_of_injective e.injective]
    exact hJ
  · rw [hcompose, ← map_map]
    have hh := mem_map_of_mem e.toMonoidHom hyQ
    simpa [e, MulAut.conj_apply, mul_assoc] using hh

/-- The five-fixed involution lies in the core of one conjugate having
the common derived eight, residual sixteen and prescribed central line.
The witness is chosen by residual conjugation, not just by cardinality. -/
public theorem LargeTerminalContext.exists_derived_conjugate_residual_sixteen_mem_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : orderOf y = 2) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ∃ g : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 ∧
      Nat.card (ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 16 ∧
      y ∈ (twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hz, hI, hJ, hC, hindex, hout⟩ := derived_conjugate_seed_geometry ctx z hgen
  obtain ⟨r, hr, hyr⟩ := residual_conjugate_mem_seed_core ctx A hA hAN hfixed
    y hy hyQ hyA hyR ((twoCoreIn ctx.second).map (MulAut.conj g).toMonoidHom) hC hindex hout
  exact conjugate_geometry_residual_transport ctx z y g r hr hz hI hJ hyr

/-- One chosen conjugate has all three intersection conclusions and places
the residual-intersection displacement in its central line. -/
public theorem LargeTerminalContext.exists_derived_conjugate_residual_seed_bound
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : orderOf y = 2) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ∃ g : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 ∧
      Nat.card (ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 16 ∧
      ⁅ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom, zpowers y⁆ ≤
        (CenterAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hz, hI, hJ, hycore⟩ :=
    ctx.exists_derived_conjugate_residual_sixteen_mem_core A hA hAN hfixed z hgen y hy hyQ hyA hyR
  refine ⟨g, hz, hI, hJ, ?_⟩
  have hh := congrArg (fun H : Subgroup G => H.map (MulAut.conj g).toMonoidHom)
    ctx.derived_commutator_second_core
  rw [map_commutator] at hh
  exact (commutator_mono inf_le_right (zpowers_le.mpr hycore)).trans_eq hh

/-- A middle-stabilizer conjugate of the derived residual meets it in an
actual elementary eight and carries the central involution into it. -/
public theorem LargeTerminalContext.exists_derived_conjugate_eight
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ g : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 := by
  obtain ⟨g, hz, hI, _⟩ := ctx.exists_derived_conjugate_residual_sixteen z hgen
  exact ⟨g, hz, hI⟩

/-- Any conjugate with a residual intersection of order sixteen contains
an element of that intersection moved by the five-fixed element. -/
public theorem LargeTerminalContext.exists_moved_element_in_conjugate_residual
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (g : G)
    (hI : Nat.card (DerivedAmbient ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8)
    (hJ : Nat.card (ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 16) :
    ∃ v : G, v ∈ ctx.firstResidual ∧
      v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      v ∉ DerivedAmbient ctx.firstResidual ∧ ⁅v, y⁆ ≠ 1 := by
  let D := DerivedAmbient ctx.firstResidual
  let Dg := D.map (MulAut.conj g).toMonoidHom
  have hnot : ¬ ctx.firstResidual ⊓ Dg ≤ D ⊓ Dg := by
    intro h
    have hh := card_le_of_le h
    change Nat.card (ctx.firstResidual ⊓ Dg : Subgroup G) ≤ Nat.card (D ⊓ Dg : Subgroup G) at hh
    rw [hJ, hI] at hh
    omega
  obtain ⟨v, hv, hout⟩ := SetLike.not_le_iff_exists.mp hnot
  have hvD : v ∉ D := fun h => hout ⟨h, hv.2⟩
  refine ⟨v, hv.1, hv.2, hvD, ?_⟩
  intro hcomm
  apply hvD
  change v ∈ DerivedAmbient ctx.firstResidual
  rw [← ctx.five_fixed_residual_centralizer_eq_derived A hA hAN hfixed y hyQ hyA hyR]
  exact ⟨hv.1, mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_commute.mp hcomm).eq⟩

/-- The simultaneous intersection geometry already gives a nontrivial
 displacement. Only its containment in the conjugate central line remains. -/
public theorem LargeTerminalContext.exists_derived_conjugate_nontrivial_displacement
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ∃ g v : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 ∧
      v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      v ∈ ctx.firstResidual ∧ v ∉ DerivedAmbient ctx.firstResidual ∧ ⁅v, y⁆ ≠ 1 := by
  obtain ⟨g, hz, hI, hJ⟩ := ctx.exists_derived_conjugate_residual_sixteen z hgen
  obtain ⟨v, hvR, hvDg, hvD, hcomm⟩ :=
    ctx.exists_moved_element_in_conjugate_residual A hA hAN hfixed y hyQ hyA hyR g hI hJ
  exact ⟨g, v, hz, hI, hvDg, hvR, hvD, hcomm⟩

/-- A central commutator bound on the residual intersection supplies the
requested nontrivial central displacement for the same conjugate. -/
public theorem LargeTerminalContext.central_displacement_of_residual_seed_bound
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (g : G)
    (hI : Nat.card (DerivedAmbient ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8)
    (hJ : Nat.card (ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 16)
    (hcentral : ⁅ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom, zpowers y⁆ ≤
      (CenterAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom) :
    ∃ v : G, v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅zpowers v, zpowers y⁆ ≤
        (CenterAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅v, y⁆ ≠ 1 := by
  obtain ⟨v, hvR, hvDg, _, hcomm⟩ :=
    ctx.exists_moved_element_in_conjugate_residual A hA hAN hfixed y hyQ hyA hyR g hI hJ
  have hvJ : zpowers v ≤ ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom :=
    zpowers_le.mpr ⟨hvR, hvDg⟩
  exact ⟨v, hvDg, (commutator_mono hvJ le_rfl).trans hcentral, hcomm⟩

/-- A five-fixed involution outside the residual has a nontrivial central
displacement in one conjugate of the derived residual. The same conjugate
carries the central involution into the derived group and meets it in an eight.
The residual seed bound chooses the conjugate before the moved element. -/
public theorem LargeTerminalContext.exists_derived_conjugate_central_displacement
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : orderOf y = 2) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ∃ g v : G, MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual ∧
      Nat.card (DerivedAmbient ctx.firstResidual ⊓
        (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8 ∧
      v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅zpowers v, zpowers y⁆ ≤
        (CenterAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅v, y⁆ ≠ 1 := by
  obtain ⟨g, hz, hI, hJ, hcentral⟩ :=
    ctx.exists_derived_conjugate_residual_seed_bound A hA hAN hfixed z hgen y hy hyQ hyA hyR
  obtain ⟨v, hvDg, hvZg, hcomm⟩ :=
    ctx.central_displacement_of_residual_seed_bound A hA hAN hfixed y hyQ hyA hyR g hI hJ hcentral
  exact ⟨g, v, hz, hI, hvDg, hvZg, hcomm⟩

private theorem large_layer_of_displacement
    {G : Type u} [Group G] [Finite G]
    (D Z I : Subgroup G) (hDZ : D ≤ normalizer (Z : Set G))
    (hID : I ≤ D) (hI : Nat.card I = 8)
    (y : G) (hyI : y ∈ centralizer (I : Set G))
    (v : G) (hvD : v ∈ D)
    (hvZ : ⁅zpowers v, zpowers y⁆ ≤ Z) (hvy : ⁅v, y⁆ ≠ 1) :
    ∃ E : Subgroup G, E ≤ D ∧ 16 ≤ Nat.card E ∧ ⁅E, zpowers y⁆ ≤ Z := by
  let E := commutatorPreimage D (zpowers y) Z
  have hIY : ⁅I, zpowers y⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mpr (zpowers_le.mpr hyI))
  have hIE : I ≤ E := le_commutatorPreimage hID (hIY ▸ bot_le)
  have hvE : v ∈ E := (le_commutatorPreimage (zpowers_le.mpr hvD) hvZ) (mem_zpowers v)
  have hvI : v ∉ I := by
    intro hv
    exact hvy (commutatorElement_eq_one_iff_commute.mpr
      (mem_centralizer_iff.mp hyI v hv))
  have hcard : 16 ≤ Nat.card E := by
    obtain ⟨n, hn⟩ := card_dvd_of_le hIE
    rw [hI] at hn
    by_contra hsmall
    have hbound : Nat.card E ≤ Nat.card I := by rw [hI]; omega
    have heq : I = E := eq_of_le_of_card_ge hIE hbound
    exact hvI (heq.symm ▸ hvE)
  exact ⟨E, commutatorPreimage_le D (zpowers y) Z, hcard,
    commutator_commutatorPreimage_le D (zpowers y) Z hDZ⟩

/-- A central displacement in a conjugate derived group supplies the full
sixteen-element fixed layer needed for transport. The common eight is the
literal intersection of the two derived groups. -/
public theorem LargeTerminalContext.conjugate_geometry_of_central_displacement
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G)
    (y : G) (hyD : y ∈ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (g v : G)
    (hzD : MulAut.conj g z ∈ DerivedAmbient ctx.firstResidual)
    (hI : Nat.card (DerivedAmbient ctx.firstResidual ⊓
      (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom : Subgroup G) = 8)
    (hvD : v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom)
    (hvZ : ⁅zpowers v, zpowers y⁆ ≤ (CenterAmbient ctx.firstResidual).map
      (MulAut.conj g).toMonoidHom)
    (hvy : ⁅v, y⁆ ≠ 1) :
    ∃ (g : G) (E : Subgroup G) (v : G),
      y ∈ (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom ∧
      E ≤ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      16 ≤ Nat.card E ∧
      ⁅E, zpowers y⁆ ≤ (CenterAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅v, y⁆ ≠ 1 := by
  let D := DerivedAmbient ctx.firstResidual
  let Z := CenterAmbient ctx.firstResidual
  let e := MulAut.conj g
  have hDZ : D ≤ normalizer (Z : Set G) :=
    ((map_subtype_le _ : D ≤ ctx.firstResidual).trans
      (le_centralizer_iff.mpr (centerAmbient_le_centralizer _))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hDgZg : D.map e.toMonoidHom ≤ normalizer (Z.map e.toMonoidHom : Set G) :=
    (map_mono hDZ).trans (le_normalizer_map _)
  have hyI : y ∈ centralizer (D ⊓ D.map e.toMonoidHom : Set G) :=
    centralizer_le inf_le_left hyD
  obtain ⟨E, hED, hE, hcomm⟩ := large_layer_of_displacement
    (D.map e.toMonoidHom) (Z.map e.toMonoidHom) (D ⊓ D.map e.toMonoidHom)
    hDgZg inf_le_right hI y hyI v hvD hvZ hvy
  refine ⟨g, E, v, ?_, hED, hE, hcomm, hvD, hvy⟩
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  apply mem_centralizer_singleton_iff.mpr
  apply e.injective
  simp only [map_mul, e.apply_symm_apply]
  exact (mem_centralizer_iff.mp hyD (e z) hzD).symm

/-- Every five-fixed involution in the second core outside the first residual
has a conjugate derived layer of order at least sixteen fixed modulo its center,
and acts nontrivially on that conjugate derived group. This is the geometric
input for involution transport in Thompson VI, printed p.630. -/
public theorem LargeTerminalContext.five_fixed_conjugate_geometry
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hy : orderOf y = 2) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ∃ (g : G) (E : Subgroup G) (v : G),
      y ∈ (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom ∧
      E ≤ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      16 ≤ Nat.card E ∧
      ⁅E, zpowers y⁆ ≤ (CenterAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      v ∈ (DerivedAmbient ctx.firstResidual).map (MulAut.conj g).toMonoidHom ∧
      ⁅v, y⁆ ≠ 1 := by
  obtain ⟨g, v, hzD, hI, hvD, hvZ, hvy⟩ :=
    ctx.exists_derived_conjugate_central_displacement A hA hAN hfixed z hgen y hy hyQ hyA hyR
  exact ctx.conjugate_geometry_of_central_displacement z y
    (ctx.five_fixed_centralizes_derived A hA hAN hfixed y hyQ hyA)
    g v hzD hI hvD hvZ hvy

end Stellmacher.Recognition
