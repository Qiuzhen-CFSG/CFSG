module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.RudvalisNormalizer.Transport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.RelativeComplementProjection
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Preservation of the original Rudvalis-cover complement

The original V is the unique L₁-invariant complement to the covering line
C = ⟨u⟩ in E = CV: the commutator identity V = [V,L₁] puts V inside
any invariant complement, and disjointness from C then gives equality.

The literal recognition map identifies E with the full inverse image of
the marked model eight. Hence the full max4 preimage J acts on E and fixes
C pointwise. Relative normality and the supplied Sylow premise make
C_T(u) ∩ L_u a Sylow subgroup of L_u. It preserves V by the original flag,
and the model normalizer bound places it in J. Thus a Sylow subgroup of J
fixes the projection E → C along V. The orbit of that projection has odd
size. Multiplying its conjugates gives a J-invariant retraction onto C;
its kernel is an invariant complement. The actual L₁ lies in J, so the
uniqueness calculation identifies this kernel with the original V.

This supplies the intervening model action argument using the genuine Sylow
hypothesis. All actions are literal conjugation and the projection is the
original recognition map. The result retains the complete fixed-centralizer
source configuration and only the three permitted marking premises: V=[V,L₁],
V≤L_u, and the marked image of V. Their producer is
`qt-14-07-fixed-ru-eight-marking`; the parent RudvalisNormalizer assembly
must discharge them. The final normalizer equality applies Transport's
conditional identification to the newly proved preservation theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.68(2), printed p.1071 (PDF p.1088), lines 54955–54967.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise BigOperators
open Rudvalis.SylowOvergroups Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

-- Averaging over the orbit, rather than the whole even-order actor, retains
-- the restriction to its fixed binary subgroup.
private theorem invariant_hom_of_sylow_fixed
    {A E C : Type*} [Group A] [Finite A] [Group E] [CommGroup C]
    (ρ : A →* MulAut E) (P : Sylow 2 A) (f : E →* C)
    (hP : ∀ p : P, ∀ x : E, f (ρ p x) = f x)
    (hC : ∀ c : C, c ^ 2 = 1) :
    ∃ F : E →* C, (∀ a x, F (ρ a x) = F x) ∧
      ∀ x, (∀ a, ρ a x = x) → F x = f x := by
  classical
  let : MulAction A (E →* C) := {
    smul := fun a q => q.comp (ρ a⁻¹).toMonoidHom
    one_smul := by
      intro q; ext x
      change q (ρ (1 : A)⁻¹ x) = q x
      simp
    mul_smul := by
      intro a b q; ext x
      change q (ρ (a * b)⁻¹ x) = q (ρ b⁻¹ (ρ a⁻¹ x))
      simp }
  have smul_apply (a : A) (q : E →* C) (x : E) :
      (a • q) x = q (ρ a⁻¹ x) := rfl
  have hPS : (P : Subgroup A) ≤ MulAction.stabilizer A f := by
    intro p hp
    change p • f = f
    ext x
    exact hP ⟨p⁻¹, P.inv_mem hp⟩ x
  have hodd : Odd (Nat.card (MulAction.orbit A f)) := by
    change Odd (MulAction.orbit A f).ncard
    rw [← MulAction.index_stabilizer]
    exact Nat.not_even_iff_odd.mp (fun h =>
      P.not_dvd_index ((even_iff_two_dvd.mp h).trans (index_dvd_of_le hPS)))
  let : Finite (MulAction.orbit A f) :=
    Finite.of_equiv (A ⧸ MulAction.stabilizer A f) (MulAction.orbitEquivQuotientStabilizer A f).symm
  let : Fintype (MulAction.orbit A f) := Fintype.ofFinite _
  let F : E →* C := ∏ q : MulAction.orbit A f, q.val
  refine ⟨F, ?_, ?_⟩
  · intro a x
    change (∏ q : MulAction.orbit A f, q.val) (ρ a x) = (∏ q : MulAction.orbit A f, q.val) x
    simp only [MonoidHom.finsetProd_apply]
    apply Fintype.prod_equiv (MulAction.toPerm a⁻¹)
    intro q
    change q.val (ρ a x) = (a⁻¹ • q.val) x
    rw [smul_apply, inv_inv]
  · intro x hx
    have hq (q : MulAction.orbit A f) : q.val x = f x := by
      obtain ⟨a, ha⟩ := q.property
      rw [← ha, smul_apply, hx]
    change (∏ q : MulAction.orbit A f, q.val) x = f x
    simp only [MonoidHom.finsetProd_apply, hq, Finset.prod_const, Finset.card_univ,
      Fintype.card_eq_nat_card]
    obtain ⟨n, hn⟩ := hodd
    rw [hn, pow_add, pow_mul, hC, one_pow, pow_one, one_mul]

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

omit [Finite G] in
private theorem complement_local_le_K : F.Li L 1 ≤ K F := by
  intro x hx
  change x ∈ (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype at hx
  obtain ⟨n, hn, rfl⟩ := hx
  let f : (L ⊓ F.H : Subgroup G) →* F.H := inclusion inf_le_right
  exact mem_map.mpr ⟨f n, map_pResidual_le 2 f (mem_map.mpr ⟨n, hn, rfl⟩), rfl⟩

private theorem complement_line_centralizes (u : F.U) (hu : (u : G) ∈ d.U₀) :
    zpowers (u : G) ≤ centralizer (F.Li L 1 : Set G) := by
  apply zpowers_le.mpr
  apply mem_centralizer_iff.mpr
  intro l hl
  exact mem_centralizer_singleton_iff.mp
    (d.K_le_fixedCentralizer u hu (complement_local_le_K hl))

/-- Uniqueness among the original actor's invariant complements. -/
theorem fixed_invariant_complement_unique (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hgen : V = ⁅V, F.Li L 1⁆) (B : Subgroup G)
    (hB : B ≤ zpowers (u : G) ⊔ V)
    (hdisj : zpowers (u : G) ⊓ B = ⊥)
    (hsup : zpowers (u : G) ⊔ B = zpowers (u : G) ⊔ V)
    (hn : F.Li L 1 ≤ normalizer (B : Set G)) : B = V := by
  let := d.abelian
  have hEU : zpowers (u : G) ⊔ V ≤ F.U := sup_le (zpowers_le.mpr u.property) (V_le_U F)
  have hEB : zpowers (u : G) ⊔ V ≤ normalizer (B : Set G) :=
    ((hEU.trans (le_centralizer F.U)).trans (centralizer_le (hB.trans hEU))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hpre : zpowers (u : G) ⊔ V ≤
      commutatorPreimage (zpowers (u : G) ⊔ V) (F.Li L 1) B := by
    rw [← hsup]
    refine sup_le (le_commutatorPreimage le_sup_left ?_)
      (le_commutatorPreimage le_sup_right (le_normalizer_iff_commutator_le_left.mp hn))
    rw [commutator_eq_bot_iff_le_centralizer.mpr (d.complement_line_centralizes u hu)]
    exact bot_le
  have hVB : V ≤ B := calc
    V = ⁅V, F.Li L 1⁆ := hgen
    _ ≤ ⁅zpowers (u : G) ⊔ V, F.Li L 1⁆ := commutator_mono le_sup_right le_rfl
    _ ≤ B := (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hEB)
  apply le_antisymm ?_ hVB
  intro b hb
  have hCV : zpowers (u : G) ≤ normalizer (V : Set G) :=
    (((zpowers_le.mpr u.property).trans (le_centralizer F.U)).trans
      (centralizer_le (V_le_U F))).trans (Subgroup.centralizer_le_normalizer _)
  have hm : b ∈ (zpowers (u : G) : Set G) * (V : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hCV]
    exact hB hb
  obtain ⟨c, hc, v, hv, he⟩ := hm
  have hcB : c ∈ B := by
    have h := B.mul_mem hb (B.inv_mem (hVB hv))
    rwa [← he, mul_inv_cancel_right] at h
  have hc1 : c = 1 := mem_bot.mp
    (hdisj ▸ (show c ∈ zpowers (u : G) ⊓ B from ⟨hc, hcB⟩))
  have hvb : v = b := by simpa only [hc1, one_mul] using he
  exact hvb ▸ hv

/-- The original V, rather than an unmarked isomorphic eight, is the unique
L₁-invariant complement to the covering line in its join with that line. -/
theorem fixed_seed_unique_invariant_complement (earlier : d.ModuleSeparation)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hout : ¬ d.fixedCentralizer u ≤ F.H) (hgen : V = ⁅V, F.Li L 1⁆) :
    ∃! B : Subgroup G, B ≤ zpowers (u : G) ⊔ V ∧
      zpowers (u : G) ⊓ B = ⊥ ∧
      zpowers (u : G) ⊔ B = zpowers (u : G) ⊔ V ∧
      F.Li L 1 ≤ normalizer (B : Set G) := by
  refine ⟨V, ⟨le_sup_right, d.fixed_line_inf_seed_eq_bot earlier u hu hne hout,
    rfl, (F.Li_le L 1).trans (inf_le_left.trans d.natural.chosen.normalizes)⟩, ?_⟩
  intro B hB
  exact d.fixed_invariant_complement_unique u hu hgen B hB.1 hB.2.1 hB.2.2.1 hB.2.2.2

namespace FixedRudvalisCover
variable {d} {u : F.U} {Lu : Subgroup G} (r : d.FixedRudvalisCover u Lu)

/-- The full inverse image of the marked eight is the original sixteen-group. -/
theorem markedEight_preimage (hV : V ≤ Lu)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) :
    (elementary 2).comap r.projection = (zpowers (u : G) ⊔ V).subgroupOf Lu := by
  rw [← hmap, comap_map_eq]
  have hk : r.projection.ker = (zpowers (u : G)).subgroupOf Lu := by
    rw [← r.kernel]
    exact (comap_map_eq_self_of_injective Lu.subtype_injective _).symm
  rw [hk, ← subgroupOf_sup hV (zpowers_le.mpr r.mem_component), sup_comm]

/-- This action normalizes the sixteen-group before normalization of V is known. -/
theorem max4Preimage_normalizes_join (hV : V ≤ Lu)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) :
    r.max4Preimage ≤ (normalizer ((zpowers (u : G) ⊔ V : Subgroup G) : Set G)).subgroupOf Lu := by
  rw [subgroupOf_normalizer_eq (sup_le (zpowers_le.mpr r.mem_component) hV)]
  rw [← r.markedEight_preimage hV hmap]
  apply le_trans ?_ ((elementary 2).le_normalizer_comap r.projection)
  exact comap_mono RankOneEightAction.max4_le_normalizer_eight

/-- The original Sylow restricts to a Sylow of the preimage which preserves V. -/
theorem max4Preimage_sylow_preserves_seed
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (hV : V ≤ Lu) (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) :
    ∃ P : Sylow 2 r.max4Preimage, ∀ p : P,
      ((p : r.max4Preimage) : Lu).val ∈ normalizer (V : Set G) := by
  obtain ⟨S, hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsyl hLu hn.isSubnormal
  have hTN : (T : Subgroup G) ≤ normalizer (V : Set G) := F.last ▸ F.invariant 3
  have hSN : ∀ s : Lu, s ∈ S → (s : G) ∈ normalizer (V : Set G) := by
    intro s hs
    have hm : (s : G) ∈ d.fixedSylow u ⊓ Lu := hS ▸ mem_map_of_mem Lu.subtype hs
    exact hTN hm.1.1
  have hSJ : (S : Subgroup Lu) ≤ r.max4Preimage := by
    intro s hs
    exact r.normalizer_le_max4Preimage hV hmap ⟨s.property, hSN s hs⟩
  refine ⟨S.subtype hSJ, ?_⟩
  intro p
  exact hSN p.val.val p.property

/-- Preservation of the original complement, using the actual Sylow action
on the full marked-eight preimage. -/
private theorem max4Preimage_le_seed_normalizer_of_sylow
    (earlier : d.ModuleSeparation) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hout : ¬ Lu ≤ F.H) (hKLu : K F ≤ Lu)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (hgen : V = ⁅V, F.Li L 1⁆)
    (hV : V ≤ Lu) (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) :
    r.max4Preimage ≤ (normalizer (V : Set G)).subgroupOf Lu := by
  classical
  let C := zpowers (u : G)
  let E := C ⊔ V
  have hCE : C ≤ E := le_sup_left
  have hVE : V ≤ E := le_sup_right
  have hEU : E ≤ F.U := sup_le (zpowers_le.mpr u.property) (V_le_U F)
  let := d.U_elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hEU
  have hd : Disjoint V C := disjoint_iff.mpr
    ((inf_comm V C).trans (d.fixed_line_inf_seed_eq_bot earlier u hu hne
      (fun hc => hout (hLu.trans hc))))
  let χ : E →* C := relativeComplementProjection hVE hCE (sup_comm V C) hd
  have hχC (c : C) : χ (inclusion hCE c) = c :=
    relativeComplementProjection_inclusion hVE hCE (sup_comm V C) hd c
  have hχker : χ.ker = V.subgroupOf E :=
    relativeComplementProjection_ker hVE hCE (sup_comm V C) hd
  let J := r.max4Preimage
  let jG : J →* G := Lu.subtype.comp J.subtype
  have hJN (j : J) : jG j ∈ normalizer (E : Set G) :=
    r.max4Preimage_normalizes_join hV hmap j.property
  let ρ : J →* MulAut E := E.normalizerMonoidHom.comp
    (jG.codRestrict (normalizer (E : Set G)) hJN)
  have hρ (j : J) (x : E) : (ρ j x : G) = jG j * x * (jG j)⁻¹ := rfl
  have hρC (j : J) (c : C) : ρ j (inclusion hCE c) = inclusion hCE c := by
    apply Subtype.ext
    rw [hρ]
    have hj : jG j ∈ centralizer (C : Set G) := by
      change jG j ∈ centralizer (zpowers (u : G) : Set G)
      rw [zpowers_eq_closure, centralizer_closure]
      exact hLu j.val.property
    change jG j * (c : G) * (jG j)⁻¹ = (c : G)
    rw [← mem_centralizer_iff.mp hj c c.property, mul_inv_cancel_right]
  obtain ⟨P, hP⟩ := r.max4Preimage_sylow_preserves_seed hLu hn hsyl hV hmap
  have hχP (p : P) (x : E) : χ (ρ p x) = χ x := by
    obtain ⟨⟨c, v⟩, hcv⟩ := (relative_isComplement hVE hCE (sup_comm V C) hd).2 x
    change (c : E) * (v : E) = x at hcv
    have hc : ρ (p : J) (c : E) = c := hρC p ⟨c, c.property⟩
    have hv : χ (v : E) = 1 := by
      change (v : E) ∈ χ.ker
      rw [hχker]
      exact v.property
    have hpv : χ (ρ (p : J) (v : E)) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hχker]
      change (ρ (p : J) (v : E) : G) ∈ V
      rw [hρ]
      exact (mem_normalizer_iff.mp (hP p) v).mp v.property
    rw [← hcv, map_mul, map_mul, map_mul, hc, hv, hpv]
  have hCpow (c : C) : c ^ 2 = 1 := by
    apply Subtype.ext
    let := d.U_elementary
    exact elemPow_eq_one_of_isElementaryAbelian (c : G) ((zpowers_le.mpr u.property) c.property)
  obtain ⟨ψ, hψinv, hψfix⟩ := invariant_hom_of_sylow_fixed ρ P χ hχP hCpow
  have hψC (c : C) : ψ (inclusion hCE c) = c :=
    (hψfix _ (fun j => hρC j c)).trans (hχC c)
  let B : Subgroup G := ψ.ker.map E.subtype
  have hBE : B ≤ E := map_subtype_le _
  have hCB : C ⊓ B = ⊥ := by
    apply bot_unique
    intro x hx
    obtain ⟨y, hy, he⟩ := hx.2
    have hyC : (y : G) ∈ C := by
      change E.subtype y ∈ C
      rw [he]
      exact hx.1
    let c : C := ⟨y, hyC⟩
    have hcy : inclusion hCE c = y := rfl
    have hc1 : c = 1 := (hψC c).symm.trans (hcy ▸ hy)
    exact he.symm.trans (congrArg Subtype.val hc1)
  have hsup : C ⊔ B = E := by
    apply le_antisymm (sup_le hCE hBE)
    intro x hx
    let y : E := ⟨x, hx⟩
    let c : C := ψ y
    have hk : (inclusion hCE c)⁻¹ * y ∈ ψ.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hψC]
      exact inv_mul_cancel _
    have hm := mul_mem_sup c.property (mem_map_of_mem E.subtype hk)
    simpa only [map_mul, map_inv, subtype_apply, coe_inclusion, mul_inv_cancel_left] using hm
  have hJB : J ≤ (normalizer (B : Set G)).subgroupOf Lu := by
    intro j hj
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine mem_map.mpr ⟨ρ ⟨j, hj⟩ y, ?_, hρ ⟨j, hj⟩ y⟩
      exact (hψinv ⟨j, hj⟩ y).trans hy
    · intro hx
      have hh : (j : G)⁻¹ * ((j : G) * x * (j : G)⁻¹) * j ∈ B := by
        obtain ⟨y, hy, he⟩ := hx
        refine mem_map.mpr ⟨ρ (⟨j, hj⟩ : J)⁻¹ y, ?_, ?_⟩
        · exact (hψinv _ y).trans hy
        · change (ρ (⟨j, hj⟩ : J)⁻¹ y : G) = _
          rw [hρ, map_inv, inv_inv]
          change (j : G)⁻¹ * (y : G) * j = _
          rw [show (y : G) = (j : G) * x * (j : G)⁻¹ from he]
      simpa only [inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh
  have hAJ : F.Li L 1 ≤ J.map Lu.subtype := by
    intro a ha
    have haLu : a ∈ Lu := hKLu (complement_local_le_K ha)
    have haN : a ∈ normalizer (V : Set G) :=
      d.natural.chosen.normalizes (F.Li_le L 1 ha).1
    exact mem_map.mpr ⟨⟨a, haLu⟩,
      r.normalizer_le_max4Preimage hV hmap ⟨haLu, haN⟩, rfl⟩
  have hAB : F.Li L 1 ≤ normalizer (B : Set G) := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := hAJ ha
    exact hJB hj
  have hBV : B = V := d.fixed_invariant_complement_unique u hu hgen B hBE hCB hsup hAB
  rwa [hBV] at hJB

/-- Source application for 14.7.68(2), retaining the genuine fixed-centralizer
and component hypotheses. The only additional inputs are the three marked-eight
premises supplied by `qt-14-07-fixed-ru-eight-marking`. -/
theorem max4Preimage_le_seed_normalizer
    (earlier : d.ModuleSeparation) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (_hfix : d.FixedModuloPoint u) (_hNK : normalizer (K F : Set G) = F.H)
    (_hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (hLu : Lu ≤ d.fixedCentralizer u)
    (_hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (_hq : IsQuasisimple Lu)
    (hgen : V = ⁅V, F.Li L 1⁆)
    (hV : V ≤ Lu) (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) :
    r.max4Preimage ≤ (normalizer (V : Set G)).subgroupOf Lu :=
  r.max4Preimage_le_seed_normalizer_of_sylow earlier hu hne hLu hn hout hKLu.le hsyl hgen hV hmap

/-- The reverse inclusion just proved discharges the transport module's
normalizer-identification premise on the actual original subgroups. -/
theorem original_normalizer_eq_max4Preimage
    (earlier : d.ModuleSeparation) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hNK : normalizer (K F : Set G) = F.H)
    (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (hq : IsQuasisimple Lu)
    (hgen : V = ⁅V, F.Li L 1⁆)
    (hV : V ≤ Lu) (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) :
    (d.fixedComponentNormalizer Lu).subgroupOf Lu = r.max4Preimage :=
  r.normalizer_eq_max4Preimage hV hmap
    (r.max4Preimage_le_seed_normalizer earlier hu hne hfix hNK hmax hsyl hLu hc hn
      hKLu hout hq hgen hV hmap)

end FixedRudvalisCover
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
