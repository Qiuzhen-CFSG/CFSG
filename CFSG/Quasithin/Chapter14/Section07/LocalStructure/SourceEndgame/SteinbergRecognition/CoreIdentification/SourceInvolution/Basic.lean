module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.CommutatorGeneration
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.Preparation
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# A critical kernel involution and coprime parabolic capture

The reciprocal commutator in the opening paragraph of 14.7.70 selects an
involution in the original Uα∩Q_H that does not centralize U. This element
lies in the kernel of the original star map.

For an actual cubic subgroup J of L₁, coprime action gives
Q_H = [Q_H,J] C_{Q_H}(J). A K-element normalizing J preserves the first
factor. If C_{Q_H}(J) ≤ C_H(U), the proved 14.7.71 centralizer bound puts
its displacement on the second factor inside U. Consequently it carries
Q_H∩L₁ into L₁, and relative H-normality places the conjugate in O₂(L₁).
When the same element takes V to an opposite plane generating U with V,
its conjugate of the selected involution cannot centralize V, hence escapes Q.

The source construction of the torus geometry and the containment S≤L₁
remain separate obligations. The final theorem here is conditional on those
inputs, not a completed proof of 14.7.72. No involutory quotient lift, splitting,
or equality S=O₂(L) is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.70, printed p.1073, and 14.7.72, printed p.1076 (PDF p.1093).
-/

public section

open Subgroup Representation
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

/-- Actual cubic subgroup and normalizer element on the original H and U.
Construction requires the original natural marking and source duality; the
record does not contain an involution or a conjugate-placement conclusion. -/
structure TorusGeometry (F : InvariantFlag T V 3) (L : Subgroup G) where
  torus : Subgroup G
  torus_le : torus ≤ F.Li L 1
  torus_card : Nat.card torus = 3
  mover : F.H
  mover_mem : (mover : G) ∈ K F
  mover_normalizes : (mover : G) ∈ normalizer (torus : Set G)
  fixed_le : F.H.pCoreIn 2 ⊓ centralizer (torus : Set G) ≤
    F.H ⊓ centralizer (F.U : Set G)
  span : V ⊔ conjugate V (mover : G) = F.U

omit [Finite G] in
private theorem H_normalizes_QH : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
  F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))

omit [Finite G] in
private theorem T_normalizes_parabolic
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
  change (T : Subgroup G) ≤ normalizer
    (((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype) : Set G)
  exact ((le_inf hTL ((F.invariant 1).trans F.H.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (L ⊓ F.H) (pResidual 2 (L ⊓ F.H : Subgroup G)))

omit [Finite G] in
private theorem QH_le_T : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
    (map_subgroupOf_eq_of_le (F.invariant 1))

include d in
/-- The starting involution comes from the kernel of star, using the reciprocal
commutator in the opening paragraph of 14.7.70. -/
theorem exists_critical_involution (c : CriticalPath (L := L) F)
    (hrecip : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ = F.Vi 1) :
    ∃ u : c.Uα, orderOf u = 2 ∧ (u : G) ∈ F.H.pCoreIn 2 ∧
      (u : G) ∉ centralizer (F.U : Set G) := by
  have hn : ¬ c.Uα ⊓ F.H.pCoreIn 2 ≤ centralizer (F.U : Set G) := by
    intro h
    have hb := commutator_eq_bot_iff_le_centralizer.mpr h
    rw [hrecip] at hb
    have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hb, card_bot] at hc
    omega
  obtain ⟨x, hx, hxc⟩ := SetLike.not_le_iff_exists.mp hn
  let := d.U_elementary
  let : IsElementaryAbelian 2 c.Uα :=
    IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  let a : c.Uα := ⟨x,hx.1⟩
  have hne : a ≠ 1 := by
    intro he
    apply hxc
    have he' : x = 1 := congrArg Subtype.val he
    rw [he']
    exact (centralizer (F.U : Set G)).one_mem
  have hs : a ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1
  exact ⟨a, orderOf_eq_prime hs hne, hx.2, hxc⟩

/-- Coprime decomposition and the existing 14.7.71 centralizer theorem show
that the torus normalizer preserves the required intersection with L₁. -/
theorem conjugate_mem_parabolic (c : CriticalPath (L := L) F)
    (earlier : ChiefFactors.Earlier d c) (g : TorusGeometry F L)
    (hSP : S F L ≤ F.Li L 1)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (x : G) (hxQ : x ∈ F.H.pCoreIn 2) (hxP : x ∈ F.Li L 1) :
    (g.mover : G) * x * (g.mover : G)⁻¹ ∈ F.Li L 1 := by
  let R := F.H.pCoreIn 2
  let P := F.Li L 1
  let B := ⁅R,g.torus⁆
  let C := R ⊓ centralizer (g.torus : Set G)
  have hPH : P ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hJR : g.torus ≤ normalizer (R : Set G) :=
    (g.torus_le.trans hPH).trans H_normalizes_QH
  have hRP : R ≤ normalizer (P : Set G) := QH_le_T.trans (T_normalizes_parabolic hTL)
  have hBP : B ≤ P := (commutator_mono le_rfl g.torus_le).trans
    (le_normalizer_iff_commutator_le_right.mp hRP)
  have hUP : F.U ≤ P := (U_le_S (F := F) (L := L)).trans hSP
  have hp := isPGroup_pCoreIn 2 F.H
  have hsolv : Group.IsSolvable R := @IsNilpotent.to_isSolvable R _ hp.isNilpotent
  have hcop : Nat.Coprime (Nat.card g.torus) (Nat.card R) := by
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [g.torus_card,hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hR : R = B ⊔ C := eq_commutator_sup_centralizer_of_solvable_coprime R g.torus
    hJR hsolv hcop
  have hprod : x ∈ (B : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left B C
      (inf_le_left.trans (normalizer_commutator_ge_left R g.torus)), ← hR]
    exact hxQ
  obtain ⟨b,hb,z,hz,rfl⟩ := hprod
  have hzP : z ∈ P := by
    have hh := P.mul_mem (P.inv_mem (hBP hb)) hxP
    simpa only [inv_mul_cancel_left] using hh
  have hnB : (g.mover : G) ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (H_normalizes_QH g.mover.property),
      mem_normalizer_iff_map_conj_eq.mp g.mover_normalizes]
  have hnz : (g.mover : G) * z * (g.mover : G)⁻¹ ∈ P := by
    have hc := ChiefFactors.centralizer_commutator d c earlier
      (commutator_mem_commutator g.mover_mem (g.fixed_le hz))
    have hh := P.mul_mem (hUP hc) hzP
    simpa only [commutatorElement_def, inv_mul_cancel_right] using hh
  have hnb := hBP ((mem_normalizer_iff.mp hnB b).mp hb)
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using P.mul_mem hnb hnz

omit [Finite G] in
/-- Normality here is relative to H, so its intersection with L₁ lies in
O₂(L₁), the two-core rather than the two-residual. -/
theorem intersection_le_parabolic_core :
    F.H.pCoreIn 2 ⊓ F.Li L 1 ≤ (F.Li L 1).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 F.H).to_le inf_le_left) inf_le_right
  exact (le_inf (((F.Li_le L 1).trans inf_le_right).trans H_normalizes_QH)
    (F.Li L 1).le_normalizer).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
private theorem conjugate_not_centralizes_seed (g : TorusGeometry F L)
    (x : G) (hx : x ∈ centralizer (V : Set G))
    (hxU : x ∉ centralizer (F.U : Set G)) :
    (g.mover : G) * x * (g.mover : G)⁻¹ ∉ centralizer (V : Set G) := by
  intro hm
  apply hxU
  have hVC : V ≤ centralizer ({x} : Set G) := by
    intro v hv y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (hx v hv).symm
  have hVnC : conjugate V (g.mover : G) ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨v,hv,rfl⟩ y hy
    rw [Set.mem_singleton_iff.mp hy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    apply (MulAut.conj (g.mover : G)).injective
    have hh := hm v hv
    simpa [MulAut.conj_apply, mul_assoc] using hh.symm
  have hUC : F.U ≤ centralizer ({x} : Set G) :=
    g.span ▸ sup_le hVC hVnC
  intro u hu
  exact (hUC hu x (Set.mem_singleton x)).symm

/-- Conditional final assembly. The remaining producer constructs TorusGeometry;
this theorem does not assert that its source construction is complete. -/
theorem exists_source_involution_of_torus (c : CriticalPath (L := L) F)
    (earlier : ChiefFactors.Earlier d c) (g : TorusGeometry F L)
    (hSP : S F L ≤ F.Li L 1)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hSQ : S F L ≤ Q T L)
    (hrecip : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ = F.Vi 1) :
    ∃ u : c.Uα, orderOf u = 2 ∧ ∃ h : F.H,
      (h : G) * u * (h : G)⁻¹ ∈ F.H.pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∈ (F.Li L 1).pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∉ Q T L := by
  obtain ⟨u,hu,huQ,huC⟩ := exists_critical_involution d c hrecip
  have hAS : c.Uα ≤ S F L := ChiefFactors.critical_le_S c earlier.conjugate
  have hq := (mem_normalizer_iff.mp (H_normalizes_QH g.mover.property) (u : G)).mp huQ
  have hp := conjugate_mem_parabolic d c earlier g hSP hTL u huQ
    (hSP (hAS u.property))
  refine ⟨u,hu,g.mover,hq,intersection_le_parabolic_core ⟨hq,hp⟩,?_⟩
  intro hh
  exact conjugate_not_centralizes_seed g u
    (d.natural.chosen.core_centralizes (hSQ (hAS u.property))) huC
    (d.natural.chosen.core_centralizes hh)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution
