module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Intermediate
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Overgroups
public import Theory.Quasithin.NormalTwoRank
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankComplementaryCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# Three-rank in the section-centralizer branch of 14.7.67

Let N = N_G(K), D = C_N(K/O₂(K)), Y = DR₁, and J = J(Y).
The original nonidentity point lies in U ≤ O₂(K) ≤ O₂(N), so quasithinness
bounds m₃(N) by two. Modulo O₂(N), the image of K is the actual A₅ obtained
from the source map qH. The image of D centralizes it. Since A₅ is centerless
and has a cubic subgroup, that subgroup contributes an independent direction
to the three-rank of D's image. Thus m₃(D) ≤ 1.

Both quotient comparisons use two-group kernels; arbitrary quotient rank
monotonicity is not used. Finally Y/D is a two-group, giving m₃(Y) = m₃(D).
The bounds for the actual J and JR₁ discharge the rank premise in the solvable
Thompson assembly. None of maximality in L*, relative Sylow control, Baumann
control, or the contrary assumption that D is not a two-group is needed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed pp.1070–1071, PDF pp.1087–1088.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)
include d

/-- The original point gives a nontrivial normal two-subgroup of N_G(K),
so its three-rank is bounded by actual ambient quasithinness. -/
theorem residual_normalizer_threeRank_le_two : primeRank 3 (normalizer (K F : Set G)) ≤ 2 := by
  let N := normalizer (K F : Set G)
  have hcore : (K F).pCoreIn 2 ≤ N.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (K F).le_normalizer le_rfl
  have hz : d.z ∈ (K F).pCoreIn 2 := d.U_le_K_core (d.conjugationSection.kernel_le
    (d.point.symm ▸ mem_zpowers d.z))
  have hne : pCore 2 N ≠ ⊥ := by
    intro he
    have hm := hcore hz
    change d.z ∈ (pCore 2 N).map N.subtype at hm
    rw [he, Subgroup.map_bot, mem_bot] at hm
    exact d.z_ne_one hm
  exact Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup
    d.counterexample.qtke.quasithin N (pCore 2 N) hne pCore_isPGroup
    3 (by decide) (by decide)

/-- Centralizing the actual alternating section costs D one of the two
available cubic directions in N_G(K). -/
theorem residual_D_threeRank_le_one : primeRank 3 (D F) ≤ 1 := by
  let N := normalizer (K F : Set G)
  let A := (K F).subgroupOf N
  let B := (D F).subgroupOf N
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let q := QuotientGroup.mk' (pCore 2 N)
  let Abar := A.map q
  let Bbar := B.map q
  let eA : A ≃* K F := subgroupOfEquivOfLe (K F).le_normalizer
  let e : Abar ≃* alternatingGroup (Fin 5) :=
    (coreQuotientEquivImage 2 A).symm |>.trans
      ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans d.K_quotient_equiv_A5)
  have hcomm : Bbar ≤ centralizer (Abar : Set (N ⧸ pCore 2 N)) := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    have hc : ⁅b, a⁆ ∈ pCore 2 N := by
      apply (mem_map_iff_mem N.subtype_injective).mp
      exact (pCoreIn_mono_of_normalizes (K F).le_normalizer le_rfl)
        (commutator_le.mp (D_commutator (F := F)) (b : G) hb (a : G) ha)
    have he : ⁅q b, q a⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have hcenter : ∀ x : center Abar, x ^ 2 = 1 := by
    intro x
    have hx : e x ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨a, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e ((mem_center_iff.mp x.property) a)
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hx
    have hx1 : x = 1 := Subtype.ext (e.injective (hx.trans e.map_one.symm))
    rw [hx1, one_pow]
  have hdiv : 3 ∣ Nat.card Abar := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hplus := Subgroup.one_add_primeRank_le_sup_of_centralizes
    (by decide : Odd 3) Abar Bbar hcomm hcenter hdiv
  have hquot : primeRank 3 (N ⧸ pCore 2 N) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      d.residual_normalizer_threeRank_le_two
  have hbar : primeRank 3 Bbar ≤ 1 := by
    have hle := primeRank_subgroup_le 3 (Abar ⊔ Bbar)
    omega
  let f := q.comp B.subtype
  have hf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.comp B.subtype).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hrange : f.range = Bbar := by
    rw [MonoidHom.range_comp, range_subtype]
  have hr : primeRank 3 B ≤ primeRank 3 Bbar := by
    have hh := (primeRank_quotient_eq_of_isTwoGroup 3 (by decide) f.ker hf).symm
    rw [primeRank_congr 3 (QuotientGroup.quotientKerEquivRange f), hrange] at hh
    exact hh.le
  rw [primeRank_congr 3 (subgroupOfEquivOfLe D_le_normalizer)] at hr
  exact hr.trans hbar

omit d [AddCommGroup W] [Module (ZMod 2) W] in
/-- The quotient by the relatively normal D is generated by the image of
R₁, a two-group, so adjoining R₁ does not change three-rank. -/
theorem residual_Y_threeRank_eq_D : primeRank 3 (Y L F) = primeRank 3 (D F) := by
  let A := Y L F
  let B := (D F).subgroupOf A
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (D F).le_normalizer residual_R_normalizes_D)
  have hgen : B ⊔ (F.Ri L 1).subgroupOf A = ⊤ := by
    rw [← subgroupOf_sup (show D F ≤ A from le_sup_left)
      (show F.Ri L 1 ≤ A from le_sup_right)]
    exact subgroupOf_self A
  have hp : IsPGroup 2 (A ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B _
      ((T.isPGroup'.to_le residual_R_le_sylow).comap_subtype) hgen
  have hz : primeRank 3 (A ⧸ B) = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hr := Theory.GroupTheory.primeRank_le_ker_add (p := 3) (QuotientGroup.mk' B)
  rw [QuotientGroup.ker_mk', hz, add_zero,
    primeRank_congr 3 (subgroupOfEquivOfLe (show D F ≤ A from le_sup_left))] at hr
  exact le_antisymm hr (primeRank_mono 3 (show D F ≤ Y L F from le_sup_left))

/-- The source group DR₁ has three-rank at most one. -/
theorem residual_Y_threeRank_le_one : primeRank 3 (Y L F) ≤ 1 := by
  rw [residual_Y_threeRank_eq_D]
  exact d.residual_D_threeRank_le_one

/-- Application to the literal Thompson subgroup J(DR₁). -/
theorem residual_thompson_threeRank_le_one : primeRank 3 (J L F) ≤ 1 :=
  (primeRank_mono 3 J_le_Y).trans d.residual_Y_threeRank_le_one

/-- The same bound for J(DR₁)R₁, the actual input to solvable Thompson
factorization and the W₀ argument. -/
theorem residual_thompsonJoin_threeRank_le_one : primeRank 3 (JR L F) ≤ 1 :=
  (primeRank_mono 3 JR_le_Y).trans d.residual_Y_threeRank_le_one

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
