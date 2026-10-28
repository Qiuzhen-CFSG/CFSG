module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.LocalReduction.ZeroCorank
public import CFSG.Quasithin.ChapterE.Section03.Parameters.RankKernel
public import Theory.GroupTheory.FixedSupplementCentralizer
public import CFSG.Quasithin.ChapterI.Section06To08.Basic

/-!
# Vanishing of the fixed part at natural corank one

A nonzero central kernel makes the moved factor have at least sixteen
points. Its corank-one intersection therefore has more than four points;
the full automizer's two-rank bound forces a nonidentity action kernel.
Point control then puts W in Mᵍ. Applying the same argument after a literal
M-alignment puts the other factor there, contradicting reverse escape.
The two crossed factors now give vanishing of C_V(L₀) and global TI.

Only the preceding component-normalizer bound remains explicit. No later
survivor, weak-closure equality w=2, or centralizer-core theorem is used.
Source: Aschbacher--Smith 10.2.10(2), 10.2.12, printed pp.753,755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

omit [Finite G] in
private theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a*b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
  Subgroup.conjBy_mul H a b

/-- Left alignment inside M preserves the exact attained offender. -/
theorem configuration_left_mul (c : Configuration T D g)
    {a : G} (ha : a ∈ D.maximalLocal) : Configuration T D (a * g) := by
  let V := D.fullModule
  let M := D.maximalLocal
  have hV : V.map (MulAut.conj a).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule ha)
  have hM : M.map (MulAut.conj a).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer ha)
  have hI : (V.map (MulAut.conj g).toMonoidHom ⊓ M).map
      (MulAut.conj a).toMonoidHom = V.map (MulAut.conj (a*g)).toMonoidHom ⊓ M := by
    rw [map_inf _ _ _ (MulAut.conj a).injective,←map_conj_mul,hM]
  have hcor : subgroupCorank (V.map (MulAut.conj (a*g)).toMonoidHom)
      (V.map (MulAut.conj (a*g)).toMonoidHom ⊓ M) =
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ M) := by
    rw [←hI,map_conj_mul,subgroupCorank,
      relIndex_map_map_of_injective _ _ (MulAut.conj a).injective]
    rfl
  refine ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,
    fun h => c.outside ((M.mul_mem_cancel_left ha).mp h),?_,?_,?_⟩
  · intro hc
    have hm : (⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map
        (MulAut.conj a).toMonoidHom = ⊥ := by
      rw [map_commutator,hV,←map_conj_mul]
      exact hc
    exact c.noncommuting ((map_eq_bot_iff_of_injective _ (MulAut.conj a).injective).mp hm)
  · change globalW V (T : Subgroup G) = _
    rw [hcor]
    exact c.attained
  · change subgroupCorank (V.map (MulAut.conj (a*g)).toMonoidHom)
      (V.map (MulAut.conj (a*g)).toMonoidHom ⊓ M) ≤ 2
    rw [hcor]
    exact c.small

/-- A nonzero natural central kernel makes the corank-one offender large
enough to have a nonidentity kernel on W; hence W lies in Mᵍ. -/
theorem moved_le_conjugate_of_fixed_ne_bot
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) ≠ ⊥) :
    ⁅D.fullModule,L⁆ ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := offender_elementary_of_le (show A ≤ P from inf_le_left)
  have hZ := (W ⊓ centralizer (L : Set G)).one_lt_card_iff_ne_bot.mpr hz
  have hcard := m.natural.card_section
  simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod] at hcard
  change Nat.card W = 8 * Nat.card (W ⊓ centralizer (L : Set G) : Subgroup G) at hcard
  have hW : 16 ≤ Nat.card W := by omega
  have hP : Nat.card P = Nat.card W :=
    (Nat.card_congr ((MulAut.conj g).subgroupMap W).toEquiv).symm
  have hi : A.relIndex P ≤ 2 := Recognition.moved_intersection_index_le D hsmall
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) A P bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at hm
  have hA : 2 ^ 2 < Nat.card A := by
    have hh := Nat.mul_le_mul_left (Nat.card A) hi
    rw [hm,hP] at hh
    omega
  have hAN := (natural_offender_geometry c m hsmall
    (natural_outside_intersection c m hNL c.outside)).1
  obtain ⟨a,ha,hane,hac⟩ := exists_nontrivial_centralizer_of_local_rank A W D.maximalLocal
    (le_inf inf_le_right hAN) (local_primeRank_le_two m c.nonnormal) hA
  obtain ⟨w,hw,rfl⟩ := ha.1
  have hwne : w ≠ 1 := fun he => hane (by simp [he])
  have hc : centralizer ({(MulAut.conj g) w} : Set G) ≤
      D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) w]
    exact map_mono (c.pointCentralizers w hw hwne)
  exact (show W ≤ centralizer ({(MulAut.conj g) w} : Set G) from
    fun v hv => mem_centralizer_singleton_iff.mpr (hac v hv)).trans hc

/-- The central kernel of the original moved natural section vanishes at
corank at most one. The two literal M-alignments are retained. -/
theorem moved_fixed_eq_bot_of_small_corank
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hz
  obtain ⟨hone,hescape⟩ := natural_corank_one_and_reverse_escape c m hNL hsmall
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  have htM := le_normalizer_componentOrbit L T ht
  have h₁ := moved_le_conjugate_of_fixed_ne_bot c m hNL hsmall hz
  let c' := configuration_left_mul c (D.maximalLocal.inv_mem htM)
  have hsmall' : subgroupCorank (D.fullModule.map (MulAut.conj (t⁻¹*g)).toMonoidHom)
      (D.fullModule.map (MulAut.conj (t⁻¹*g)).toMonoidHom ⊓ D.maximalLocal) ≤ 1 := by
    have he := c'.attained.symm.trans c.attained
    have hh : subgroupCorank (D.fullModule.map (MulAut.conj (t⁻¹*g)).toMonoidHom)
      (D.fullModule.map (MulAut.conj (t⁻¹*g)).toMonoidHom ⊓ D.maximalLocal) =
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by exact_mod_cast he
    exact hh ▸ hsmall
  have h₂ := map_mono (f := (MulAut.conj t).toMonoidHom)
    (moved_le_conjugate_of_fixed_ne_bot c' m hNL hsmall' hz)
  rw [←map_conj_mul,mul_inv_cancel_left] at h₂
  apply hescape
  rw [source_nonnormal_fullModule_eq_moved_pair D c.nonnormal ht (m.crossed t ht htn)]
  exact sup_le h₁ h₂

/-- Vanishing of C_W(L) and crossed factor generation give C_V(L₀)=1. -/
theorem full_fixed_eq_bot_of_moved_fixed_eq_bot
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  let W := ⁅D.fullModule,L⁆
  let B := W.map (MulAut.conj t).toMonoidHom
  let F := D.fullModule ⊓ centralizer (localOrbit T L : Set G)
  have hgen := source_nonnormal_fullModule_eq_moved_pair D hn ht (m.crossed t ht htn)
  have hWV : W ≤ D.fullModule := le_sup_left.trans_eq hgen.symm
  have hBV : B ≤ D.fullModule := le_sup_right.trans_eq hgen.symm
  let : IsElementaryAbelian 2 D.fullModule := m.full_eq_local.symm ▸ D.module_elementary
  have hBW : B ≤ normalizer (W : Set G) :=
    ((hBV.trans D.fullModule.le_centralizer).trans (centralizer_le hWV)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hfixed : D.fullModule ⊓ centralizer (L : Set G) = B := by
    rw [hgen,sup_comm,inf_centralizer_sup_of_centralizing B W L hBW (m.crossed t ht htn),
      hz,sup_bot_eq]
  have hFB : F ≤ B :=
    (inf_le_inf_left _ (centralizer_le (le_componentOrbit L T))).trans_eq hfixed
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
      ((le_normalizer_componentOrbit L T).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  apply bot_unique
  intro x hx
  have htx : (MulAut.conj t) x ∈ F := by
    rw [←mem_normalizer_iff_map_conj_eq.mp (hTF ht)]
    exact mem_map_of_mem _ hx
  obtain ⟨w,hw,heq⟩ := hFB htx
  have hwx : w = x := (MulAut.conj t).injective heq
  exact hz.le ⟨hwx ▸ hw,(centralizer_le (le_componentOrbit L T)) hx.2⟩

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
