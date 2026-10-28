module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.ComponentLocalization
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Source

/-!
# Outside intersections and uniform fixed spaces in the cubic rows

The actual cubic residual puts a conjugate component contained in M inside
L₀. Component localization at a common moved point then identifies that
conjugate with the fixed factor. Component-normalizer control excludes an
outside conjugator. The same residual supplies orbit rigidity.

The applications discharge both intersection fields in the original uniform
fixed-space argument. The component-normalizer bound remains the earlier
10.2.6 input; divisibility by three specifies the rows proved here.
Source: Aschbacher--Smith 10.1.3 and10.2.10--12, printed pp.742,753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Cubic residual functoriality places every contained conjugate component in the orbit. -/
theorem conjugate_component_le_orbit_of_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (g : G) (hg : L.map (MulAut.conj g).toMonoidHom ≤ D.maximalLocal) :
    L.map (MulAut.conj g).toMonoidHom ≤ localOrbit T L := by
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let := quotient_simple D hn
  have hp : IsPPerfect 2 L := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (L ⧸ N) := by
      by_contra! hne
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have hr : (primeToResidual 3 L).map L.subtype = L := by
    rw [primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 L)
      pCore_isPGroup hp hd, ← MonoidHom.range_eq_map, range_subtype]
  have hh := embedded_primeToResidual_mono 3 hg
  rwa [←map_embedded_primeToResidual 3 L (MulAut.conj g), hr,
    source_nonnormal_cubic_residual D hn hd] at hh

/-- Outside intersections use same-component localization rather than solvability of all proper subgroups. -/
theorem fixed_factor_inf_conjugate_eq_bot_of_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (U : Subgroup G) (hUV : U ≤ D.fullModule)
    (hUL : U ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal) :
    U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro v ⟨hv,u,hu,rfl⟩
  by_cases hu1 : u = 1
  · simp [hu1]
  have hv1 : (MulAut.conj g) u ≠ 1 :=
    fun he => hu1 ((MulAut.conj g).map_eq_one_iff.mp he)
  let C := centralizer ({(MulAut.conj g) u} : Set G)
  have hCM : C ≤ D.maximalLocal := hcent _ hv hv1
  have hCMg : C ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
    rw [show C = (centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom from
      (CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) u).symm]
    exact map_mono (hcent u hu hu1)
  by_cases hvR : (MulAut.conj g) u ∈ centralizer (localOrbit T L : Set G)
  · exact (hg ((source_nonnormal_orbit_le_conjugate_maximal_iff D hn hd g).mp
      ((show localOrbit T L ≤ C from fun r hr =>
        mem_centralizer_singleton_iff.mpr (hvR r hr)).trans hCMg))).elim
  let A := L.map (MulAut.conj g).toMonoidHom
  have hAC : A ≤ C := by
    rintro x ⟨l,hl,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) (hUL hu l hl)
  have hAR : A ≤ localOrbit T L :=
    conjugate_component_le_orbit_of_three D hn hd g (hAC.trans hCM)
  have hAL : A ≤ L := isomorphic_component_point_le D hn (hUV hv) (hUL hv) hvR A
    ((MulAut.conj g).subgroupMap L).symm hAR hAC
  have he : A = L := eq_of_le_of_card_ge hAL
    (Nat.card_congr ((MulAut.conj g).subgroupMap L).toEquiv).le
  exact (hg (hNL (mem_normalizer_iff_map_conj_eq.mpr he))).elim

/-- The actual moved factor has trivial intersections outside M in every cubic row. -/
theorem moved_inf_conjugate_eq_bot_of_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (t : G) (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 →
      centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  let M := D.maximalLocal
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  have htM : t ∈ M := (le_normalizer_componentOrbit L T) ht
  have hMM : M.map (MulAut.conj t).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer htM)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hUV : U ≤ D.fullModule := by
    have hmV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule htM)
    exact (map_mono hWV).trans_eq hmV
  have hcU : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M := by
    rintro u ⟨w,hw,rfl⟩ hne
    have hwne : w ≠ 1 := fun he => hne (by simp [he])
    change centralizer ({(MulAut.conj t) w} : Set G) ≤ M
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj t) w]
    exact (map_mono (hcent w hw hwne)).trans_eq hMM
  have hnot : t * g * t⁻¹ ∉ M := by
    intro hh
    apply hg
    simpa [mul_assoc] using M.mul_mem (M.mul_mem (M.inv_mem htM) hh) htM
  have hTI := fixed_factor_inf_conjugate_eq_bot_of_three D hn hd U hUV hcross hcU hNL hnot
  apply eq_bot_iff.mpr
  rintro x ⟨hx,w,hw,rfl⟩
  have hmem : (MulAut.conj t) ((MulAut.conj g) w) ∈
      U ⊓ U.map (MulAut.conj (t * g * t⁻¹)).toMonoidHom := by
    refine ⟨mem_map_of_mem _ hx, (MulAut.conj t) w, mem_map_of_mem _ hw, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  rw [hTI,mem_bot] at hmem
  exact (MulAut.conj t).map_eq_one_iff.mp hmem

/-- Both exact intersection inputs are proved in every cubic row. -/
theorem intersectionInputs_of_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : IntersectionInputs D := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  exact ⟨fun _ hx => moved_inf_conjugate_eq_bot_of_three D c.nonnormal hd t ht
    (c.crossed t ht htn) c.pointCentralizers hNL hx,
    fun x hx => (source_nonnormal_orbit_le_conjugate_maximal_iff D c.nonnormal hd x).mp hx⟩

/-- The original normalization and uniform fixed-space identities follow,
with the earlier component-normalizer bound displayed. -/
theorem fixedSpaceGeometry_of_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (c : Context D)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : FixedSpaceGeometry D :=
  fixedSpaceGeometry_of_source_inputs D c (source_actionInputs D c)
    (intersectionInputs_of_three D c hd hNL)

/-- The cubic-row large-module exclusion consumes the actual original offender. -/
theorem large_module_false_of_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (b : LargeModuleBounds D)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  let ctx : Context D := ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,
    b.crossed,b.fixed_size_gt_eight⟩
  exact b.false_of_configuration c (fixedSpaceGeometry_of_three D ctx hd hNL)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
