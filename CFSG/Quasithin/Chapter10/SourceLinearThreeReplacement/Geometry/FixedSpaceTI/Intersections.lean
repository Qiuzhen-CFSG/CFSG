module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Residual
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import Theory.GroupTheory.PerfectCentralizerIntersection

/-!
# Outside-local intersections of the original linear-three moved factor

The actual SL₃(2) quotient is simple and has order divisible by three.
Cubic residual functoriality puts a conjugate component contained in M
inside L₀. The original point-centralizer residual then identifies it
with L, unless the point is fixed by L₀, when orbit rigidity suffices.
Conjugation by the specified Sylow exchange transfers the result from
the opposite factor back to [V,L].

The earlier component-normalizer bound remains explicit here; its producer
is half-Sylow uniqueness, not an A₅ model assumption.
Source: Aschbacher--Smith 10.2.10(1), printed p.753.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem three_dvd
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]
  decide

/-- Every conjugate linear-three component contained in M lies in its actual component
orbit; cubic residual functoriality discharges this source comparison. -/
theorem conjugate_component_le_orbit
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (g : G) (hg : L.map (MulAut.conj g).toMonoidHom ≤ D.maximalLocal) :
    L.map (MulAut.conj g).toMonoidHom ≤ localOrbit T L := by
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := e.isSimpleGroup
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
      pCore_isPGroup hp (three_dvd e), ← MonoidHom.range_eq_map, range_subtype]
  have hh := embedded_primeToResidual_mono 3 hg
  rwa [←map_embedded_primeToResidual 3 L (MulAut.conj g), hr,
    source_nonnormal_cubic_residual D hn (three_dvd e)] at hh

/-- A full-module subgroup fixed by L has trivial intersections with its
outside-M conjugates, given the genuine earlier centralizer bounds. -/
theorem fixed_factor_inf_conjugate_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (U : Subgroup G) (hUV : U ≤ D.fullModule)
    (hUL : U ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g : G} (hg : g ∉ D.maximalLocal) :
    U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ := by
  let := Chapter1.mem_L_isPerfect D.maximal.1
  apply inf_conjugate_eq_bot_of_perfect_centralizer_residual
    L (localOrbit T L) D.maximalLocal U hUL hcent
    (conjugate_component_le_orbit D e hn)
    (fun g hg => (source_nonnormal_orbit_le_conjugate_maximal_iff D hn
      (three_dvd e) g).mp hg) ?_ hNL hg
  intro u hu hnot
  exact point_centralizer_residual D e hn (hUV hu) (hUL hu) hnot

/-- The literal original moved factor satisfies source 10.2.10(1) once the
chosen opposite factor centralizes L and 10.2.6/10.2.9 are discharged. -/
theorem moved_inf_conjugate_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
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
  have hTI := fixed_factor_inf_conjugate_eq_bot D e hn U hUV hcross
    hcU hNL hnot
  apply eq_bot_iff.mpr
  rintro x ⟨hx,w,hw,rfl⟩
  have hmem : (MulAut.conj t) ((MulAut.conj g) w) ∈
      U ⊓ U.map (MulAut.conj (t * g * t⁻¹)).toMonoidHom := by
    refine ⟨mem_map_of_mem _ hx, (MulAut.conj t) w, mem_map_of_mem _ hw, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  rw [hTI,mem_bot] at hmem
  exact (MulAut.conj t).map_eq_one_iff.mp hmem

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
