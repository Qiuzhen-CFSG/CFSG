module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCongruence
public import Theory.SpecificGroups.PSL3Two.Parabolics.CubicSylowExclusion

/-!
# The original module in the collapsed-radical enlargement

The original parabolic radical survives in L₀/O₂(L₀): otherwise the
parabolic's two-residual would map to a three-group normalized by a full
Sylow in SL₃(2)². The concrete cubic exclusion kills this image, forcing
the original cubic complement into a two-group. The source centralizer
identity C_T(V)=O₂(L₀T) then shows that O₂(X) acts nontrivially on V_M.

Consequently the remaining collapse O₂(X) ≤ O₂(K) forces noncentral action
of both O₂(K) and O₂(E), for the literal E=<N_G(T₁),H>. Moreover
[O₂(K),P]=O₂(X) for the same cubic complement P. The central-core branch
therefore feeds the established residual-normalizer proof, and the final
consumer retains all original source guards on the noncentral case.

This does not exclude that remaining configuration. Its exclusion and both
final source contracts remain with qt-d-10-nona5-half-sylow-unique. Only
ModuleChoiceAt is external, finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

/-- The parabolic radical survives in the original orbit quotient. -/
theorem Data.residual_core_not_le_orbit_core (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) :
    ¬ (residual H).pCoreIn 2 ≤ (localOrbit T L).pCoreIn 2 := by
  intro hc
  let R := localOrbit T L
  let X := (residual H).subgroupOf R
  let q := QuotientGroup.mk' (pCore 2 R)
  obtain ⟨P,hi⟩ := h.exists_localInput
  have hPR : P ≤ R := hi.complement_le.trans h.residual_le_orbit
  have hCR : (residual H).pCoreIn 2 ≤ R := (pCoreIn_le 2 _).trans h.residual_le_orbit
  have hz : quotientImage R ((residual H).pCoreIn 2) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    intro x hx
    obtain ⟨y,hy,he⟩ := hc hx
    exact (Subtype.ext he : y=x) ▸ hy
  have he := congrArg (fun A : Subgroup G => A.subgroupOf R) hi.complement
  rw [subgroupOf_sup hCR hPR] at he
  have he' := congrArg (Subgroup.map q) he
  rw [Subgroup.map_sup] at he'
  change quotientImage R ((residual H).pCoreIn 2) ⊔ quotientImage R P = quotientImage R (residual H) at he'
  rw [hz,bot_sup_eq] at he'
  have hthree : IsPGroup 3 (quotientImage R (residual H)) :=
    he' ▸ (hi.odd_complement.isPGroup.comap_subtype.map q)
  have hperfect : IsPPerfect 2 (quotientImage R (residual H)) :=
    ((isPPerfect_embedded_pResidual 2 H).of_surjective
      (subgroupOfEquivOfLe h.residual_le_orbit).symm.toMonoidHom
      (subgroupOfEquivOfLe h.residual_le_orbit).symm.surjective).of_surjective
        (q.subgroupMap X) (q.subgroupMap_surjective X)
  have hRM : R ≤ D.maximalLocal := R.le_normalizer
  have hnormal : (R.subgroupOf D.maximalLocal).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨S,hS⟩ := InvariantThree.component_quotient_sylow
    (SourceLinearThreeReplacement.Overgroups.Closure.sylowIn_overgroup
      (le_normalizer_componentOrbit L T)) hRM hnormal
  obtain ⟨e⟩ := CentralHall.LinearThree.quotient_equiv D eL hn
  have hSX : (T : Subgroup G).subgroupOf R ≤ normalizer (X : Set R) := by
    rw [← subgroupOf_normalizer_eq h.residual_le_orbit]
    exact subgroupOf_mono R hi.invariant
  have hzero := Matrix.PSL3Two.pair_sylow_normalized_three_eq_bot e
    (quotientImage R (residual H)) S hthree hperfect (by
      rw [hS]
      exact (map_mono hSX).trans (le_normalizer_map q))
  have hXQ : residual H ≤ R.pCoreIn 2 := by
    have hk : X ≤ pCore 2 R := by
      have hh := (Subgroup.map_eq_bot_iff _).mp hzero
      rwa [QuotientGroup.ker_mk'] at hh
    intro x hx
    exact mem_map_of_mem R.subtype (hk (show (⟨x,h.residual_le_orbit hx⟩ : R) ∈ X from hx))
  have hp2 := (isPGroup_pCoreIn 2 R).to_le (hi.complement_le.trans hXQ)
  have hd := hi.odd_complement.isPGroup.disjoint_of_coprime hp2
    (by decide : Nat.Coprime 3 2)
  have hb : P = ⊥ := by simpa only [inf_idem] using hd.eq_bot
  apply hi.complement_not_cyclic
  rw [hb]
  infer_instance

/-- The original parabolic radical cannot centralize the full module. -/
theorem Data.residual_core_moves_fullModule (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D) :
    ¬ (residual H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
  obtain ⟨eL,_⟩ := hmodel
  intro hc
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  obtain ⟨P,hi⟩ := h.exists_localInput
  have hQ : (residual H).pCoreIn 2 ≤ (localJoin T L).pCoreIn 2 := by
    rw [← D.sylow_centralizer_module hu]
    exact le_inf hi.core_le_two_group
      (hc.trans (centralizer_le (le_componentOrbit D.moduleSubgroup D.maximalLocal)))
  exact h.residual_core_not_le_orbit_core hn eL
    ((le_inf ((pCoreIn_le 2 _).trans h.residual_le_orbit) hQ).trans
      (inf_pCoreIn_le_of_le 2 (show localOrbit T L ≤ localJoin T L from le_sup_left)))

/-- Collapse transfers the same noncentral action to the containing radical. -/
theorem Data.collapsed_core_moves_fullModule (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ¬ (enlargedResidual T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) :=
  fun hh => h.residual_core_moves_fullModule hn hmodel (hc.trans hh)

/-- The normal two-core of the actual enlargement also acts nontrivially. -/
theorem Data.collapsed_enlargement_core_moves_fullModule (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ¬ (enlargement T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
  apply fun hh => h.collapsed_core_moves_fullModule hn hmodel hc (?_)
  exact (pCoreIn_mono_of_normalizes h.enlargedResidual_le_enlargement
    (le_normalizer_conjugateSpanBy (residual H) (enlargement T L H))).trans hh

/-- The source collapse identifies the original radical with the movement
of the containing radical by the same cubic complement. -/
theorem Data.collapsed_core_commutator (h : Data D H) {P : Subgroup G}
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ⁅(enlargedResidual T L H).pCoreIn 2,P⁆ = (residual H).pCoreIn 2 := by
  have hQH : (enlargedResidual T L H).pCoreIn 2 ≤ H :=
    h.enlargedResidual_core_le_intersection.trans
      (inf_le_left.trans (inf_le_left.trans h.sylow_le))
  have hnorm : H ≤ normalizer ((enlargedResidual T L H).pCoreIn 2 : Set G) :=
    (le_sup_right.trans (le_normalizer_conjugateSpanBy _ _)).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply le_antisymm
  · have hle : ⁅(enlargedResidual T L H).pCoreIn 2,P⁆ ≤
        residual H ⊓ (enlargedResidual T L H).pCoreIn 2 :=
      le_inf ((commutator_mono le_rfl hi.complement_le).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hQH.trans (le_normalizer_embedded_pResidual 2 H))))
        (le_normalizer_iff_commutator_le_left.mp
          (hi.complement_le.trans ((map_subtype_le _).trans hnorm)))
    exact hle.trans (inf_pCoreIn_le_of_le 2 h.residual_le_enlargedResidual)
  · rw [hi.core_commutator]
    exact commutator_mono hc le_rfl


/-- In the small odd-prime rows, a containing radical centralizing the
original module cannot be the collapsed case. The established positive-image
and half-intersection arguments therefore normalize the original residual. -/
theorem Data.normalizes_residual_of_odd_small_core_centralizes (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D) {P I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hcentral : (enlargedResidual T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  by_cases hR : stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H
  · apply h.normalizes_residual_of_odd_small_full_positive hn hs hK hp ho hm hmod hR
    intro hc
    exact h.collapsed_core_moves_fullModule hn hmodel (h.quotient_core_eq_bot_iff.mp hc) hcentral
  · exact h.normalizes_residual_of_odd_small_half hn hs hK hp ho hm hmod hR

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original collapsed configuration forces noncentral action of both
actual normal two-cores on the original full module. -/
theorem SourceCubicNormalizerEnlargement.exists_noncentral_cores
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) (residual H) P
        (enlargement T L H) I ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
      (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
      (enlargement T L H).pCoreIn 2 ≠ ⊥ ∧
      residual H < enlargedResidual T L H ∧
      stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H ∧
      (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      ¬ (enlargedResidual T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) ∧
      (¬ (enlargement T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G)) ∧
      ⁅(enlargedResidual T L H).pCoreIn 2,P⁆ = (residual H).pCoreIn 2 := by
  obtain ⟨_,_,_,hn,_,hmodel,_,_,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,h24,hcore,hlt,hR,hc⟩ := hc
  exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,hmod,h24,hcore,hlt,hR,hc,
    h.collapsed_core_moves_fullModule hn hmodel hc,
    h.collapsed_enlargement_core_moves_fullModule hn hmodel hc,
    h.collapsed_core_commutator hs.toLocalInput hc⟩

/-- A failure of either original contract retains all source guards and
has a noncentral normal two-core on the original full module. This is
still a reduction; its remaining exclusion belongs to this source owner. -/
theorem sourceContracts_or_noncentralCubicNormalizerEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∀ H : Subgroup G, Data D H →
          (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 →
          (¬ (enlargedResidual T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G)) ∧
          (¬ (enlargement T L H).pCoreIn 2 ≤ centralizer (D.fullModule : Set G)) := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · right
    refine ⟨L,D,hc,?_⟩
    obtain ⟨_,_,_,hn,_,hmodel,_⟩ := hc
    intro H h hcollapse
    exact ⟨h.collapsed_core_moves_fullModule hn hmodel hcollapse,
      h.collapsed_enlargement_core_moves_fullModule hn hmodel hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
