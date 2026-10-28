module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CoreStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CentralOrbitQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.PResidual.RelativeCoreCommutator

/-!
# The original nonbinary MS action and critical geometry

Relative normality and MS2(a) identify the original component as the
two-residual. The intrinsic and ambient core commutators agree. On the
normal closure of Ω₁(Z(R)), the radical centralizer is exactly the ambient
two-core. This uses quasisimplicity and retains a possible odd covering
kernel in the full action, as required for SL₃(4).

MS3 then supplies an FF offender on the literal central-omega action
through its centralizer quotient. The actual free holomorph amalgam has
positive even critical distance, and the radical-centralizer identity
transports to every edge. The characteristic replacement preserves the
same original commutator core.

These are the initial hypotheses for the later marked module classification;
no C.1.34 module alternative is asserted here. Source: MS93 (2.0)--(2.2),
the opening of (3.2), and Section 7, printed pp.854--857,863,932--933;
Aschbacher--Smith C.1.31--34, printed pp.135--137.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open MSCentralOrbit
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "T" => R.subgroupOf (K ⊔ R)

include h hn

/-- The original relative component is the two-residual of the join. -/
theorem residual_eq : pResidual 2 J = L :=
  component_eq_residual L T h.component.2 (join_oddIndex h hn).isPGroup (join_product h hn)

/-- Two-perfectness transported to the original component carrier. -/
theorem component_twoPerfect : IsPPerfect 2 K := by
  have hp : IsPPerfect 2 L := by
    rw [←residual_eq h hn]
    exact isPPerfect_pResidual 2
  exact hp.of_surjective (subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)).toMonoidHom
    (subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)).surjective

/-- The actual C.1.34 core is the intrinsic component-core commutator. -/
theorem msQ_eq_intrinsic : msQ K R = ⁅K.pCoreIn 2,K⁆ :=
  commutator_pCoreIn_eq_intrinsic_of_subnormal K (K ⊔ R) le_sup_left
    h.component.2.subnormal (component_twoPerfect h hn)

omit h hn [Finite G] [Finite F] in
/-- The literal join inclusion maps its commutator to the original msQ. -/
theorem commutator_map_eq_msQ :
    (⁅pCore 2 J,L⁆).map (J).subtype = msQ K R := by
  rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ R from le_sup_left)]
  rfl

omit hn in
/-- The given generalized-Fitting equality supplies characteristic two. -/
theorem core_selfCentralizing : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
  simpa only [h.fitting] using centralizer_generalizedFitting_le J

/-- The radical is nontrivial, since the join contains a C-component. -/
theorem radical_ne_bot : T ≠ ⊥ := by
  intro hr
  have hq : pCore 2 J = ⊥ := le_bot_iff.mp (hr ▸ (join_oddIndex h hn).twoCore_le)
  have ht : (⊤ : Subgroup J) ≤ ⊥ := by
    intro x _
    have hx : x ∈ centralizer (pCore 2 J : Set J) := by
      rw [hq]
      intro y hy
      have hy' : y = 1 := hy
      simp only [hy',one_mul,mul_one]
    exact hq ▸ core_selfCentralizing h hx
  exact h.component.2.ne_bot (le_bot_iff.mp (le_top.trans ht))

omit hn [Finite G] in
/-- The quotient remains quasisimple after restriction to the join. -/
theorem join_quotient_quasisimple : IsQuasisimple (L ⧸ pCore 2 L) := by
  let := quotient_quasisimple h
  exact IsQuasisimple.of_mulEquiv
    (RankTwo.NonbinarySymplectic.subgroupOfCoreQuotientEquiv
      (show K ≤ K ⊔ R from le_sup_left)).symm

/-- The exact radical kernel, without imposing a centerless full quotient. -/
theorem omegaOrbit_radical_kernel :
    T ⊓ centralizer (omegaOrbit T : Set J) = pCore 2 J := by
  let := component_normal h hn
  let := join_quotient_quasisimple h
  exact omegaOrbit_radical_centralizer L T h.component.2
    (join_oddIndex h hn).isPGroup (radical_ne_bot h hn) (join_oddIndex h hn).twoCore_le
    (core_selfCentralizing h) (join_product h hn) (join_characteristic h)

/-- The genuine FF module on the actual centralizer quotient of the omega layer. -/
theorem centralOmega_isFF :
    Representation.BinaryOffender.IsFFModule
      (Representation.NormalElementaryQuotient.representation
        (Subgroup.omegaCenterIn (pCore 2 J))
        (QuotientGroup.mk' (centralizer (Subgroup.omegaCenterIn (pCore 2 J) : Set J)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) := by
  let := component_normal h hn
  let := join_quotient_quasisimple h
  apply layer_isFFModule L T (Subgroup.omegaCenterIn (pCore 2 J)) h.component.2
    (join_oddIndex h hn).isPGroup (radical_ne_bot h hn) (join_oddIndex h hn).twoCore_le
    (core_selfCentralizing h) (join_product h hn) (join_characteristic h)
    (omegaOrbit_le_centralOmega T (join_oddIndex h hn).twoCore_le (core_selfCentralizing h))
  intro x hx
  exact (join_oddIndex h hn).twoCore_le ((mem_omegaCenterIn_iff _ _).mp hx).1

open Stellmacher.PushingUp.AmalgamGraph BinaryMS.MS93

/-- The original holomorph geometry has positive even critical distance. -/
theorem positive_even_geometry : ∃ g : Geometry T, 0 < g.b T ∧ Even (g.b T) := by
  let hp := (join_oddIndex h hn).isPGroup
  let hQR := (join_oddIndex h hn).twoCore_le
  let g := geometry T hp (radical_ne_bot h hn) (join_characteristic h)
  refine ⟨g,?_,g.even (alpha T) rfl⟩
  have hZ : Z T (alpha T) ≤ Q T (alpha T) := by
    rw [Z_alpha_eq_omegaOrbit, Q_alpha T hp hQR]
    apply map_mono
    exact (omegaOrbit_le_centralOmega T hQR (core_selfCentralizing h)).trans
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1)
  obtain ⟨a,hc⟩ := criticalPair_exists T (alpha T) (g.exists_critical (alpha T) rfl)
  by_contra! hz
  have hd : (cosetGraph T).dist (alpha T) a = 0 := by
    rw [hc.1]
    exact Nat.eq_zero_of_le_zero hz
  have heq := (cosetGraph_connected T).dist_eq_zero_iff.mp hd
  exact hc.2 (heq ▸ hZ)

/-- The graph core pulls back through its actual embedding to the original msQ. -/
theorem graph_core_pullback :
    ((core T (alpha T)).comap (embedM T)).map (J).subtype = msQ K R := by
  rw [core_alpha T (join_oddIndex h hn).isPGroup (join_oddIndex h hn).twoCore_le
    (residual_eq h hn),comap_map_eq_self_of_injective (embedM_injective T)]
  exact commutator_map_eq_msQ

/-- The Section 7 replacement preserves the original ambient commutator core. -/
theorem characteristic_replacement :
    ∃ d : CharacteristicReduction L T,
      d.overgroup.Normal ∧ MSCharacteristicCondition d.radical ∧
      pCore 2 d.overgroup ≤ d.radical ∧
      ((⁅pCore 2 d.overgroup,(L).subgroupOf d.overgroup⁆).map
        d.overgroup.subtype).map (J).subtype = msQ K R := by
  obtain ⟨d,hd,hm,hc,hq⟩ := component_characteristic_reduction L T h.component.2
    (join_oddIndex h hn).isPGroup (join_product h hn)
    (join_oddIndex h hn).twoCore_le (join_characteristic h)
  refine ⟨d,hd,hm,hc,?_⟩
  let := component_normal h hn
  have hp : IsPPerfect 2 L := by
    rw [←residual_eq h hn]
    exact isPPerfect_pResidual 2
  have he : (blockU L).map (L).subtype = ⁅pCore 2 J,L⁆ :=
    (commutatorCore_eq_intrinsic L hp).symm
  rw [hq,he]
  exact commutator_map_eq_msQ

/-- Source (2.2) centralizer control at every edge of the actual amalgam. -/
theorem edge_centralizer : EdgeCentralizerCondition T := by
  let hp := (join_oddIndex h hn).isPGroup
  let hQR := (join_oddIndex h hn).twoCore_le
  have hb : Q T (beta T) ⊓ centralizer (Z T (alpha T) : Set (FreeAmalgam T)) =
      Q T (alpha T) := by
    rw [Q_beta, Q_alpha T hp hQR, Z_alpha_eq_omegaOrbit]
    apply le_antisymm
    · rintro x ⟨⟨r,hr,rfl⟩,hx⟩
      apply mem_map_of_mem
      apply (omegaOrbit_radical_kernel h hn).le
      refine ⟨hr,?_⟩
      intro w hw
      apply embedM_injective T
      simpa only [map_mul] using hx (embedM T w) (mem_map_of_mem _ hw)
    · rintro x ⟨q,hq,rfl⟩
      refine ⟨mem_map_of_mem _ (hQR hq),?_⟩
      rintro w ⟨z,hz,rfl⟩
      have he : z*q=q*z := (((mem_omegaCenterIn_iff _ _).mp
        (omegaOrbit_le_centralOmega T hQR (core_selfCentralizing h) hz)).2.1 q hq).symm
      simpa only [map_mul] using congrArg (embedM T) he
  intro a t ha hat
  obtain ⟨g,hh|hh⟩ := (adjacent_iff_exists_common T a t).mp hat
  · rcases hh with ⟨rfl,rfl⟩
    have ha0 : act T g (alpha T) = mVertex T g := by simp [alpha]
    have ht0 : act T g (beta T) = hVertex T g := by simp [beta]
    rw [←ha0,←ht0,Q_act,Z_act,Q_act]
    have hm := congrArg (fun U : Subgroup (FreeAmalgam T) =>
      U.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,map_centralizer_equiv] at hm
    exact hm
  · rcases hh with ⟨rfl,rfl⟩
    cases ha

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
