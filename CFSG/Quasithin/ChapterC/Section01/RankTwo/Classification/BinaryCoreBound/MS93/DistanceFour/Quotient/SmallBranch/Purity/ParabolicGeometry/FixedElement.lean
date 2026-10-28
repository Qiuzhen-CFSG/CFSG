module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry.Star
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.ElementaryAbelianAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.Representation.HigherFieldBorelFixedSpaces.Extension

/-!
# Transferring a fixed starred vector to the actual core quotient

The literal conjugation action on VStar/Z is a finite binary module. Its
invariants vanish by the starred-intersection identity. The square obstruction
on the supplied core module also proves core intersect Z = U, so the image of
the core in VStar/Z is exactly core/U, with no additional fixed kernel.

Suppose that this image has no nonzero fixed vector for the selected ordered
residual. Every local displacement lies in the core image. Relative normality
of the residual in its parabolic then makes every residual-fixed starred vector
parabolic-fixed. Averaging over the seven parabolic cosets makes it globally
fixed, contradicting the nonzero fixed vector supplied by the edge star.

All quotients and actions are constructed from ambient conjugation. The marking
of the supplied CoreModule and ModuleQuotient is retained. No midpoint facts,
parabolic recognition or purity assumption is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.10)--(4.6.11), printed pp.908--909, especially the use of (1.4)
on the starred quotient at the beginning of the proof of (4.6.11).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

/-- The finite binary starred quotient, with its genuine local conjugation action. -/
structure StarModule (R : Subgroup M) (geometry : Geometry R) where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) M Space
  projection : VStar R geometry (alpha R) (beta R) →* Multiplicative Space
  onto : Function.Surjective projection
  kernel : projection.ker = (Z R (alpha R)).subgroupOf
    (VStar R geometry (alpha R) (beta R))
  action : ∀ (m : M) (x y : VStar R geometry (alpha R) (beta R)),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (projection y).toAdd = representation m (projection x).toAdd
attribute [instance] StarModule.addCommGroup StarModule.module StarModule.finite

omit [Finite M] in
include radius in
private theorem star_square_mem_Z (x : VStar R geometry (alpha R) (beta R)) :
    (x : FreeAmalgam R) ^ 2 ∈ Z R (alpha R) := by
  apply DistanceEight.U_le_Z R (alpha R)
  let P := V R (alpha R)
  let f : P →* Abelianization P := (powMonoidHom 2).comp Abelianization.of
  have hle : P ≤ f.ker.map P.subtype := by
    change VBall R (alpha R) 2 ≤ _
    conv_lhs => rw [← DistanceEight.VBall_omegaOne R (alpha R) 2]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro y hy hy2
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    change (Abelianization.of (⟨y, hy⟩ : P)) ^ 2 = 1
    rw [← map_pow, show (⟨y, hy⟩ : P) ^ 2 = 1 from Subtype.ext hy2, map_one]
  obtain ⟨y, hy, he⟩ := hle (Flags.star_le_radius geometry _ _ x.property)
  change (y : FreeAmalgam R) = x at he
  have hpow : y ^ 2 ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    change Abelianization.of (y ^ 2) = 1
    rw [map_pow]
    exact hy
  have hh := mem_map_of_mem P.subtype hpow
  rw [← radius.radius_derived (alpha R) rfl]
  simpa only [_root_.commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype,
    subtype_apply, coe_pow, he] using hh

include common radius in
/-- Construct VStar/Z and the action of the original local group on that quotient. -/
theorem exists_starModule : Nonempty (StarModule R geometry) := by
  let S := VStar R geometry (alpha R) (beta R)
  let N := (Z R (alpha R)).subgroupOf S
  have hSP : S ≤ stabilizer R (alpha R) :=
    (Flags.star_le_radius geometry _ _).trans (geometry.V_local _ rfl common.large_distance)
  have hSZ : S ≤ normalizer (Z R (alpha R)) := hSP.trans (Z_normalized R _)
  let : N.Normal := ⟨by
    intro x hx g
    exact (mem_normalizer_iff.mp (hSZ g.property) x).mp hx⟩
  let D := S ⧸ N
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite S := Finite.of_injective (inclusion hSP) (inclusion_injective hSP)
  have hderived : _root_.commutator S ≤ N := by
    intro x hx
    have hh := mem_map_of_mem S.subtype hx
    rw [map_subtype_commutator] at hh
    apply DistanceEight.U_le_Z R (alpha R)
    rw [← radius.radius_derived (alpha R) rfl]
    exact commutator_mono (Flags.star_le_radius geometry _ _)
      (Flags.star_le_radius geometry _ _) hh
  let : IsMulCommutative D := Normal.quotient_commutative_iff_commutator_le.mpr hderived
  let : IsElementaryAbelian 2 D := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact star_square_mem_Z geometry radius y }
  have hPS : Mbar R ≤ normalizer S := by
    rw [← stabilizer_m_base R]
    exact Flags.star_normalized geometry _ _
  have hPZ : Mbar R ≤ normalizer (Z R (alpha R)) := by
    rw [← stabilizer_m_base R]
    exact Z_normalized R _
  obtain ⟨a, ha⟩ := exists_quotient_conjugation_action (Mbar R) S
    (Z R (alpha R)) hPS hPZ inferInstance
  let ι : M →* Mbar R := (embedM R).rangeRestrict
  let aM : M →* MulAut D := a.comp ι
  let : MulDistribMulAction M D := MulDistribMulAction.compHom D aM
  let ρ : Representation (ZMod 2) M (Additive D) := ofElementaryAbelianAction
  let p : S →* Multiplicative (Additive D) :=
    (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom.comp (QuotientGroup.mk' N)
  refine ⟨{
    Space := Additive D
    representation := ρ
    projection := p
    onto := (MulEquiv.multiplicativeAdditive (H := D)).symm.surjective.comp
      (QuotientGroup.mk'_surjective N)
    kernel := ?_
    action := ?_ }⟩
  · exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N)
      (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom
      (MulEquiv.multiplicativeAdditive (H := D)).symm.injective).trans
        (QuotientGroup.ker_mk' N)
  · intro m x y hy
    change QuotientGroup.mk' N y = aM m (QuotientGroup.mk' N x)
    rw [show aM m = a (ι m) from rfl, ha]
    congr 1
    exact Subtype.ext hy

private theorem mem_preimage_iff {G : Type*} [Group G]
    (Q E Z : Subgroup G) (hn : Q ≤ normalizer Z) (x : G) :
    x ∈ commutatorPreimage Q E Z ↔ x ∈ Q ∧ ∀ e ∈ E, ⁅e, x⁆ ∈ Z := by
  constructor
  · intro hx
    refine ⟨commutatorPreimage_le _ _ _ hx, ?_⟩
    intro e he
    have hc := commutator_commutatorPreimage_le Q E Z hn
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator he hx)
  · rintro ⟨hx, hc⟩
    let K : Subgroup G := {
      carrier := {z | z ∈ Q ∧ ∀ e ∈ E, ⁅z, e⁆ ∈ Z}
      one_mem' := ⟨Q.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
        refine ⟨Q.mul_mem ha hb, ?_⟩
        intro e he
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact Z.mul_mem (le_normalizer_iff.mp hn a ha _ (hcb e he)) (hca e he)
      inv_mem' := by
        rintro a ⟨ha, hca⟩
        refine ⟨Q.inv_mem ha, ?_⟩
        intro e he
        rw [commutatorElement_inv_left]
        have hh : ⁅e, a⁆ ∈ Z := by
          rw [← commutatorElement_inv]
          exact Z.inv_mem (hca e he)
        simpa only [inv_inv] using le_normalizer_iff.mp hn a⁻¹ (Q.inv_mem ha) _ hh }
    apply (le_commutatorPreimage (show K ≤ Q from fun _ hy => hy.1)
      (commutator_le.mpr fun _ hy => hy.2))
    refine ⟨hx, fun e he => ?_⟩
    rw [← commutatorElement_inv]
    exact Z.inv_mem (hc e he)

include common in
private theorem Z_commutator_le_U :
    ⁅Z R (alpha R), stabilizer R (alpha R)⁆ ≤ U R (alpha R) := by
  let naturalData : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have hsplit := naturalData.decomposition_at (alpha R) rfl
  have hh := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans hsplit.symm) inf_le_right
    ((DistanceEight.U_le_Z R _).trans ((Z_le_stabilizer R _).trans
      (stabilizer R (alpha R)).le_normalizer))
  rw [commutator_comm, ← hh]
  exact le_normalizer_iff_commutator_le_right.mp (U_normalized (alpha R))

include common radius in
/-- The square obstruction removes the kernel of the core image in the starred quotient. -/
theorem core_inter_Z_eq_U (d : CoreModule source) (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m) :
    core R (alpha R) ⊓ Z R (alpha R) = U R (alpha R) := by
  apply le_antisymm
  · intro x hx
    let c : core R (alpha R) := ⟨x, hx.1⟩
    have hfix : (d.projection c).toAdd ∈ fixedSpace d.representation ⊤ := by
      intro g
      obtain ⟨a, ha⟩ := source.projection_surjective g.val
      let y := coreAction (R := R) a c
      have he : y * c⁻¹ ∈ d.projection.ker := by
        rw [d.kernel]
        change ⁅embedM R a, x⁆ ∈ U R (alpha R)
        have hc := Z_commutator_le_U source geometry common
        rw [commutator_comm] at hc
        apply hc (commutator_mem_commutator _ hx.2)
        rw [alpha, stabilizer_m_base]
        exact ⟨a, rfl⟩
      have hp : d.projection y = d.projection c := by
        change d.projection (y * c⁻¹) = 1 at he
        rwa [map_mul, map_inv, mul_inv_eq_one] at he
      change d.representation g.val _ = _
      rw [← ha, ← d.action a c y rfl, hp]
    rw [no_fixed source geometry common radius d m q] at hfix
    have hk : c ∈ d.projection.ker := Multiplicative.toAdd.injective hfix
    rwa [d.kernel] at hk
  · exact le_inf (U_le_core source geometry common) (DistanceEight.U_le_Z R _)

include common radius in
private theorem star_commutator_local_le_core :
    ⁅VStar R geometry (alpha R) (beta R), stabilizer R (alpha R)⁆ ≤ core R (alpha R) := by
  let S := VStar R geometry (alpha R) (beta R)
  have hL : Ltilde R (alpha R) ≤ stabilizer R (alpha R) := map_subtype_le _
  have hQ : Q R (alpha R) ≤ stabilizer R (alpha R) := fun _ hx => hx.1
  have hSC : ⁅S, Ltilde R (alpha R)⁆ ≤ core R (alpha R) :=
    commutator_mono ((Flags.star_le_radius geometry _ _).trans
      (Flags.V_le_Q geometry common.large_distance _ rfl)) le_rfl
  have hpre : stabilizer R (alpha R) ≤
      commutatorPreimage (stabilizer R (alpha R)) S (core R (alpha R)) := by
    conv_lhs => rw [← source.local_generation (alpha R) rfl]
    apply sup_le
    · exact le_commutatorPreimage hL (by rwa [commutator_comm])
    · apply le_commutatorPreimage hQ
      rw [commutator_comm]
      exact (radius.star_commutator (alpha R) (beta R) rfl (base_adjacent R)).le.trans
        (U_le_core source geometry common)
  rw [commutator_comm]
  apply (commutator_mono hpre le_rfl).trans
  apply commutator_commutatorPreimage_le
  simpa only [alpha, stabilizer_m_base] using (core_normalized (R := R))

variable (a : StarModule R geometry)

private def starConjugate (m : M) (x : VStar R geometry (alpha R) (beta R)) :
    VStar R geometry (alpha R) (beta R) :=
  ⟨embedM R m * x * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp (Flags.star_normalized geometry _ _ (by
      rw [alpha, stabilizer_m_base]; exact ⟨m, rfl⟩)) x).mp x.property⟩

omit [Finite M] in
private theorem star_fixed_iff (m : M) (x : VStar R geometry (alpha R) (beta R)) :
    a.representation m (a.projection x).toAdd = (a.projection x).toAdd ↔
      ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ Z R (alpha R) := by
  let y := starConjugate geometry m x
  rw [← a.action m x y rfl]
  have he : (a.projection y).toAdd = (a.projection x).toAdd ↔
      y * x⁻¹ ∈ a.projection.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    exact Multiplicative.toAdd.injective.eq_iff
  rw [he, a.kernel]
  rfl

include common radius in
private theorem star_invariants_eq_bot : a.representation.invariants = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  obtain ⟨x, hx⟩ := a.onto (Multiplicative.ofAdd v)
  have hxZ : (x : FreeAmalgam R) ∈ Z R (alpha R) := by
    rw [← star_fixed_preimage_eq_Z source geometry common radius]
    apply (mem_preimage_iff _ _ _ ?_ _).mpr
    · refine ⟨x.property, ?_⟩
      intro l hl
      have hlocal : l ∈ Mbar R := by
        rw [← stabilizer_m_base R]
        exact map_subtype_le _ hl
      obtain ⟨m, rfl⟩ := hlocal
      apply (star_fixed_iff geometry a m x).mp
      rw [hx]
      exact hv m
    · exact ((Flags.star_le_radius geometry _ _).trans
        (geometry.V_local _ rfl common.large_distance)).trans (Z_normalized R _)
  have hk : x ∈ a.projection.ker := a.kernel.symm ▸ hxZ
  have hq : a.projection x = 1 := hk
  rw [hx] at hq
  exact congrArg Multiplicative.toAdd hq

private theorem residual_fixed_le_invariants
    {G A : Type*} [Group G] [AddCommGroup A] [Module (ZMod 2) A]
    (ρ : Representation (ZMod 2) G A) (P E : Subgroup G)
    (W : Submodule (ZMod 2) A) (hEP : E ≤ P) (hn : P ≤ normalizer E)
    (hindex : Odd P.index)
    (hquot : ∀ (g : G) (v : A), ρ g v - v ∈ W)
    (hzero : W ⊓ fixedSpace ρ E ≤ ⊥) :
    fixedSpace ρ E ≤ ρ.invariants := by
  have hmove (p : P) (v : A) (hv : v ∈ fixedSpace ρ E) :
      ρ p v ∈ fixedSpace ρ E := by
    intro e
    have he : (p : G)⁻¹ * (e : G) * p ∈ E :=
      by simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hn (P.inv_mem p.property)) e).mp e.property
    change ρ (e : G) (ρ (p : G) v) = ρ (p : G) v
    calc
      _ = ρ ((e : G) * p) v := (Module.End.mul_apply _ _ _).symm.trans
        (congrArg (fun f => f v) (ρ.map_mul _ _).symm)
      _ = ρ ((p : G) * ((p : G)⁻¹ * e * p)) v := by congr 2; group
      _ = ρ (p : G) (ρ ((p : G)⁻¹ * e * p) v) := by rw [map_mul]; rfl
      _ = ρ (p : G) v := congrArg (ρ (p : G)) (hv ⟨_, he⟩)
  have hPB : fixedSpace ρ P ≤ fixedSpace ρ E := by
    intro v hv e
    exact hv ⟨e, hEP e.property⟩
  have heq := Representation.HigherFieldBorelFixedSpaces.odd_index_fixedSpace_extension
    ρ P W hindex hquot (show W ⊓ fixedSpace ρ P ≤ ρ.invariants from
      (inf_le_inf_left W hPB).trans (hzero.trans bot_le))
  rw [← heq]
  intro v hv p
  have hz : ρ p v - v = 0 := hzero ⟨hquot p v,
    (fixedSpace ρ E).sub_mem (hmove p v hv) hv⟩
  exact sub_eq_zero.mp hz

include common radius in
/-- The selected source-ordered residual fixes a nonzero element of core/U.
The distance, small-intersection and edge-kernel hypotheses are retained in the
consumer-facing statement; the supplied module and triple bound suffice here. -/
theorem flag_fixed_preimage_not_le_U (_hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (_hs : s.SmallIntersection)
    (d : CoreModule source) (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m)
    (i : Bool)
    (_hkernel : Flags.RankOne.flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), Flags.RankOne.flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ¬ commutatorPreimage (core R (alpha R)) (Flags.RankOne.flagResidual source i)
      (U R (alpha R)) ≤ U R (alpha R) := by
  intro hno
  obtain ⟨a⟩ := exists_starModule source geometry common radius
  let P := parabolic source.projection source.flag i
  let E := rankOne P
  let S := VStar R geometry (alpha R) (beta R)
  let C := core R (alpha R)
  have hCS : C ≤ S := core_le_star source geometry common radius _ _ rfl (base_adjacent R)
  let f : C →* Multiplicative a.Space := a.projection.comp (inclusion hCS)
  let W : Submodule (ZMod 2) a.Space := AddSubgroup.toZModSubmodule 2 f.range.toAddSubgroup'
  have hEP : E ≤ P := map_subtype_le _
  have hn : P ≤ normalizer E := by
    dsimp only [E, P]
    rw [rankOne_parabolic_eq source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup)]
    exact P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)
  have hindex : Odd P.index := by
    have hc := (modelParabolic source.flag i).index_mul_card
    rw [card_modelParabolic, Atlas.Comparisons.Exceptional.sl3Two_card] at hc
    have hp : P.index = 7 := by
      dsimp only [P, parabolic]
      rw [index_comap_of_surjective _ source.projection_surjective]
      omega
    rw [hp]
    decide
  have hquot (g : M) (v : a.Space) : a.representation g v - v ∈ W := by
    obtain ⟨x, hx⟩ := a.onto (Multiplicative.ofAdd v)
    let y := starConjugate geometry g x
    have hgc : ⁅embedM R g, (x : FreeAmalgam R)⁆ ∈ C := by
      have hc := star_commutator_local_le_core source geometry common radius
      rw [commutator_comm] at hc
      apply hc (commutator_mem_commutator _ x.property)
      rw [alpha, stabilizer_m_base]
      exact ⟨g, rfl⟩
    let c : C := ⟨⁅embedM R g, (x : FreeAmalgam R)⁆, hgc⟩
    change Multiplicative.ofAdd (a.representation g v - v) ∈ f.range
    refine ⟨c, ?_⟩
    change a.projection (inclusion hCS c) = _
    have hy : inclusion hCS c = y * x⁻¹ := Subtype.ext rfl
    rw [hy, map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg, toAdd_ofAdd]
    rw [a.action g x y rfl, hx]
    rfl
  have hzero : W ⊓ fixedSpace a.representation E ≤ ⊥ := by
    rintro v ⟨hvW, hvE⟩
    obtain ⟨c, hc⟩ : ∃ c : C, f c = Multiplicative.ofAdd v := hvW
    have hcpre : (c : FreeAmalgam R) ∈
        commutatorPreimage C (Flags.RankOne.flagResidual source i) (U R (alpha R)) := by
      have hCP : C ≤ stabilizer R (alpha R) :=
        (core_le_Q source).trans (fun _ hx => hx.1)
      have hCU : C ≤ normalizer (U R (alpha R)) :=
        hCP.trans (by simpa only [alpha, stabilizer_m_base] using common.natural.normalized)
      apply (mem_preimage_iff _ _ _ hCU _).mpr
      refine ⟨c.property, ?_⟩
      intro e he
      obtain ⟨g, hg, rfl⟩ := he
      have hz : ⁅embedM R g, (c : FreeAmalgam R)⁆ ∈ Z R (alpha R) := by
        apply (star_fixed_iff geometry a g (inclusion hCS c)).mp
        change a.representation g (f c).toAdd = (f c).toAdd
        rw [hc]
        exact hvE ⟨g, hg⟩
      have hcc : ⁅embedM R g, (c : FreeAmalgam R)⁆ ∈ C := by
        have hh : Mbar R ≤ normalizer C := core_normalized
        exact (le_normalizer_iff_commutator_le_right.mp hh)
          (commutator_mem_commutator (show embedM R g ∈ Mbar R from ⟨g, rfl⟩) c.property)
      rw [← core_inter_Z_eq_U source geometry common radius d m q]
      exact ⟨hcc, hz⟩
    have hcz := DistanceEight.U_le_Z R (alpha R) (hno hcpre)
    have hk : inclusion hCS c ∈ a.projection.ker := by
      rw [a.kernel]
      exact hcz
    have hz : f c = 1 := hk
    rw [hc] at hz
    exact congrArg Multiplicative.toAdd hz
  have hfixed := residual_fixed_le_invariants a.representation P E W hEP hn hindex hquot hzero
  obtain ⟨x, hxe, hxZ⟩ := SetLike.not_le_iff_exists.mp
    (edgeStar_not_le_Z source geometry common radius)
  let z : S := ⟨x, Flags.edgeStar_le_star geometry _ _ hxe⟩
  have hzfixed : (a.projection z).toAdd ∈ fixedSpace a.representation E := by
    intro e
    apply (star_fixed_iff geometry a e z).mpr
    have he : embedM R e ∈ Flags.RankOne.flagResidual source i := mem_map_of_mem _ e.property
    have hh := edgeStar_commutator_le_Z_of_flag source geometry common radius i htriple
    rw [commutator_comm] at hh
    exact hh (commutator_mem_commutator he hxe)
  have hz0 : (a.projection z).toAdd = 0 := by
    have hh := hfixed hzfixed
    rwa [star_invariants_eq_bot source geometry common radius a] at hh
  apply hxZ
  have hk : z ∈ a.projection.ker := Multiplicative.toAdd.injective hz0
  rwa [a.kernel] at hk

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
