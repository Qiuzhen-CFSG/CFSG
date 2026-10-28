module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCoreElementary
public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# The actual containing-core Frattini action

For the original parabolic H, retain E=<N_G(T₁),H>, K=<O²(H)^E>,
and Q=O₂(K). The actual ambient characteristic-two hypothesis passes first
to E and then to its relatively normal subgroup K. Burnside's Frattini
kernel theorem consequently identifies the kernel of K acting on Q/Φ(Q)
with O₂(K). Thus the original quotient K/O₂(K), with its original
conjugation map, acts faithfully on this elementary abelian section.

The common kernel Q∩O₂(L₀T) contains Φ(Q), so its image has index sixteen
in this section under collapse. The original module V centralizes this
image. Its fixed subgroup therefore has index dividing sixteen. The image
is not K-invariant: pulling invariance back through the same quotient would
contradict the proved nonnormality of the original common kernel.

The last two theorems apply these facts to the literal source witnesses and
to both requested contracts, without a new premise. These action constraints
do not yet exclude the collapsed configuration. Its exclusion and assembly
of StabilizerNormalizerAt and HalfSylowUniqueAt remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only external premise,
finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The original containing normal closure inherits characteristic two from its enlargement. -/
theorem Data.enlargedResidual_mem_He (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    enlargedResidual T L H ∈ He G := by
  have he : enlargement T L H ∈ He G := lemma_1_1_4_6 T (D.simpleQTKE.evenCharacteristic T)
    ⟨h.enlargement_mem_H hn,h.sylow_le.trans le_sup_right⟩
  let : ((enlargedResidual T L H).subgroupOf (enlargement T L H)).Normal :=
    h.enlargedResidual_normal
  exact mem_He_iff.mpr ((Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe h.enlargedResidual_le_enlargement)).mp
      (normal_core_selfCentralizing (mem_He_iff.mp he) _))

omit [Finite G] in
/-- The original enlargement normalizes the original containing core. -/
theorem enlargement_normalizes_core (T : Sylow 2 G) (L H : Subgroup G) :
    enlargement T L H ≤ normalizer ((enlargedResidual T L H).pCoreIn 2 : Set G) :=
  (le_normalizer_conjugateSpanBy _ _).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The literal containing core modulo its own Frattini subgroup. -/
abbrev CoreFrattiniSection (T : Sylow 2 G) (L H : Subgroup G) :=
  (enlargedResidual T L H).pCoreIn 2 ⧸ frattini ((enlargedResidual T L H).pCoreIn 2)

/-- Conjugation by the actual enlargement on the containing core's Frattini section. -/
def coreFrattiniAction (T : Sylow 2 G) (L H : Subgroup G) :
    enlargement T L H →* MulAut (CoreFrattiniSection T L H) :=
  (quotientAut (frattini ((enlargedResidual T L H).pCoreIn 2))).comp
    (((enlargedResidual T L H).pCoreIn 2).normalizerMonoidHom.comp
      (inclusion (enlargement_normalizes_core T L H)))

omit [Finite G] in
/-- The action uses the same conjugation and the same quotient map as the original core. -/
theorem coreFrattiniAction_mk (g : enlargement T L H)
    (q : (enlargedResidual T L H).pCoreIn 2) :
    coreFrattiniAction T L H g (QuotientGroup.mk' _ q) =
      QuotientGroup.mk' _ (((enlargedResidual T L H).pCoreIn 2).normalizerMonoidHom
        ⟨g,enlargement_normalizes_core T L H g.property⟩ q) := by
  exact quotientAut_apply_mk _ _ _

/-- The containing quotient acts faithfully: the kernel on K is exactly O₂(K). -/
theorem Data.coreFrattiniAction_kernel (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ((coreFrattiniAction T L H).comp (inclusion h.enlargedResidual_le_enlargement)).ker =
      pCore 2 (enlargedResidual T L H) := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  let a : K →* MulAut Q := Q.normalizerMonoidHom.comp
    (inclusion (h.enlargedResidual_le_enlargement.trans (enlargement_normalizes_core T L H)))
  let b := (quotientAut (frattini Q)).comp a
  have hQ := isPGroup_pCoreIn 2 K
  have hker : a.ker ≤ pCore 2 K := by
    intro g hg
    have hcent : (g : G) ∈ centralizer (Q : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hh := congrArg (fun f : MulAut Q => (f ⟨q,hq⟩ : G))
        (show a g = 1 from hg)
      change (g:G) * q * (g:G)⁻¹ = q at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hself : K ⊓ centralizer (Q : Set G) ≤ Q := h.enlargedResidual_mem_He hn
    obtain ⟨x,hx,he⟩ := hself ⟨g.property,hcent⟩
    exact (Subtype.ext he : x=g) ▸ hx
  have hp : IsPGroup 2 b.ker :=
    (isPGroup_quotientAut_frattini_kernel hQ).comap_of_ker_isPGroup a
      (pCore_isPGroup.to_le hker)
  change b.ker = pCore 2 K
  apply le_antisymm (show b.ker ≤ pCore 2 K from le_sSup ⟨inferInstance,hp⟩)
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) := isElementaryAbelian_quotient_frattini
  intro g hg
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) v
  have hgQ : (g:G) ∈ Q := mem_map_of_mem K.subtype hg
  change quotientAut (frattini Q) (a g) (QuotientGroup.mk' _ q) = QuotientGroup.mk' _ q
  rw [quotientAut_apply_mk]
  have he : a g q = (⟨g,hgQ⟩ : Q) * q * (⟨g,hgQ⟩ : Q)⁻¹ := rfl
  rw [he,map_mul,map_mul,map_inv,mul_comm (QuotientGroup.mk' _ (⟨g,hgQ⟩ : Q))
    (QuotientGroup.mk' _ q),mul_inv_cancel_right]

/-- The common kernel, in the same containing-core Frattini section. -/
def commonFrattiniImage (T : Sylow 2 G) (L H : Subgroup G) :
    Subgroup (CoreFrattiniSection T L H) :=
  (((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2).subgroupOf
    ((enlargedResidual T L H).pCoreIn 2)).map (QuotientGroup.mk' _)

/-- The common kernel has codimension four in the literal Frattini section. -/
theorem Data.commonFrattiniImage_index (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (commonFrattiniImage T L H).index = 16 := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let N := (Q ⊓ (localJoin T L).pCoreIn 2).subgroupOf Q
  have hphi : frattini Q ≤ N := by
    intro q hq
    exact h.core_frattini_le_common_kernel f hi hP (mem_map_of_mem Q.subtype hq)
  change (N.map (QuotientGroup.mk' (frattini Q))).index = 16
  rw [N.index_map_eq (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])]
  have hh := h.collapsed_core_centralizer_relIndex f hi hP hc
  rwa [h.core_action_kernel_eq_intersection f] at hh

/-- The actual original module fixes the common-kernel image pointwise in the new section. -/
theorem Data.fullModule_fixes_commonFrattiniImage (_h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (v : enlargement T L H) (hv : (v:G) ∈ D.fullModule)
    (w : CoreFrattiniSection T L H) (hw : w ∈ commonFrattiniImage T L H) :
    coreFrattiniAction T L H v w = w := by
  obtain ⟨q,hq,rfl⟩ := hw
  rw [coreFrattiniAction_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  change (v:G) * (q:G) * (v:G)⁻¹ = (q:G)
  have he : (v:G) * (q:G) = (q:G) * (v:G) :=
    D.core_centralizes_module hq.2 v (hfull ▸ hv)
  rw [he,mul_inv_cancel_right]

/-- The actual quotient K/O₂(K) embeds in the automorphism group of this same
Frattini section, compatibly with every original element of K. -/
theorem Data.exists_faithful_coreFrattiniAction (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ a : XiQuotient (enlargedResidual T L H) →* MulAut (CoreFrattiniSection T L H),
      Function.Injective a ∧ ∀ k : enlargedResidual T L H,
        a (QuotientGroup.mk' _ k) =
          coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k) := by
  let b := (coreFrattiniAction T L H).comp (inclusion h.enlargedResidual_le_enlargement)
  have hb := h.coreFrattiniAction_kernel hn
  let a := QuotientGroup.lift (pCore 2 (enlargedResidual T L H)) b hb.ge
  exact ⟨a,(QuotientGroup.injective_lift_iff _ b hb.ge).mpr hb.symm,fun _ => rfl⟩

/-- The original module has fixed index at most sixteen on the containing
core's Frattini section. This is an action bound, not a bound on its dimension. -/
theorem Data.coreFrattiniAction_fixed_index (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    let A := D.fullModule.subgroupOf (enlargement T L H)
    let := MulDistribMulAction.compHom (CoreFrattiniSection T L H)
      ((coreFrattiniAction T L H).comp A.subtype)
    (FixedPoints.subgroup A (CoreFrattiniSection T L H)).index ∣ 16 := by
  let A := D.fullModule.subgroupOf (enlargement T L H)
  let := MulDistribMulAction.compHom (CoreFrattiniSection T L H)
    ((coreFrattiniAction T L H).comp A.subtype)
  have hle : commonFrattiniImage T L H ≤ FixedPoints.subgroup A (CoreFrattiniSection T L H) := by
    intro w hw v
    exact h.fullModule_fixes_commonFrattiniImage s.full_eq_local v v.property w hw
  exact h.commonFrattiniImage_index f hi hP hc ▸ index_dvd_of_le hle

/-- The common kernel's codimension-four image is not invariant under the
actual containing component action, even after passage to Frattini. -/
theorem Data.commonFrattiniImage_not_invariant (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D) {I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ¬ ∀ k : enlargedResidual T L H,
      (commonFrattiniImage T L H).map
        (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)).toMonoidHom =
          commonFrattiniImage T L H := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  let N := (Q ⊓ (localJoin T L).pCoreIn 2).subgroupOf Q
  let π := QuotientGroup.mk' (frattini Q)
  have hphi : frattini Q ≤ N := by
    intro q hq
    exact h.core_frattini_le_common_kernel f hs.toLocalInput hP (mem_map_of_mem Q.subtype hq)
  have hpre : (commonFrattiniImage T L H).comap π = N := by
    change (N.map π).comap π = N
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hphi]
  intro hinv
  apply h.collapsed_core_kernel_not_normalized f hn hmodel hs hK hp ho hm hlarge hP hc
  change K ≤ normalizer (↑(Q ⊓ (localJoin T L).pCoreIn 2) : Set G)
  rw [le_normalizer_iff]
  intro k hk n hn'
  let k' : K := ⟨k,hk⟩
  let n' : Q := ⟨n,hn'.1⟩
  let g := inclusion h.enlargedResidual_le_enlargement k'
  let y := Q.normalizerMonoidHom ⟨g,enlargement_normalizes_core T L H g.property⟩ n'
  have hmem : π y ∈ commonFrattiniImage T L H := by
    rw [←coreFrattiniAction_mk]
    rw [←hinv k']
    exact mem_map_of_mem _ (mem_map_of_mem π (show n' ∈ N from hn'))
  have hy : y ∈ N := hpre ▸ hmem
  exact hy

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual source obstruction gives a faithful containing-quotient action
and the same noninvariant common-kernel image, fixed by the original module. -/
theorem SourceCubicNormalizerEnlargement.exists_frattini_action
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H : Subgroup G, ∃ h : Data D H,
      (∃ a : XiQuotient (enlargedResidual T L H) →* MulAut (CoreFrattiniSection T L H),
        Function.Injective a ∧ ∀ k : enlargedResidual T L H,
          a (QuotientGroup.mk' _ k) =
            coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)) ∧
      (commonFrattiniImage T L H).index = 16 ∧
      (∀ v : enlargement T L H, (v:G) ∈ D.fullModule →
        ∀ w ∈ commonFrattiniImage T L H, coreFrattiniAction T L H v w = w) ∧
      (let A := D.fullModule.subgroupOf (enlargement T L H)
       let := MulDistribMulAction.compHom (CoreFrattiniSection T L H)
         ((coreFrattiniAction T L H).comp A.subtype)
       (FixedPoints.subgroup A (CoreFrattiniSection T L H)).index ∣ 16) ∧
      ¬ ∀ k : enlargedResidual T L H,
        (commonFrattiniImage T L H).map
          (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)).toMonoidHom =
            commonFrattiniImage T L H := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  have hlarge : 11 ≤ p := by have := Nat.mod_le p 24; omega
  exact ⟨H,h,h.exists_faithful_coreFrattiniAction hn,
    h.commonFrattiniImage_index f hs.toLocalInput hP hcollapse,
    h.fullModule_fixes_commonFrattiniImage hfull,
    h.coreFrattiniAction_fixed_index f hs.toLocalInput hP hcollapse,
    h.commonFrattiniImage_not_invariant f hn hmodel hs hK hp ho hm hlarge hP hcollapse⟩

/-- Both original source contracts reduce to the same configuration, now with
its faithful Frattini action and the original module's fixed-index bound. -/
theorem sourceContracts_or_cubicFrattiniAction (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, ∃ h : Data D H,
          (∃ a : XiQuotient (enlargedResidual T L H) →* MulAut (CoreFrattiniSection T L H),
            Function.Injective a ∧ ∀ k : enlargedResidual T L H,
              a (QuotientGroup.mk' _ k) =
                coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)) ∧
          (commonFrattiniImage T L H).index = 16 ∧
          (let A := D.fullModule.subgroupOf (enlargement T L H)
           let := MulDistribMulAction.compHom (CoreFrattiniSection T L H)
             ((coreFrattiniAction T L H).comp A.subtype)
           (FixedPoints.subgroup A (CoreFrattiniSection T L H)).index ∣ 16) ∧
          ¬ ∀ k : enlargedResidual T L H,
            (commonFrattiniImage T L H).map
              (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)).toMonoidHom =
                commonFrattiniImage T L H := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,h,ha,hi,_,hfix,hnot⟩ := hc.exists_frattini_action
    exact Or.inr ⟨L,D,hc,H,h,ha,hi,hfix,hnot⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
