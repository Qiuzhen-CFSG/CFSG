module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The original plus kernel and its subnormal residuals

Put U0=C_UH(QH) and C=C_H(UH/U0). The literal section action has
embedded kernel C, which is normal in H and contains QH. A nontrivial
subnormal two-perfect subgroup K of C satisfies the source calculation
[UH,K]=[U0,K]≠1, with this commutator in O₂(K)≤QH. In particular
K acts nontrivially on the fixed layer U0 and O₂(K) centralizes U0.

These conclusions use the original F.9 kernel bound and subnormal
coprime commutator idempotence. They are the opening calculation (!)
in the proof of Aschbacher--Smith 13.7.4(1), printed pp.936--937.
The later component and odd-core exclusions are separate source steps.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]

def fixedLayer (D : ChapterF.Section09.Setup G) : Subgroup G :=
  D.UH ⊓ centralizer (D.QH : Set G)

def kernel (D : ChapterF.Section09.Setup G) : Subgroup G :=
  commutatorPreimage D.H D.UH (fixedLayer D)

variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

include h

omit [Finite G] h in
theorem fixedLayer_normalized : D.H ≤ normalizer (fixedLayer D : Set G) :=
  (le_inf (le_normalizer_conjugateSpanBy D.Vplus D.H)
    (Hypothesis.H_normalizes_QH.trans (normalizer_le_normalizer_centralizer D.QH))).trans
      inf_normalizer_le_normalizer_inf

theorem point_le_fixedLayer : D.V₁ ≤ fixedLayer D :=
  le_inf (h.point_lt.le.trans (le_conjugateSpanBy D.Vplus D.H))
    (le_centralizer_iff.mp ((pCoreIn_le 2 D.H).trans h.H_centralizes))

theorem core_le_kernel : D.QH ≤ kernel D := by
  apply le_commutatorPreimage (pCoreIn_le 2 D.H)
  rw [commutator_comm]
  exact h.commutator_UH_QH_le_point.trans (point_le_fixedLayer h)

omit [Finite G] h in
theorem kernel_le_H : kernel D ≤ D.H := commutatorPreimage_le _ _ _

omit [Finite G] h in
theorem kernel_normalized : D.H ≤ normalizer (kernel D : Set G) :=
  commutatorPreimage_normalized D.H D.UH (fixedLayer D) D.H
    (fixedLayer_normalized (D := D)) D.H.le_normalizer
    (le_normalizer_conjugateSpanBy D.Vplus D.H) (fixedLayer_normalized (D := D))

omit [Finite G] h in
theorem kernel_normal : ((kernel D).subgroupOf D.H).Normal :=
  normal_subgroupOf_of_le_normalizer (kernel_normalized (D := D))

omit [Finite G] h in
theorem kernel_commutator : ⁅D.UH, kernel D⁆ ≤ fixedLayer D := by
  rw [commutator_comm]
  exact commutator_commutatorPreimage_le _ _ _ (fixedLayer_normalized (D := D))

omit [Finite G] h in
theorem section_action_kernel {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D.H W}
    (s : Representation.BinaryConjugationSection D.H D.UH (fixedLayer D) ρ) :
    ρ.ker.map D.H.subtype = kernel D :=
  s.action_kernel_map (fixedLayer_normalized (D := D))

theorem centralizer_UH_le_core :
    D.H ⊓ centralizer (D.UH : Set G) ≤ D.QH := by
  apply le_trans _ h.kernel_UH_eq_QH.le
  intro x hx
  apply (h.mem_kernel_iff h.UH_le_H).mpr
  refine ⟨hx.1, fun u hu => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
  exact D.V₁.one_mem

omit h in
theorem subnormal_core_le {K : Subgroup G} (hKH : K ≤ D.H)
    (hn : (K.subgroupOf D.H).IsSubnormal) : K.pCoreIn 2 ≤ D.QH :=
  pCoreAmbient_mono_of_isSubnormalIn K D.H 2 hKH hn

omit [Finite G] h in
theorem core_normalizes_subnormal {K : Subgroup G} (hKH : K ≤ D.H)
    (hn : (K.subgroupOf D.H).IsSubnormal) (hp : IsPPerfect 2 K) :
    D.QH ≤ normalizer (K : Set G) := by
  have hp' : IsPPerfect 2 (K.subgroupOf D.H) :=
    hp.of_surjective (subgroupOfEquivOfLe hKH).symm.toMonoidHom
      (subgroupOfEquivOfLe hKH).symm.surjective
  have hnQ : K.subgroupOf D.H ≤ normalizer (D.QH.subgroupOf D.H : Set D.H) := by
    intro k _
    rw [mem_normalizer_iff]
    intro q
    exact mem_normalizer_iff.mp (Hypothesis.H_normalizes_QH (D := D) k.property) q.val
  have hh := le_normalizer_of_isSubnormal_isPPerfect
    (K.subgroupOf D.H) (D.QH.subgroupOf D.H) hn hp'
    ((isPGroup_pCoreIn 2 D.H).comap_subtype) hnQ
  rw [← subgroupOf_normalizer_eq hKH] at hh
  intro q hq
  exact hh (show (⟨q, pCoreIn_le 2 D.H hq⟩ : D.H) ∈ D.QH.subgroupOf D.H from hq)

theorem residual_kernel_commutator {K : Subgroup G} (hKC : K ≤ kernel D)
    (hp : IsPPerfect 2 K) : ⁅D.UH, K⁆ = ⁅fixedLayer D, K⁆ := by
  have hKU : K ≤ normalizer (D.UH : Set G) :=
    (hKC.trans kernel_le_H).trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have hi := commutator_isPPerfect_idempotent K D.UH hp
    (h.g2_hypothesis.U_isPGroup) hKU
  apply le_antisymm
  · rw [← hi]
    exact commutator_mono
      ((commutator_mono le_rfl hKC).trans (kernel_commutator (D := D))) le_rfl
  · exact commutator_mono inf_le_left le_rfl

theorem residual_kernel_commutator_ne_bot {K : Subgroup G}
    (hKC : K ≤ kernel D) (hp : IsPPerfect 2 K) (hne : K ≠ ⊥) :
    ⁅D.UH, K⁆ ≠ ⊥ := by
  intro hc
  have hKH : K ≤ D.H := hKC.trans kernel_le_H
  have hKQ : K ≤ D.QH := (le_inf hKH
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))).trans
      (centralizer_UH_le_core h)
  have hpK : IsPGroup 2 K := (isPGroup_pCoreIn 2 D.H).to_le hKQ
  have hi := hp.hom_eq_one_of_isPGroup hpK (MonoidHom.id K)
  apply hne
  apply eq_bot_iff.mpr
  intro k hk
  have he := congrArg (fun f : K →* K => (f ⟨k, hk⟩ : G)) hi
  exact he

/-- The entire source calculation (!), on any actual nontrivial subnormal
two-perfect subgroup of the plus kernel. -/
theorem subnormal_kernel_structure {K : Subgroup G} (hKC : K ≤ kernel D)
    (hn : (K.subgroupOf D.H).IsSubnormal) (hp : IsPPerfect 2 K) (hne : K ≠ ⊥) :
    ⁅D.UH, K⁆ = ⁅fixedLayer D, K⁆ ∧
    ⁅fixedLayer D, K⁆ ≠ ⊥ ∧
    ⁅fixedLayer D, K⁆ ≤ K.pCoreIn 2 ∧
    K.pCoreIn 2 ≤ D.QH ∧
    K.pCoreIn 2 ≤ centralizer (fixedLayer D : Set G) := by
  have hKH : K ≤ D.H := hKC.trans kernel_le_H
  have hid := residual_kernel_commutator h hKC hp
  have hnorm := core_normalizes_subnormal hKH hn hp
  have hcK : ⁅D.UH, K⁆ ≤ K := le_normalizer_iff_commutator_le_right.mp
    (h.UH_le_QH.trans hnorm)
  have hcU : ⁅D.UH, K⁆ ≤ D.UH := le_normalizer_iff_commutator_le_left.mp
    (hKH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
  have hcore : ⁅D.UH, K⁆ ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (h.g2_hypothesis.U_isPGroup.to_le hcU) hcK
      (normalizer_commutator_ge_right D.UH K)
  have hQ := subnormal_core_le hKH hn
  exact ⟨hid, hid ▸ residual_kernel_commutator_ne_bot h hKC hp hne,
    hid ▸ hcore, hQ, hQ.trans (le_centralizer_iff.mp inf_le_right)⟩

/-- An arbitrary subgroup of the plus kernel has a two-group kernel on
the original fixed layer. The proof uses its actual two-residual. -/
theorem fixedLayer_centralizer_isPGroup {K : Subgroup G} (hKC : K ≤ kernel D) :
    IsPGroup 2 (K ⊓ centralizer (fixedLayer D : Set G) : Subgroup G) := by
  let N := K ⊓ centralizer (fixedLayer D : Set G)
  let R := (pResidual 2 N).map N.subtype
  have hRC : R ≤ kernel D := (map_subtype_le _).trans (inf_le_left.trans hKC)
  have hpR : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 N
  have hc : ⁅fixedLayer D, R⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr ((map_subtype_le _).trans inf_le_right)
  have hR : R = ⊥ := by
    by_contra hn
    exact residual_kernel_commutator_ne_bot h hRC hpR hn
      ((residual_kernel_commutator h hRC hpR).trans hc)
  have hr : pResidual 2 N = ⊥ := by
    apply map_injective N.subtype_injective
    simpa only [Subgroup.map_bot] using hR
  apply (isPGroup_quotient_pResidual 2 (G := N)).of_injective
    (QuotientGroup.mk' (pResidual 2 N))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [QuotientGroup.ker_mk', hr]

/-- The source equality (*) on the literal U0. Subnormality suffices;
the later simple and odd-order model alternatives are not needed here. -/
theorem subnormal_fixedLayer_centralizer {K : Subgroup G} (hKC : K ≤ kernel D)
    (hn : (K.subgroupOf D.H).IsSubnormal) :
    K ⊓ centralizer (fixedLayer D : Set G) = K.pCoreIn 2 := by
  have hKH : K ≤ D.H := hKC.trans kernel_le_H
  apply le_antisymm
  · apply le_pCoreIn_of_normalizes (fixedLayer_centralizer_isPGroup h hKC) inf_le_left
    exact (le_inf K.le_normalizer ((hKH.trans (fixedLayer_normalized (D := D))).trans
      (normalizer_le_normalizer_centralizer (fixedLayer D)))).trans
        inf_normalizer_le_normalizer_inf
  · exact le_inf (pCoreIn_le 2 K)
      ((subnormal_core_le hKH hn).trans (le_centralizer_iff.mp inf_le_right))

/-- The two-core of the original plus kernel is exactly the original QH. -/
theorem kernel_core : (kernel D).pCoreIn 2 = D.QH := by
  apply le_antisymm (subnormal_core_le kernel_le_H (kernel_normal.isSubnormal))
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 D.H) (core_le_kernel h)
  exact kernel_le_H.trans Hypothesis.H_normalizes_QH

/-- The whole plus kernel has exactly QH as its kernel on U0. This does
not identify the plus kernel itself with QH. -/
theorem kernel_fixedLayer_centralizer :
    kernel D ⊓ centralizer (fixedLayer D : Set G) = D.QH :=
  (subnormal_fixedLayer_centralizer h le_rfl kernel_normal.isSubnormal).trans
    (kernel_core h)

end CFSG.Quasithin.Chapter13.Section07.PlusAction
