module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.ClosureBounds
public import Theory.Frattini.ConjugateSpan
public import Theory.GroupTheory.SylowCoreRestriction
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Original action images and the closure Frattini bound

Comparing images in Aut(V) compares their actual commutators with every
subgroup of V. Pointwise fixation is equivalent to the corresponding literal
centralizer. The initial two-core lies in the original R₁ and Sylow subgroup.
Finally [V,W_H]≤V₁ propagates through the G₁-conjugate generators to
[W_H,W_H]≤V₁ and hence Φ(W_H)≤V₁, since those generators are involutions.
These are the group-theoretic inputs to the marked radical calculation in
Aschbacher--Smith 11.5.7, printed pp.782--783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] {V : Subgroup G}

theorem image_mono {A B : Subgroup G} (h : A ≤ B) :
    actionImage (V := V) A ≤ actionImage (V := V) B := map_mono (comap_mono h)

theorem image_normalizes (A B : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) :
    actionImage (V := V) B ≤ normalizer (actionImage (V := V) A : Set (MulAut V)) := by
  apply le_trans _ (le_normalizer_map V.normalizerMonoidHom)
  apply map_mono
  exact (comap_mono hn).trans (A.le_normalizer_comap _)

theorem commutator_mono_of_image_le (A B C : Subgroup G) (hCV : C ≤ V)
    (hA : A ≤ normalizer (V : Set G))
    (h : actionImage (V := V) A ≤ actionImage (V := V) B) :
    ⁅C,A⁆ ≤ ⁅C,B⁆ := by
  rw [commutator_comm C A, commutator_comm C B]
  apply commutator_le.mpr
  intro a ha c hc
  have hm : V.normalizerMonoidHom ⟨a,hA ha⟩ ∈ actionImage (V := V) B :=
    h (mem_map_of_mem _ (show (⟨a,hA ha⟩ : normalizer (V : Set G)) ∈
      A.subgroupOf _ from ha))
  obtain ⟨b,hb,he⟩ := hm
  have hec := congrArg (fun f : MulAut V => ((f ⟨c,hCV hc⟩ : V) : G)) he
  have hecomm : ⁅(b : G),c⁆ = ⁅a,c⁆ := by
    change (b : G) * c * (b : G)⁻¹ = a * c * a⁻¹ at hec
    simpa only [commutatorElement_def] using congrArg (fun x => x * c⁻¹) hec
  rw [← hecomm]
  exact commutator_mem_commutator hb hc

theorem commutator_eq_of_image_eq (A B C : Subgroup G) (hCV : C ≤ V)
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (h : actionImage (V := V) A = actionImage (V := V) B) :
    ⁅C,A⁆ = ⁅C,B⁆ :=
  le_antisymm (commutator_mono_of_image_le A B C hCV hA h.le)
    (commutator_mono_of_image_le B A C hCV hB h.ge)

theorem image_le_fixer_iff (A C : Subgroup G) (hCV : C ≤ V)
    (hA : A ≤ normalizer (V : Set G)) :
    actionImage (V := V) A ≤ fixingSubgroup (MulAut V) (C.subgroupOf V : Set V) ↔
      ⁅C,A⁆ = ⊥ := by
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h a ha c hc
    have hm := h (mem_map_of_mem V.normalizerMonoidHom
      (show (⟨a,hA ha⟩ : normalizer (V : Set G)) ∈ A.subgroupOf _ from ha))
    have he := congrArg Subtype.val ((mem_fixingSubgroup_iff _).mp hm ⟨c,hCV hc⟩ hc)
    change a * c * a⁻¹ = c at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h f hf
    obtain ⟨a,ha,rfl⟩ := hf
    apply (mem_fixingSubgroup_iff _).mpr
    intro c hc
    apply Subtype.ext
    change (a : G) * (c : G) * (a : G)⁻¹ = (c : G)
    exact mul_inv_eq_iff_eq_mul.mpr (h ha c hc).symm

variable [Finite G]
open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L : Subgroup G} {D : ChosenModule T L V}
    (E : Geometry D)

theorem core_le_local_radical (m : MarkedFlag E) : E.G₁.pCoreIn 2 ≤ E.R₁ :=
  Theory.GroupTheory.pCoreIn_le_of_sylow_le T le_sup_right
    (sup_le ((residualIn_le _).trans inf_le_right) m.sylow_le_point_normalizer)

theorem core_le_sylow (m : MarkedFlag E) : E.G₁.pCoreIn 2 ≤ (T : Subgroup G) :=
  (core_le_local_radical E m).trans (LocalGeometry.localRadical_le_sylow E.V₁)

theorem closure_frattini_le_point (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (hc : ⁅V,E.W⁆ ≤ E.V₁) :
    (frattini E.W).map E.W.subtype ≤ E.V₁ := by
  let := D.elementary
  apply frattini_conjugateSpan_le_of_commutator V E.G₁ E.V₁
    ((isPGroup_pCoreIn 2 E.G₁).to_le hW)
  change ⁅conjugateSpanBy V E.G₁,E.W⁆ ≤ E.V₁
  rw [conjugateSpanBy_eq_iSup_conj]
  apply commutator_iSup_le_of_relative_normal E.G₁ E.W E.V₁ _ le_rfl
  · intro g
    exact (map_mono (f := (MulAut.conj (g : G)).toMonoidHom)
      (D.le_sylow.trans m.sylow_le_point_normalizer)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (E.G₁.le_normalizer g.property))
  · intro g
    have hh := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hc
    have hw : E.W.map (MulAut.conj (g : G)).toMonoidHom = E.W :=
      mem_normalizer_iff_map_conj_eq.mp ((closure_normalizations E).2 g.property)
    have hp : E.V₁.map (MulAut.conj (g : G)).toMonoidHom = E.V₁ :=
      mem_normalizer_iff_map_conj_eq.mp g.property
    simpa only [map_commutator, hw, hp] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction
