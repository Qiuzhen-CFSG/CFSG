module

public import CFSG.Quasithin.ChapterD.Section01.Configuration
public import CFSG.Quasithin.ChapterD.Section01.ChiefFactors
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.Representation.QuadraticDuality

/-!
# The literal actions and chief-factor hypothesis of D.1.4

The source has no assumption on q. Its chief-factor hypothesis concerns a
genuine G₂-chief series on U = ⟨Vᴳ₂⟩, even before U is known to be abelian.
The dual alternative uses the faithful image of conjugation on V, identified
with the quotient by its centralizer through the first isomorphism theorem.

These interfaces and subgroup transports are shared by the two stages of the
unique-factor proof. Source: Aschbacher--Smith, D.1.4, printed pp.175--176.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

namespace UniqueFactor

/-- Agreement of the chapter's join of conjugates with the closure API. -/
theorem conjugateSpan_eq (H V : Subgroup G) :
    conjugateSpan H V = conjugateSpanBy V H := by
  apply le_antisymm
  · apply iSup_le
    rintro g x ⟨v, hv, rfl⟩
    exact subset_closure ⟨g, g.property, v, hv, rfl⟩
  · apply (closure_le _).mpr
    rintro x ⟨g, hg, v, hv, rfl⟩
    exact (le_iSup (fun g : H => V.map (MulAut.conj (g : G)).toMonoidHom)
      ⟨g, hg⟩) (mem_map_of_mem _ hv)

theorem conjugateSpan_normalized (H V : Subgroup G) :
    H ≤ normalizer (conjugateSpan H V : Set G) := by
  rw [conjugateSpan_eq]
  exact le_normalizer_conjugateSpanBy V H

instance conjugateSpan_subgroupOf_normal (H V : Subgroup G) :
    ((conjugateSpan H V).subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer (conjugateSpan_normalized H V)

/-- One noncentral interval in an actual chief series, not an arbitrary count. -/
def HasUniqueNoncentralChiefFactor (H V : Subgroup G) : Prop :=
  ∃ s : NoncentralChiefRefinement.SeriesOn ((conjugateSpan H V).subgroupOf H),
    s.noncentralCount = 1

/-- The literal conjugation homomorphism whose range occurs in D.1.1. -/
def actionHom (H V : Subgroup G) (hHV : H ≤ normalizer (V : Set G)) :
    H →* MulAut V := V.normalizerMonoidHom.comp (inclusion hHV)

theorem actionHom_ker (H V : Subgroup G) (hHV : H ≤ normalizer (V : Set G)) :
    (actionHom H V hHV).ker = (centralizer (V : Set G)).subgroupOf H := by
  ext g
  constructor
  · intro hg v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G))
      (MonoidHom.mem_ker.mp hg)
    change (g : G) * v * (g : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (g : G) * (v : G) * (g : G)⁻¹ = v
    have hv : (v : G) * (g : G) = (g : G) * (v : G) := hg v v.property
    rw [← hv, mul_inv_cancel_right]

/-- The action image is the genuine centralizer quotient, using the kernel
identified by `actionHom_ker`. -/
noncomputable def actionQuotientEquiv (H V : Subgroup G)
    (hHV : H ≤ normalizer (V : Set G)) :
    H ⧸ (actionHom H V hHV).ker ≃* internalActionImage H V hHV :=
  QuotientGroup.quotientKerEquivRange (actionHom H V hHV)

/-- The faithful binary action on the original internal V. -/
noncomputable def imageRepresentation (H V : Subgroup G)
    (hHV : H ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V] :
    Representation (ZMod 2) (internalActionImage H V hHV) (Additive V) where
  toFun a := a.val.toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    rfl

theorem imageRepresentation_injective (H V : Subgroup G)
    (hHV : H ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V] :
    Function.Injective (imageRepresentation H V hHV) := by
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) (Additive V) =>
    (f (Additive.ofMul v)).toMul) hab

/-- D.1.4(1), on the actual faithful conjugation image. -/
def DualFF {G₁ G₂ T V : Subgroup G} (d : QRCConfiguration G₁ G₂ T V) : Prop :=
  letI := d.module_elementary
  Representation.BinaryOffender.IsFFModule
    (imageRepresentation G₁ V d.module_normalized).dual

/-- The source's Q before its equality with R ∩ R₂ has been proved. -/
noncomputable def intersectionClosure (G₁ G₂ : Subgroup G) : Subgroup G :=
  conjugateSpan G₂ (twoCoreIn G₁ ⊓ twoCoreIn G₂)

theorem twoCore_le (H : Subgroup G) : twoCoreIn H ≤ H := map_subtype_le _

theorem twoCore_normalized (H : Subgroup G) :
    H ≤ normalizer (twoCoreIn H : Set G) := by
  have ht : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  conv_lhs => rw [← ht]
  exact (map_mono (show (⊤ : Subgroup H) ≤ normalizer (pCore 2 H : Set H) by
    rw [normalizer_eq_top])).trans (le_normalizer_map H.subtype)

theorem sylow_le_left {G₁ G₂ T V : Subgroup G} (d : QRCConfiguration G₁ G₂ T V) :
    T ≤ G₁ := by
  obtain ⟨S, hS⟩ := d.sylow_left
  rw [← hS]
  exact map_subtype_le _

theorem sylow_le_right {G₁ G₂ T V : Subgroup G} (d : QRCConfiguration G₁ G₂ T V) :
    T ≤ G₂ := by
  obtain ⟨S, hS⟩ := d.sylow_right
  rw [← hS]
  exact map_subtype_le _

theorem left_core_le_sylow {G₁ G₂ T V : Subgroup G}
    (d : QRCConfiguration G₁ G₂ T V) : twoCoreIn G₁ ≤ T := by
  rw [d.core_eq_centralizer]
  exact inf_le_left

theorem right_core_le_sylow {G₁ G₂ T V : Subgroup G}
    (d : QRCConfiguration G₁ G₂ T V) : twoCoreIn G₂ ≤ T := by
  let := d.finite_right
  obtain ⟨S, hS⟩ := d.sylow_right
  rw [← hS]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal S)

theorem span_le_right_core {G₁ G₂ T V : Subgroup G}
    (_d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂) :
    conjugateSpan G₂ V ≤ twoCoreIn G₂ :=
  conjugateSpan_le G₂ V _ hV (twoCore_normalized G₂)

/-- The unique-factor hypothesis excludes the trivial module permitted by D.1.1. -/
theorem module_ne_bot {H V : Subgroup G} (hu : HasUniqueNoncentralChiefFactor H V) :
    V ≠ ⊥ := by
  intro hV
  obtain ⟨s, hs⟩ := hu
  obtain ⟨i, hi, _⟩ := s.noncentralCount_eq_one_iff.mp hs
  apply hi
  rw [NoncentralChiefRefinement.SeriesOn.Central,
    NoncentralChiefRefinement.isCentral_iff_commutator_le]
  have hspan : conjugateSpan H V = ⊥ := by
    rw [hV]
    exact le_antisymm (conjugateSpan_le H ⊥ ⊥ le_rfl
      (by rw [normalizer_eq_top]; exact le_top)) bot_le
  have hup : (s.upper i).val = ⊥ := by
    apply le_bot_iff.mp
    simpa only [hspan, bot_subgroupOf] using s.upper_le i
  rw [hup, commutator_bot_right]
  exact bot_le

end UniqueFactor
end CFSG.Quasithin.ChapterD
