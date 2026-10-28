module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisMarkedModule

/-!
# Fusion in the original Rudvalis source module

The natural G₂(2)′ action is transitive on the 63 nonzero vectors.
The full source module is the conjugated chosen module, and L is covered
by the intersection residual and its two-core. Since the latter centralizes
the module, fusion is already realized by that literal residual.

Source: Aschbacher–Smith 4.2.13, printed pp.611–612. The universal
Structural1222 input retains its final discharge with qt-theorem-d.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Chapter4 Chapter4.Section04 Chapter4.Section02.Unitary OriginalPlaneCentralizers
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original natural module is transitive on nonidentity elements under L. -/
theorem unitary_original_nonzero_fusion (s : Context T L V)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, l * x * l⁻¹ = y := by
  let v : Additive V := Additive.ofMul ⟨x,hx⟩
  let w : Additive V := Additive.ofMul ⟨y,hy⟩
  have hv : v ≠ 0 := fun h => hx1 (congrArg (fun z : Additive V => z.toMul.val) h)
  have hw : w ≠ 0 := fun h => hy1 (congrArg (fun z : Additive V => z.toMul.val) h)
  obtain ⟨g,hg⟩ := Atlas.G2.Natural.derivedAction_transitive (ZMod 2)
    (s.coordinates v) (s.coordinates w)
    (fun h => hv (s.coordinates.map_eq_zero_iff.mp h))
    (fun h => hw (s.coordinates.map_eq_zero_iff.mp h))
  obtain ⟨a,rfl⟩ := s.actor.surjective g
  have ht : automizerRepresentation V a v = w := s.coordinates.injective
    ((s.equivariant a v).trans hg)
  obtain ⟨n,hn,he⟩ := a.property
  refine ⟨n.val,hn,?_⟩
  rw [←he] at ht
  exact congrArg (fun z : Additive V => z.toMul.val) ht

omit [Finite G] in
private theorem cover_fusion {Y U Q : Subgroup G}
    (hcover : (L : Set G) = (Y : Set G) * (Q : Set G))
    (hQ : Q ≤ centralizer (U : Set G))
    (ht : ∀ x ∈ U, ∀ y ∈ U, x ≠ 1 → y ≠ 1 → ∃ l ∈ L, l*x*l⁻¹ = y) :
    ∀ x ∈ U, ∀ y ∈ U, x ≠ 1 → y ≠ 1 → ∃ l ∈ Y, l*x*l⁻¹ = y := by
  intro x hx y hy hx1 hy1
  obtain ⟨l,hl,he⟩ := ht x hx y hy hx1 hy1
  obtain ⟨a,ha,q,hq,rfl⟩ := hcover ▸ (show l ∈ (L : Set G) from hl)
  refine ⟨a,ha,?_⟩
  have hc : q*x*q⁻¹ = x := by
    rw [←hQ hq x hx,mul_inv_cancel_right]
  have hh : (a*q)*x*(a*q)⁻¹ = a*x*a⁻¹ := by
    calc
      _ = a*(q*x*q⁻¹)*a⁻¹ := by group
      _ = _ := by rw [hc]
  exact hh.symm.trans he

/-- The actual intersection residual fuses all nonidentity elements of the full module. -/
theorem unitary_original_pushingUp_rudvalis_fusion (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    ∀ x ∈ W, ∀ y ∈ W, x ≠ 1 → y ≠ 1 →
      ∃ l ∈ (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype,
        l*x*l⁻¹ = y := by
  have hfull := unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hVW
  let f := MulAut.conj (c : G)
  have hLc : L.map f.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp c.property.1
  have htrans : ∀ x ∈ W, ∀ y ∈ W, x ≠ 1 → y ≠ 1 → ∃ l ∈ L, l*x*l⁻¹ = y := by
    intro x hx y hy hx1 hy1
    rw [hfull] at hx hy
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    obtain ⟨l,hl,he⟩ := unitary_original_nonzero_fusion s hu hv
      (fun h => hx1 (by rw [h,map_one])) (fun h => hy1 (by rw [h,map_one]))
    refine ⟨f l,hLc ▸ mem_map_of_mem f.toMonoidHom hl,?_⟩
    change f l * f u * (f l)⁻¹ = f v
    simpa only [map_mul,map_inv] using congrArg f he
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  have hyp := source_hypothesis411 h12.toHypothesis1221 hu
  obtain ⟨hYC,_,_⟩ := residual_cover_of_containment hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hcover hJH
  rw [chosen_intersection_twoResidual_eq_solvableResidual h12.toHypothesis1221 hcover hJH] at hYC
  exact cover_fusion hYC (hfull.symm ▸ (unitary_original_conjugate_fixed_points s c).2) htrans

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
