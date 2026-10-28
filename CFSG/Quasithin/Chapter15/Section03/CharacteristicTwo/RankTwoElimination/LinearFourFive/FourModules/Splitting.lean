module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Projection
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality


/-!
# Splitting the component span in the natural alternatives

For U = [W_L,L], conjugation on W_L descends through the actual quotient
L/O₂(L), using O₂(L) ≤ R ≤ C_G(V). Every vector of W_L gives a displacement
cocycle with coefficients in U. The checked natural SL₄(2) cohomology
calculation, applied separately to every natural summand, makes this cocycle
principal. Inverse transpose and the dot-product pairing give the same
calculation for the contragredient summand. Thus both actual module
alternatives imply W_L = U C_{W_L}(L).

Restricting this splitting to UZ gives precisely UZ = U C_{UZ}(L). The
central factor is retained throughout. The resulting projection preserves
the relative centralizer of Z. These results do not construct the module
alternatives, the plane parabolic, or the repeated-natural residual geometry.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.24,
printed p.1129 (PDF p.1146); I.1.5–I.1.6(6), printed p.408 (PDF p.419).
The displayed splitting also follows in the source from B.2.14; here it is
proved directly from the module alternatives and checked first cohomology.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open scoped Pointwise
open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules
private theorem graph_pairing (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (x : Space 4) :
    dotProductEquiv (ZMod 2) (Fin 4) (specialLinearNatural 4 g x) =
      (specialLinearNatural (k := ZMod 2) 4).dual (graphSL 4 g)
        (dotProductEquiv (ZMod 2) (Fin 4) x) := by
  apply LinearMap.ext
  intro y
  have hs : graphLinear 4 (slEquivLinear 4 (graphSL 4 g)) = slEquivLinear 4 g := by
    rw [graphLinear_slEquivLinear]
    change slEquivLinear 4 (graphSL 4 (graphSL 4 g)) = _
    exact congrArg (slEquivLinear 4) (MulEquiv.congr_fun (graphSL_sq 4) g)
  have he := graphLinear_dotProduct (slEquivLinear 4 (graphSL 4 g)) x
    ((slEquivLinear 4 (graphSL 4 g)).symm y)
  rw [hs, LinearEquiv.apply_symm_apply] at he
  exact he

private theorem dual_principal
    (f : cocycles (specialLinearNatural (k := ZMod 2) 4).dual) :
    ∃ v, f = principal (specialLinearNatural (k := ZMod 2) 4).dual v := by
  let e := cocyclesCongr (specialLinearNatural (k := ZMod 2) 4)
    (specialLinearNatural (k := ZMod 2) 4).dual (graphSL 4)
    (dotProductEquiv (ZMod 2) (Fin 4)) graph_pairing
  obtain ⟨v, hv⟩ := SLHigherNatural.exists_principal_of_four_le (by decide) (e.symm f)
  refine ⟨dotProductEquiv (ZMod 2) (Fin 4) v, ?_⟩
  have he := congrArg e hv
  rw [e.apply_symm_apply] at he
  exact he.trans (cocyclesCongr_principal _ _ _ _ graph_pairing v)

variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)

private def spanAction : L →* MulAut (d.componentSpan L) :=
  (d.componentSpan L).normalizerMonoidHom.comp
    (inclusion (le_normalizer_conjugateSpanBy d.V L))

private theorem core_le_spanAction_ker
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G)) :
    pCore 2 L ≤ (spanAction d L).ker := by
  rw [spanAction, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  intro l hl
  exact core_centralizes_span d L hcore hR (mem_map.mpr ⟨l, hl, rfl⟩)

private def spanQuotientAction
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G)) :
    (L ⧸ pCore 2 L) →* MulAut (d.componentSpan L) :=
  QuotientGroup.lift (pCore 2 L) (spanAction d L) (core_le_spanAction_ker d L hcore hR)

variable {d L}
variable (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))

private def displacement (w : d.componentSpan L) (q : L ⧸ pCore 2 L) :
    spanCommutator d L :=
  ⟨(spanQuotientAction d L hcore hR q w : G) * (w : G)⁻¹, by
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    change (l : G) * (w : G) * (l : G)⁻¹ * (w : G)⁻¹ ∈ _
    rw [spanCommutator, commutator_comm]
    exact commutator_mem_commutator l.property w.property⟩

private theorem displacement_mul (w : d.componentSpan L) (q t : L ⧸ pCore 2 L) :
    displacement hcore hR w (q * t) =
      commutatorQuotientAction d L hcore hR q (displacement hcore hR w t) *
        displacement hcore hR w q := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) t
  rw [← map_mul]
  apply Subtype.ext
  change ((l : G) * k) * w * ((l : G) * k)⁻¹ * (w : G)⁻¹ =
    ((l : G) * ((k : G) * w * (k : G)⁻¹ * (w : G)⁻¹) * (l : G)⁻¹) *
      ((l : G) * w * (l : G)⁻¹ * (w : G)⁻¹)
  group

private theorem repeated_quotient_equivariant {r : ℕ} (h : RepeatedNatural d L r)
    (q : L ⧸ pCore 2 L) (u : spanCommutator d L) (i : Fin r) :
    (h.coordinates (commutatorQuotientAction d L hcore hR q u)).toAdd i =
      projectiveEquivLinear (by decide) (h.model q) ((h.coordinates u).toAdd i) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  exact h.equivariant l u i

private def repeatedCocycle {r : ℕ} (h : RepeatedNatural d L r)
    (w : d.componentSpan L) (i : Fin r) :
    cocycles (specialLinearNatural (k := ZMod 2) 4) :=
  ⟨fun g => (h.coordinates (displacement hcore hR w
      (h.model.symm (QuotientGroup.mk' _ g)))).toAdd i, by
    intro g t
    simp only [map_mul, displacement_mul, toAdd_mul, Pi.add_apply,
      repeated_quotient_equivariant, MulEquiv.apply_symm_apply,
      QuotientGroup.mk'_apply, projectiveEquivLinear_mk]
    rfl⟩

include hcore hR in
private theorem span_split_of_displacement
    (h : ∀ w : d.componentSpan L, ∃ u : spanCommutator d L, ∀ l : L,
      commutatorAction d L l u * u⁻¹ =
        displacement hcore hR w (QuotientGroup.mk' _ l)) :
    d.componentSpan L = spanCommutator d L ⊔
      (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨u, hu⟩ := h ⟨w, hw⟩
    have hc : (u : G)⁻¹ * w ∈ d.componentSpan L ⊓ centralizer (L : Set G) := by
      refine ⟨(d.componentSpan L).mul_mem
        ((d.componentSpan L).inv_mem (spanCommutator_le_span d L u.property)) hw, ?_⟩
      intro l hl
      have he := congrArg Subtype.val (hu ⟨l, hl⟩)
      change l * (u : G) * l⁻¹ * (u : G)⁻¹ = l * w * l⁻¹ * w⁻¹ at he
      have hf : l * ((u : G)⁻¹ * w) * l⁻¹ = (u : G)⁻¹ * w := by
        calc
          l * ((u : G)⁻¹ * w) * l⁻¹ =
              (u : G)⁻¹ * (l * (u : G) * l⁻¹ * (u : G)⁻¹)⁻¹ *
                (l * w * l⁻¹ * w⁻¹) * w := by group
          _ = (u : G)⁻¹ * w := by rw [he]; group
      exact mul_inv_eq_iff_eq_mul.mp hf
    have hm := (spanCommutator d L ⊔
      (d.componentSpan L ⊓ centralizer (L : Set G))).mul_mem
      (mem_sup_left u.property) (mem_sup_right hc)
    simpa only [mul_inv_cancel_left] using hm
  · exact sup_le (spanCommutator_le_span d L) inf_le_left


include hcore hR in
/-- I.1.6(6) splits the extension of every repeated natural module by a
trivial module. The fixed subgroup of the whole span is retained. -/
theorem repeated_span_split {r : ℕ} (h : RepeatedNatural d L r) :
    d.componentSpan L = spanCommutator d L ⊔
      (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  classical
  apply span_split_of_displacement hcore hR
  intro w'
  have hv : ∀ i : Fin r, ∃ v : Space 4,
      repeatedCocycle hcore hR h w' i = principal (specialLinearNatural 4) v :=
    fun i => SLHigherNatural.exists_principal_of_four_le (by decide)
      (repeatedCocycle hcore hR h w' i)
  choose v hv using hv
  let u : spanCommutator d L := h.coordinates.symm (Multiplicative.ofAdd v)
  have hcu : h.coordinates u = Multiplicative.ofAdd v := h.coordinates.apply_symm_apply _
  have hu (l : L) :
      commutatorAction d L l u * u⁻¹ =
        displacement hcore hR w' (QuotientGroup.mk' _ l) := by
    apply h.coordinates.injective
    apply Multiplicative.toAdd.injective
    funext i
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      (center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
      (h.model (QuotientGroup.mk' _ l))
    have he := congrArg (fun f : cocycles (specialLinearNatural (k := ZMod 2) 4) =>
      f.val g) (hv i)
    change (h.coordinates (displacement hcore hR w'
      (h.model.symm (QuotientGroup.mk' _ g)))).toAdd i =
        specialLinearNatural 4 g (v i) - v i at he
    rw [hg, MulEquiv.symm_apply_apply] at he
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      Pi.add_apply, Pi.neg_apply, h.equivariant, hcu, toAdd_ofAdd]
    change linearAction (by decide) h.model l (v i) + -(v i) = _
    rw [he]
    rw [sub_eq_add_neg]
    apply congrArg (fun z : Space 4 => z + -v i)
    change projectiveEquivLinear (by decide)
      (h.model (QuotientGroup.mk' _ l)) (v i) = _
    rw [← hg, QuotientGroup.mk'_apply, projectiveEquivLinear_mk]
    rfl
  exact ⟨u, hu⟩

private theorem naturalDual_action_sl
    (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (v : Space 4 × Module.Dual (ZMod 2) (Space 4)) :
    BinaryLinear.NaturalDualFlag.action (slEquivLinear 4 g) v =
      ((specialLinearNatural 4).prod (specialLinearNatural 4).dual) g v := by
  apply Prod.ext
  · exact BinaryLinear.NaturalDualFlag.action_fst _ _
  · apply LinearMap.ext
    intro x
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    change v.2 ((slEquivLinear 4 g)⁻¹ x) = v.2 (specialLinearNatural 4 g⁻¹ x)
    rw [← map_inv]
    rfl

private theorem naturalDual_quotient_equivariant (h : NaturalDual d L)
    (q : L ⧸ pCore 2 L) (u : spanCommutator d L) :
    (h.coordinates (commutatorQuotientAction d L hcore hR q u)).toAdd =
      BinaryLinear.NaturalDualFlag.action (projectiveEquivLinear (by decide) (h.model q))
        (h.coordinates u).toAdd := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  exact h.equivariant l u

private def naturalDualCocycle (h : NaturalDual d L) (w : d.componentSpan L) :
    cocycles ((specialLinearNatural (k := ZMod 2) 4).prod
      (specialLinearNatural (k := ZMod 2) 4).dual) :=
  ⟨fun g => (h.coordinates (displacement hcore hR w
      (h.model.symm (QuotientGroup.mk' _ g)))).toAdd, by
    intro g t
    simp only [map_mul, displacement_mul, toAdd_mul,
      naturalDual_quotient_equivariant, MulEquiv.apply_symm_apply,
      QuotientGroup.mk'_apply, projectiveEquivLinear_mk, naturalDual_action_sl]⟩

private theorem naturalDual_principal
    (f : cocycles ((specialLinearNatural (k := ZMod 2) 4).prod
      (specialLinearNatural (k := ZMod 2) 4).dual)) :
    ∃ v, f = principal ((specialLinearNatural (k := ZMod 2) 4).prod
      (specialLinearNatural (k := ZMod 2) 4).dual) v := by
  let f₁ : cocycles (specialLinearNatural (k := ZMod 2) 4) :=
    ⟨fun g => (f.val g).1, fun g t => congrArg Prod.fst (f.property g t)⟩
  let f₂ : cocycles (specialLinearNatural (k := ZMod 2) 4).dual :=
    ⟨fun g => (f.val g).2, fun g t => congrArg Prod.snd (f.property g t)⟩
  obtain ⟨v₁, h₁⟩ := SLHigherNatural.exists_principal_of_four_le (by decide) f₁
  obtain ⟨v₂, h₂⟩ := dual_principal f₂
  refine ⟨(v₁, v₂), ?_⟩
  apply Subtype.ext
  funext g
  exact Prod.ext (congrArg (fun c => c.val g) h₁) (congrArg (fun c => c.val g) h₂)

include hcore hR in
/-- The natural and contragredient H¹ calculations also split the whole span
in the remaining alternative, without discarding its central factor. -/
theorem naturalDual_span_split (h : NaturalDual d L) :
    d.componentSpan L = spanCommutator d L ⊔
      (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  classical
  apply span_split_of_displacement hcore hR
  intro w
  obtain ⟨v, hv⟩ := naturalDual_principal (naturalDualCocycle hcore hR h w)
  let u : spanCommutator d L := h.coordinates.symm (Multiplicative.ofAdd v)
  have hcu : h.coordinates u = Multiplicative.ofAdd v := h.coordinates.apply_symm_apply _
  refine ⟨u, ?_⟩
  intro l
  apply h.coordinates.injective
  apply Multiplicative.toAdd.injective
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (h.model (QuotientGroup.mk' _ l))
  have he := congrArg (fun f : cocycles ((specialLinearNatural (k := ZMod 2) 4).prod
    (specialLinearNatural (k := ZMod 2) 4).dual) => f.val g) hv
  change (h.coordinates (displacement hcore hR w
    (h.model.symm (QuotientGroup.mk' _ g)))).toAdd =
      ((specialLinearNatural 4).prod (specialLinearNatural 4).dual) g v - v at he
  rw [hg, MulEquiv.symm_apply_apply] at he
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, h.equivariant, hcu, toAdd_ofAdd]
  rw [he, sub_eq_add_neg]
  apply congrArg (fun z => z + -v)
  change BinaryLinear.NaturalDualFlag.action
    (projectiveEquivLinear (by decide) (h.model (QuotientGroup.mk' _ l))) v = _
  rw [← hg, QuotientGroup.mk'_apply, projectiveEquivLinear_mk]
  exact naturalDual_action_sl g v

include hcore hR in
/-- Both genuine module alternatives yield the extension splitting used on
p.1129. Neither alternative's existence is asserted by this theorem. -/
theorem alternatives_span_split (h : ModuleAlternatives d L) :
    d.componentSpan L = spanCommutator d L ⊔
      (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  rcases h with h | h
  · obtain ⟨r, _, _, ⟨h⟩⟩ := h
    exact repeated_span_split hcore hR h
  · exact h.elim fun h => naturalDual_span_split hcore hR h

/-- Restricting the split span to U_L Z keeps precisely C_{U_L Z}(L).
This supplies the displayed splitting in 15.3.24 from the extension calculation. -/
theorem centralSupplement_split_of_span_split [IsElementaryAbelian 2 (d.componentSpan L)]
    (hsplit : d.componentSpan L = spanCommutator d L ⊔
      (d.componentSpan L ⊓ centralizer (L : Set G))) :
    spanCommutator d L ⊔ d.Z = spanCommutator d L ⊔ centralSupplement d L := by
  have hUW := spanCommutator_le_span d L
  have hZW : d.Z ≤ d.componentSpan L :=
    (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy d.V L)
  have hnorm : d.componentSpan L ⊓ centralizer (L : Set G) ≤
      normalizer (spanCommutator d L : Set G) :=
    (inf_le_left.trans ((d.componentSpan L).le_centralizer.trans
      (centralizer_le hUW))).trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · apply sup_le le_sup_left
    intro z hz
    have hp : z ∈ (spanCommutator d L : Set G) *
        ((d.componentSpan L ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
      exact hsplit ▸ hZW hz
    obtain ⟨u, hu, c, hc, rfl⟩ := hp
    have hcs : c ∈ centralSupplement d L :=
      ⟨(mul_mem_cancel_left (mem_sup_left hu)).mp (mem_sup_right hz), hc.2⟩
    exact mul_mem_sup hu hcs
  · exact sup_le le_sup_left inf_le_left

include hcore hR in
/-- The displayed B.2.14 splitting is proved from the actual alternatives and
checked H¹ vanishing; no local splitting witness is assumed. -/
theorem alternatives_centralSupplement_split [IsElementaryAbelian 2 (d.componentSpan L)]
    (h : ModuleAlternatives d L) :
    spanCommutator d L ⊔ d.Z = spanCommutator d L ⊔ centralSupplement d L :=
  centralSupplement_split_of_span_split (alternatives_span_split hcore hR h)

include hcore hR in
/-- The source projection of Z is now available without an assumed
B.2.14 splitting, and its supplement stays inside the larger central module. -/
theorem alternatives_center_le_projected_sup
    [IsElementaryAbelian 2 (d.componentSpan L)] (h : ModuleAlternatives d L) :
    d.Z ≤ projectedCenter d L ⊔ (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  have hZW : d.Z ≤ d.componentSpan L :=
    (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy d.V L)
  have hC : centralSupplement d L ≤ d.componentSpan L ⊓ centralizer (L : Set G) :=
    le_inf (inf_le_left.trans (sup_le (spanCommutator_le_span d L) hZW)) inf_le_right
  exact (center_le_projected_sup d L
    (alternatives_centralSupplement_split hcore hR h)).trans (sup_le_sup_left hC _)

include hcore hR in
/-- Projecting Z along the proved central supplement preserves its actual
relative centralizer in L. -/
theorem alternatives_projectedCenter_centralizer
    [IsElementaryAbelian 2 (d.componentSpan L)] (h : ModuleAlternatives d L) :
    L ⊓ centralizer (projectedCenter d L : Set G) = L ⊓ centralizer (d.Z : Set G) :=
  projectedCenter_centralizer d L (alternatives_centralSupplement_split hcore hR h)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules

end
