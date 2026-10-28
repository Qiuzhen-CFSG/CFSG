module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions.Defs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions.Commuting
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Contradiction

/-!
# The actual centralizer residual on the moving component span

Restrict the actual plus action to Y_C and then to [W_L,L]. Its commutation
with the marked component action follows from [Y_C,L] ≤ O₂(L) and the
already established trivial action of O₂(L) on W_L. The one-copy cover and
doubled-copy calculations give the required ambient action alternatives,
including the doubled branch's vanishing fixed subgroup. Two-perfectness of
the genuine residual is sufficient; no order-three or S-normalization premise
is used. The source moving-layer classification remains an explicit input.

Source: Aschbacher–Smith, 15.3.23, printed p.1128; B.4.8, pp.91–92.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)
  [(actionKernel d L).Normal] [IsElementaryAbelian 2 (d.componentSpan L)]
  (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G))
  (hcore : L.pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G))
  (e : (L ⧸ pCore 2 L) ≃* SL)

omit [(actionKernel d L).Normal] [IsElementaryAbelian 2 (d.componentSpan L)] in
private theorem residual_le_overgroup : YC d L ≤ overgroup d L :=
  ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left).trans le_sup_right

/-- The action of the actual section centralizer residual on W_L. -/
noncomputable def residualSpanRepresentation :
    Representation (ZMod 2) (YC d L) (Additive (d.componentSpan L)) :=
  (representation d hN).comp ((plusMap d L).comp
    (inclusion (by exact residual_le_overgroup d L)))

/-- The residual action retains literal ambient conjugation. -/
theorem residualSpanRepresentation_apply (y : YC d L) (w : Additive (d.componentSpan L)) :
    ((residualSpanRepresentation d L hN y w).toMul : G) =
      (y : G) * (w.toMul : G) * (y : G)⁻¹ := rfl

/-- The residual commutes with the component on W_L because its section
commutators are in O₂(L), which already centralizes this span. -/
theorem residualSpanRepresentation_commutes (y : YC d L) (g : SL)
    (w : Additive (d.componentSpan L)) :
    residualSpanRepresentation d L hN y (componentRepresentation d L hN hcore e g w) =
      componentRepresentation d L hN hcore e g (residualSpanRepresentation d L hN y w) := by
  obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
  let yy : overgroup d L := inclusion (residual_le_overgroup d L) y
  let ll : overgroup d L := ⟨l, (le_sup_left.trans le_sup_left : L ≤ overgroup d L) l.property⟩
  have hsec : ⁅YC d L,L⁆ ≤ L.pCoreIn 2 :=
    ((Chapter4.le_sectionCentralizer_iff _ L).mp
      ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)).2
  have hk : plusMap d L ⁅yy,ll⁆ = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hcore (hsec (commutator_mem_commutator y.property l.property))
  have hh : Commute (plusMap d L yy) (plusMap d L ll) :=
    commutatorElement_eq_one_iff_commute.mp (by rw [← map_commutatorElement]; exact hk)
  have hc := hh.map (representation d hN)
  have hll : componentRepresentation d L hN hcore e g = representation d hN (plusMap d L ll) := by
    rw [← hl]
    change (representation d hN) ((plusImage d L L).subtype
      (coreQuotientMap d L hcore (e.symm (e (QuotientGroup.mk' _ l))))) = _
    rw [e.symm_apply_apply]
    rfl
  rw [hll]
  exact LinearMap.congr_fun hc.eq w

private theorem moving_preserved (y : YC d L) :
    (moving (componentRepresentation d L hN hcore e)).toSubmodule ≤
      (moving (componentRepresentation d L hN hcore e)).toSubmodule.comap
        (residualSpanRepresentation d L hN y) := by
  rw [moving_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨g,_,w,_,rfl⟩
  change residualSpanRepresentation d L hN y
    (componentRepresentation d L hN hcore e g w - w) ∈
    subspaceCommutator (componentRepresentation d L hN hcore e) ⊤ ⊤
  rw [map_sub, residualSpanRepresentation_commutes]
  exact Submodule.subset_span ⟨g, mem_top _, residualSpanRepresentation d L hN y w,
    Submodule.mem_top, rfl⟩

/-- Restrict the residual action to the literal moving subrepresentation. -/
noncomputable def residualMovingRepresentation :
    Representation (ZMod 2) (YC d L)
      (moving (componentRepresentation d L hN hcore e)).toSubmodule :=
  (show Subrepresentation (residualSpanRepresentation d L hN) from
    { toSubmodule := (moving (componentRepresentation d L hN hcore e)).toSubmodule
      apply_mem_toSubmodule := by
        intro y v hv
        exact moving_preserved d L hN hcore e y hv }).toRepresentation

/-- The two restricted actions commute on the same actual carrier. -/
theorem residualMovingRepresentation_commutes (y : YC d L) (g : SL)
    (w : (moving (componentRepresentation d L hN hcore e)).toSubmodule) :
    residualMovingRepresentation d L hN hcore e y
        ((moving (componentRepresentation d L hN hcore e)).toRepresentation g w) =
      (moving (componentRepresentation d L hN hcore e)).toRepresentation g
        (residualMovingRepresentation d L hN hcore e y w) :=
  Subtype.ext (residualSpanRepresentation_commutes d L hN hcore e y g w)

private theorem moving_mem {w : G} (hw : w ∈ spanCommutator d L) :
    (Additive.ofMul ⟨w, le_normalizer_iff_commutator_le_left.mp
      (le_normalizer_conjugateSpanBy d.V L) hw⟩ : Additive (d.componentSpan L)) ∈
      (moving (componentRepresentation d L hN hcore e)).toSubmodule := by
  rw [moving_eq_spanCommutator]
  exact hw

/-- Trivial linear residual action means the ambient commutator is trivial. -/
theorem ambient_trivial_of_residual_trivial
    (h : ∀ y, residualMovingRepresentation d L hN hcore e y = 1) :
    ⁅spanCommutator d L, YC d L⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro w hw y hy
  let v : (moving (componentRepresentation d L hN hcore e)).toSubmodule :=
    ⟨_, moving_mem d L hN hcore e hw⟩
  have hh := congrArg (fun x : (moving (componentRepresentation d L hN hcore e)).toSubmodule =>
    ((x.val.toMul) : G)) (LinearMap.congr_fun (h ⟨y,hy⟩) v)
  change ((residualSpanRepresentation d L hN ⟨y,hy⟩ v.val).toMul : G) = w at hh
  rw [residualSpanRepresentation_apply] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Linear vanishing of fixed vectors gives the exact ambient fixed subgroup. -/
theorem ambient_fixed_eq_bot
    (h : fixedSpace (residualMovingRepresentation d L hN hcore e) ⊤ = ⊥) :
    spanCommutator d L ⊓ centralizer (YC d L : Set G) = ⊥ := by
  apply le_bot_iff.mp
  rintro w ⟨hw,hc⟩
  let v : (moving (componentRepresentation d L hN hcore e)).toSubmodule :=
    ⟨_, moving_mem d L hN hcore e hw⟩
  have hv : v ∈ fixedSpace (residualMovingRepresentation d L hN hcore e) ⊤ := by
    intro y
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((residualSpanRepresentation d L hN y.val v.val).toMul : G) = w
    rw [residualSpanRepresentation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hc y.val y.val.property)
  have hz : v = 0 := by
    have hv0 := h.le hv
    exact hv0
  exact congrArg (fun x : (moving (componentRepresentation d L hN hcore e)).toSubmodule =>
    ((x.val.toMul) : G)) hz

/-- Full linear displacement gives the actual ambient commutator equality. -/
theorem ambient_full_displacement
    (h : Coinvariants.ker (residualMovingRepresentation d L hN hcore e) = ⊤) :
    ⁅spanCommutator d L, YC d L⁆ = spanCommutator d L := by
  let ρ := componentRepresentation d L hN hcore e
  let σ := residualMovingRepresentation d L hN hcore e
  let H := ⁅spanCommutator d L, YC d L⁆
  let U := (subgroupSpace d L H).comap (moving ρ).toSubmodule.subtype
  have hh : Coinvariants.ker σ ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y,v⟩,rfl⟩
    change ((((residualSpanRepresentation d L hN y v.val - v.val).toMul) : G)) ∈ H
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [residualSpanRepresentation_apply]
    have hv : (v.val.toMul : G) ∈ spanCommutator d L := by
      exact (moving_eq_spanCommutator d L hN hcore e).le v.property
    rw [show H = ⁅YC d L, spanCommutator d L⁆ from commutator_comm _ _]
    exact commutator_mem_commutator y.property hv
  have hn : YC d L ≤ normalizer (spanCommutator d L : Set G) := by
    have hYL : YC d L ≤ normalizer (L : Set G) :=
      ((Chapter4.le_sectionCentralizer_iff _ L).mp
        ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)).1
    intro y hy
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [spanCommutator, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hN (residual_le_overgroup d L hy)),
      mem_normalizer_iff_map_conj_eq.mp (hYL hy)]
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
  intro w hw
  let v : (moving ρ).toSubmodule := ⟨_, moving_mem d L hN hcore e hw⟩
  exact hh (h ▸ Submodule.mem_top (x := v))

/-- Construct the source centralizer-action alternatives from the full moving
structure. Both full displacement and the fixed subgroup are proved. -/
theorem centralizerActionCases_of_movingStructure [Finite G]
    (h : MovingStructure (componentRepresentation d L hN hcore e)) :
    CentralizerActionCases d L hN hcore e := by
  let ρ := componentRepresentation d L hN hcore e
  let σ := residualMovingRepresentation d L hN hcore e
  have hc := residualMovingRepresentation_commutes d L hN hcore e
  have hp := ComponentIntersection.centralizerResidual_isPPerfect d.Yplus L
  cases h with
  | one copies =>
    exact Or.inl (ambient_trivial_of_residual_trivial d L hN hcore e
      (one_quotient_commuting_trivial _ σ hc copies.some.toQuotient (moving_full ρ)))
  | nonsplit q _ =>
    exact Or.inl (ambient_trivial_of_residual_trivial d L hN hcore e
      (one_quotient_commuting_trivial _ σ hc q.some (moving_full ρ)))
  | two copies =>
    by_cases ht : ∀ y, σ y = 1
    · exact Or.inl (ambient_trivial_of_residual_trivial d L hN hcore e ht)
    · exact Or.inr ⟨copies,
        ambient_full_displacement d L hN hcore e (doubled_full_displacement _ σ hc copies.some hp ht),
        ambient_fixed_eq_bot d L hN hcore e (doubled_fixed_eq_bot _ σ hc copies.some hp ht)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
