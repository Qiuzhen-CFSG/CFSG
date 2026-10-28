module
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction.MathieuJanko
public import Theory.GroupTheory.DoubleCoverCentralizer.ActorPreimage
public import Theory.GroupTheory.DoubleCoverCentralizer.Recognition

/-!
# The adequate J₂ actor-preimage lift

The full pointwise fixer of an A₅ representative in J₂ has odd-order elements.
The subgroup used here is instead the preimage of the actual acting four-group
under inner conjugation. No full automorphism-centralizer equality is assumed.
The all-elements component marking and the J₂ involution row make every actor
inner. E1 and the earlier center clause give a center of order two, so this
preimage has order eight. The quotient component calculation excludes 2-central
representatives, and the exact I.2.2(5b) lifting clause makes every noncentral
element have order four. Recognition gives Q₈ and the actor needed for transfer.

Placement of this subgroup in the source Sylow group belongs to the transfer
assembly. Source: Aschbacher–Smith, 16.3.6, printed p.1179 / PDF p.1196;
16.1.2(2), 16.1.5(8), and I.2.2(5b), manuscript of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer ClassificationModels
open TableReduction
variable {G : Type*} [Group G] {E L : Subgroup G} {i : G}

/-- The genuine component, action and model inputs for the adequate J₂ route.
The action image is allowed to be a proper subgroup of the full fixer. -/
structure AdequateJankoEnlargement (E L : Subgroup G) (i : G) : Prop where
  component : IsCentralizerComponent i (Enlargement L i)
  normalizes : E ≤ normalizer (Enlargement L i : Set G)
  faithful : Function.Injective (inducedAction E (Enlargement L i) normalizes)
  elementary : IsElementaryAbelian 2 E
  core_ne : pCore 2 (Enlargement L i) ≠ ⊥
  component_model : Nonempty (L ≃* alternatingGroup (Fin 5))
  quotient_model : Nonempty ((Enlargement L i ⧸ pCore 2 (Enlargement L i)) ≃*
    SporadicName.j2.Carrier)

/-- The actual preimage used in the adequate route, with its given ambient action. -/
abbrev AdequateJankoPreimage (E L : Subgroup G) (i : G)
    (h : AdequateJankoEnlargement E L i) : Subgroup (Enlargement L i) :=
  actorPreimage (inducedAction E (Enlargement L i) h.normalizes)

/-- The ambient all-elements component condition gives pointwise fixation
for any normalizing action; a full-image assumption is unnecessary. -/
theorem actor_fixes_component_of_normalizes
    (hn : E ≤ normalizer (Enlargement L i : Set G))
    (hc : CentralizesAsComponent E L) (e : E) (l : ComponentInside L i) :
    inducedAction E (Enlargement L i) hn e l = l := by
  by_cases he : e = 1
  · simp [he]
  · have hcomp := hc e e.property (fun hh => he (Subtype.ext hh))
    have hm := mem_centralizer_singleton_iff.mp (hcomp.1 l.property)
    change (l : G) * (e : G) = (e : G) * (l : G) at hm
    apply Subtype.ext
    change (e : G) * (l : G) * (e : G)⁻¹ = (l : G)
    rw [← hm]
    group

/-- Restrict the actual ambient component to the fixed subgroup of an actor,
retaining the complete component marking under the weak action input. -/
theorem actor_component_of_normalizes
    (hn : E ≤ normalizer (Enlargement L i : Set G))
    (hc : CentralizesAsComponent E L) (e : E) (he : e ≠ 1) :
    IsComponentIn (ComponentInside L i)
      (inducedAction E (Enlargement L i) hn e).fixedSubgroup := by
  let α := inducedAction E (Enlargement L i) hn
  have hcomp := hc e e.property (fun hh => he (Subtype.ext hh))
  have hle : ComponentInside L i ≤ (α e).fixedSubgroup := by
    intro l hl
    exact (MulAut.mem_fixedSubgroup _ _).mpr
      (actor_fixes_component_of_normalizes hn hc e ⟨l, hl⟩)
  let φ : (α e).fixedSubgroup →* involutionCentralizer (e : G) :=
    { toFun := fun x => ⟨(x : Enlargement L i), by
        apply mem_centralizer_singleton_iff.mpr
        have hx := congrArg (fun y : Enlargement L i => (y : G))
          ((MulAut.mem_fixedSubgroup _ _).mp x.property)
        change (e : G) * (x : G) * (e : G)⁻¹ = (x : G) at hx
        exact ((mul_inv_eq_iff_eq_mul).mp hx).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨hle, ?_, ?_⟩
  · exact hcomp.2.1.comap φ
  · let := hcomp.quasisimple
    let : IsQuasisimple (ComponentInside L i) := IsQuasisimple.of_mulEquiv
      (subgroupOfEquivOfLe (ComponentTransfer.le_layerClosure _ _)).symm
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm

variable [Finite G] {𝒦 : GroupClass}

private theorem adequate_janko_models (hG : Hypothesis1611 𝒦 G)
    (hi : orderOf i = 2) (h : AdequateJankoEnlargement E L i) :
    Nonempty (ComponentInside L i ≃* alternatingGroup (Fin 5)) ∧
      Nonempty ((Enlargement L i ⧸ center (Enlargement L i)) ≃* SporadicName.j2.Carrier) := by
  obtain ⟨eL⟩ := h.component_model
  obtain ⟨eI⟩ := h.quotient_model
  exact ⟨⟨(subgroupOfEquivOfLe (ComponentTransfer.le_layerClosure _ _)).trans eL⟩,
    ⟨(QuotientGroup.quotientMulEquivOfEq
      (hG.evenType.component_center_eq_twoCore hi h.component)).trans eI⟩⟩

omit [Finite G] in
private theorem adequate_janko_actor_order_two
    (h : AdequateJankoEnlargement E L i) (e : E) (he : e ≠ 1) :
    orderOf (inducedAction E (Enlargement L i) h.normalizes e) = 2 := by
  let := h.elementary
  rw [orderOf_injective _ h.faithful]
  apply orderOf_eq_prime _ he
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) e

/-- E1 and the literal center bound make the nontrivial J₂ cover a double cover. -/
theorem adequate_janko_center_card (source : CenterClause (G := G) 𝒦)
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : AdequateJankoEnlargement E L i) : Nat.card (center (Enlargement L i)) = 2 := by
  have hZeq := hG.evenType.component_center_eq_twoCore hi h.component
  have hZne : center (Enlargement L i) ≠ ⊥ := by rw [hZeq]; exact h.core_ne
  have hb := source hG i (Enlargement L i) hi h.component
    (Or.inr (Or.inl (adequate_janko_models hG hi h).2))
  have hn : Nat.card (center (Enlargement L i)) ≠ 1 :=
    fun hh => hZne ((center (Enlargement L i)).eq_bot_iff_card.mpr hh)
  have hp : 0 < Nat.card (center (Enlargement L i)) := Nat.card_pos
  omega

/-- The actual actor image and its conjugation preimage are two-groups.
Only E1 and the order of the actors are needed for this assertion. -/
theorem adequate_janko_preimage_isPGroup (hG : Hypothesis1611 𝒦 G)
    (hi : orderOf i = 2) (h : AdequateJankoEnlargement E L i)
    (hcard : Nat.card E = 4) :
    IsPGroup 2 (inducedAction E (Enlargement L i) h.normalizes).range ∧
      IsPGroup 2 (AdequateJankoPreimage E L i h) := by
  let α := inducedAction E (Enlargement L i) h.normalizes
  have hE : IsPGroup 2 E := IsPGroup.of_card (n := 2) hcard
  have hZ : IsPGroup 2 (center (Enlargement L i)) := by
    rw [hG.evenType.component_center_eq_twoCore hi h.component]
    exact pCore_isPGroup
  exact ⟨hE.of_surjective α.rangeRestrict α.rangeRestrict_surjective,
    actorPreimage_isPGroup α hE hZ⟩

/-- The all-elements component marking excludes the outer J₂ row for every
actor. This does not assert that the full component fixer is a two-group. -/
theorem adequate_janko_innerActors_eq_top (tables : InvolutionTables)
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : AdequateJankoEnlargement E L i) (hc : CentralizesAsComponent E L) :
    innerActors (inducedAction E (Enlargement L i) h.normalizes) = ⊤ := by
  let := h.component.quasisimple
  obtain ⟨eJ, ⟨eI⟩⟩ := adequate_janko_models hG hi h
  apply top_unique
  intro e _
  by_cases he : e = 1
  · subst e
    exact (innerActors _).one_mem
  · obtain ⟨f, hf⟩ := j2_inner_of_component tables (ComponentInside L i)
      (inducedAction E (Enlargement L i) h.normalizes e)
      (adequate_janko_actor_order_two h e he)
      (actor_component_of_normalizes h.normalizes hc e he) eJ eI
    exact ⟨f, hf.symm⟩

/-- The actual component marking excludes 2-central representatives of the
inner actor image on the quotient by the center. -/
theorem adequate_janko_non_two_central (hG : Hypothesis1611 𝒦 G)
    (hi : orderOf i = 2) (h : AdequateJankoEnlargement E L i)
    (hc : CentralizesAsComponent E L) (f : Enlargement L i)
    (hf2 : orderOf (QuotientGroup.mk' (center (Enlargement L i)) f) = 2)
    (hf : f ∈ AdequateJankoPreimage E L i h) :
    ¬ TwoCentral (QuotientGroup.mk' (center (Enlargement L i)) f) := by
  let := h.component.quasisimple
  obtain ⟨e, he⟩ := hf
  have he1 : e ≠ 1 := by
    intro he1
    have hconj : MulAut.conj f = 1 := by simpa only [he1, map_one] using he.symm
    have hfZ : f ∈ center (Enlargement L i) := by rw [← conj_kernel]; exact hconj
    have hqone : QuotientGroup.mk' (center (Enlargement L i)) f = 1 :=
      (QuotientGroup.eq_one_iff f).mpr hfZ
    rw [hqone, orderOf_one] at hf2
    norm_num at hf2
  obtain ⟨eJ, ⟨eI⟩⟩ := adequate_janko_models hG hi h
  exact j2_not_twoCentral_of_component (ComponentInside L i)
    (inducedAction E (Enlargement L i) h.normalizes e)
    (adequate_janko_actor_order_two h e he1)
    (actor_component_of_normalizes h.normalizes hc e he1) eJ eI f he.symm hf2

/-- The adequate J₂ lift: the actual actor preimage is a quaternion
two-subgroup centralizing L, and contains an order-four representative of a
nonidentity actor. No Sylow placement or full-image equality is assumed. -/
theorem adequate_janko_cover_lifts (source : CenterClause (G := G) 𝒦)
    (tables : InvolutionTables) (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : AdequateJankoEnlargement E L i) (hcard : Nat.card E = 4)
    (hc : CentralizesAsComponent E L)
    (hlift : NonTwoCentralInvolutionLifting (Enlargement L i)) :
    IsPGroup 2 (AdequateJankoPreimage E L i h) ∧
    AdequateJankoPreimage E L i h ≤ ComponentCentralizer L i ∧
    Nat.card (center (Enlargement L i)) = 2 ∧
    Nonempty (AdequateJankoPreimage E L i h ≃* QuaternionGroup 2) ∧
    ∃ e : E, e ≠ 1 ∧ ∃ f : Enlargement L i,
      f ∈ AdequateJankoPreimage E L i h ∧
      (f : G) ∈ centralizer (L : Set G) ∧ orderOf f = 4 ∧
      f ^ 2 ∈ center (Enlargement L i) ∧
      inducedAction E (Enlargement L i) h.normalizes e = MulAut.conj f := by
  classical
  let I := Enlargement L i
  let α := inducedAction E I h.normalizes
  let D := AdequateJankoPreimage E L i h
  let := h.elementary
  have hZ : Nat.card (center I) = 2 := adequate_janko_center_card source hG hi h
  have hb : innerActors α = ⊤ := adequate_janko_innerActors_eq_top tables hG hi h hc
  have hbcard : Nat.card (innerActors α) = 4 := by
    rw [hb, Nat.card_congr Subgroup.topEquiv.toEquiv, hcard]
  have hDcard : Nat.card D = 8 := by
    rw [actorPreimage_card α h.faithful, hZ, hbcard]
  have hDC : D ≤ ComponentCentralizer L i :=
    actorPreimage_le_centralizer (ComponentInside L i) α
      (actor_fixes_component_of_normalizes h.normalizes hc)
  have ha2 (e : E) : (α e) ^ 2 = 1 := by
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) e, map_one]
  have horder (f : I) (hf : f ∈ D) (hz : f ∉ center I) :
      orderOf (QuotientGroup.mk' (center I) f) = 2 := by
    obtain ⟨e, he⟩ := hf
    have hn : MulAut.conj f ≠ 1 := by
      intro hh
      exact hz ((conj_kernel (H := I)) ▸
        (show f ∈ (MulAut.conj : I →* MulAut I).ker from hh))
    have ho : orderOf (MulAut.conj f) = 2 := orderOf_eq_prime (he ▸ ha2 e) hn
    exact (orderOf_injective quotientConj quotientConj_injective _).symm.trans ho
  have hfour (f : D) (hz : (f : I) ∉ center I) : orderOf f = 4 := by
    rw [← orderOf_coe]
    exact order_four_of_marked_coset hZ hlift f (horder f f.property hz)
      (adequate_janko_non_two_central hG hi h hc f (horder f f.property hz) f.property)
  have hQ : Nonempty (D ≃* QuaternionGroup 2) := by
    rcases centralizer_shape D (center_le_actorPreimage α) hZ (Or.inr hDcard) hfour with
      hq | ⟨h4, _⟩
    · exact hq
    · omega
  refine ⟨(adequate_janko_preimage_isPGroup hG hi h hcard).2, hDC, hZ, hQ, ?_⟩
  obtain ⟨e, he, f, hf⟩ := exists_inner_actor α hcard (by rw [hb, index_top]; decide)
  have hfD : f ∈ D := ⟨e, hf⟩
  have hfZ : f ∉ center I := by
    intro hz
    have hh : α e = α 1 := by
      rw [map_one, hf]
      exact (show f ∈ (MulAut.conj : I →* MulAut I).ker from
        (conj_kernel (H := I)).symm ▸ hz)
    exact he (h.faithful hh)
  refine ⟨e, he, f, hfD, ?_, ?_, ?_, hf⟩
  · intro l hl
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hDC hfD)
      ⟨l, ComponentTransfer.le_layerClosure _ _ hl⟩ hl)
  · exact (orderOf_coe (⟨f, hfD⟩ : D)).trans (hfour ⟨f, hfD⟩ hfZ)
  · apply (QuotientGroup.eq_one_iff (f ^ 2)).mp
    change QuotientGroup.mk' (center I) (f ^ 2) = 1
    rw [map_pow, ← horder f hfD hfZ, pow_orderOf_eq_one]

end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts
