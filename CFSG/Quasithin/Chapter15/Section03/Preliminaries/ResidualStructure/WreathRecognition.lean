module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.WreathRecognition.Centralizer
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.WreathRecognition.ResidualModel
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms

/-!
# The wreath recognition argument for 15.3.9

The contrary equality `V = O₂(Y)` makes `C_Y(V) = V` by inheritance of
characteristic two. The actual residual image from 15.3.7 then recognizes
`Y` as `A₄ × A₄`: Hall splitting and the natural coordinate action identify
its two affine factors. Conversely, an actual alternating-pair model forces
the core equality by transport of its order sixteen.

The Sylow omega-center and characteristic two eliminate `C_M(Y)`, since
`Y` is centerless and contains `Ω₁(Z(T))`. This argument only needs that
containment, so the source's order-two hypothesis on `Ω₁(Z(T))` is unnecessary
here. Conjugation now embeds `M` in the proved automorphism group
`Aut(A₄ × A₄) ≃ S₄ ≀ᵣ C₂`. The natural action forces
`|M| ≥ 16 · 72 = 1152`, making the embedding surjective. Thus both contrary
branches construct the literal wreath model without assuming faithfulness,
full image, splitting, or an automorphism identification.

`residualY_exclusions` gives both conclusions of 15.3.9 from the genuine
earlier action and core-containment inputs and the exact 13.9.1 exclusion.
The source assembly remains responsible for those earlier inputs. The older
APIs with an explicit automorphism equivalence are preserved; the new
recognition and exclusion results discharge that model premise internally.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.9, printed p.1123 (PDF p.1140).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.WreathRecognition
variable {G : Type*} [Group G] [Finite G]

/-- An actual alternating-pair model proves the equality branch by core order. -/
public theorem module_eq_core_of_alternatingPair
    (M Y V : Subgroup G) (d : NaturalOrthogonalAction M V)
    (hV : V ≤ Y.pCoreIn 2) (e : Y ≃* AlternatingFourPair.Model) :
    V = Y.pCoreIn 2 := by
  have hcard : Nat.card (Y.pCoreIn 2) = 16 := by
    change Nat.card ((pCore 2 Y).map Y.subtype) = 16
    rw [card_map_of_injective Y.subtype_injective,
      ← card_map_of_injective (K := pCore 2 Y) (f := e.toMonoidHom) e.injective,
      pCore_map_iso, AlternatingFourPair.card_twoCore]
  exact eq_of_le_of_card_ge hV (by rw [d.card_vector, hcard])

/-- The literal natural orthogonal actor has order 72. -/
public theorem orthogonalActor_card : Nat.card OrthogonalActor = 72 := by
  rw [RegularWreathProduct.card]
  have hs : Nat.card OrthogonalPlaneActor = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hs]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

/-- The natural action and the order-sixteen subgroup of its kernel force the lower bound. -/
public theorem local_card_lower_bound (M V : Subgroup G)
    (d : NaturalOrthogonalAction M V) (hVM : V ≤ M) : 1152 ≤ Nat.card M := by
  have hVk : V.subgroupOf M ≤ d.actor.ker := by
    rw [d.ker_actor]
    intro v hv w hw
    have he : (⟨w, hw⟩ : V) * ⟨v, hv⟩ = ⟨v, hv⟩ * ⟨w, hw⟩ :=
      d.coordinates.injective (by simp only [map_mul, mul_comm])
    exact congrArg V.subtype he
  have hVkcard : 16 ≤ Nat.card d.actor.ker := by
    have h := card_le_of_le hVk
    rw [Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv, d.card_vector] at h
    exact h
  have hidx : d.actor.ker.index = 72 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr d.onto, card_top, orthogonalActor_card]
  calc
    1152 = 16 * 72 := rfl
    _ ≤ Nat.card d.actor.ker * 72 := Nat.mul_le_mul_right _ hVkcard
    _ = Nat.card M := by simpa only [hidx] using d.actor.ker.card_mul_index

omit [Finite G] in
private theorem normalizer_action_injective
    (M Y : Subgroup G) (hn : M ≤ normalizer (Y : Set G))
    (hc : M ⊓ centralizer (Y : Set G) = ⊥) :
    Function.Injective (Y.normalizerMonoidHom.comp (Subgroup.inclusion hn)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro m hm
  have hmC : (m : G) ∈ centralizer (Y : Set G) := by
    change Y.normalizerMonoidHom (Subgroup.inclusion hn m) = 1 at hm
    change Subgroup.inclusion hn m ∈ Y.normalizerMonoidHom.ker at hm
    rw [normalizerMonoidHom_ker] at hm
    exact hm
  have he : (m : G) = 1 := by
    have : (m : G) ∈ M ⊓ centralizer (Y : Set G) := ⟨m.property, hmC⟩
    simpa only [hc, mem_bot] using this
  exact mem_bot.mpr (Subtype.ext he)

/-- Construct the actual equivalence from conjugation, deriving both injectivity
and surjectivity. The intrinsic automorphism equivalence is still a model input. -/
public noncomputable def wreathEquiv_of_alternatingPair
    (M Y V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hn : (Y.subgroupOf M).Normal) (d : NaturalOrthogonalAction M V)
    (hVM : V ≤ M) (hZY : centralInvolutions T ≤ Y)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (eY : Y ≃* AlternatingFourPair.Model)
    (eAut : MulAut AlternatingFourPair.Model ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))) :
    M ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)) := by
  have hz : center Y = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr eY).toEquiv, AlternatingFourPair.center_eq_bot, card_bot]
  have hcY := centralizer_eq_bot_of_center_eq_bot M Y T hTM hYM hn hc hZY hz
  let ι := Subgroup.inclusion ((normal_subgroupOf_iff_le_normalizer hYM).mp hn)
  let f := Y.normalizerMonoidHom.comp ι
  have hf : Function.Injective f := normalizer_action_injective M Y _ hcY
  let g := eAut.toMonoidHom.comp ((MulAut.congr eY).toMonoidHom.comp f)
  have hg : Function.Injective g := eAut.injective.comp ((MulAut.congr eY).injective.comp hf)
  apply MulEquiv.ofBijective g
  apply hg.bijective_of_nat_card_le
  rw [AlternatingFourPair.symmetric_wreath_card]
  exact local_card_lower_bound M V d hVM

/-- The residual model implies the actual wreath model, conditional only on the intrinsic automorphism identification. -/
public theorem residualY_wreath_of_alternatingPair
    (M Mc : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M (localModule T M))
    (hVY : localModule T M ≤ (residualY M Mc).pCoreIn 2)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hY : Nonempty (residualY M Mc ≃* AlternatingFourPair.Model))
    (eAut : MulAut AlternatingFourPair.Model ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))) :
    Nonempty (M ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))) := by
  obtain ⟨eY⟩ := hY
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hVY' := hVY.trans (pCoreIn_le 2 (residualY M Mc))
  exact ⟨wreathEquiv_of_alternatingPair M (residualY M Mc) (localModule T M) T
    hTM hYM (residualY_normal M Mc) d (hVY'.trans hYM)
    ((le_conjugateSpanBy _ _).trans hVY') hc eY eAut⟩

/-- The exact 13.9.1 exclusion rules out the alternating-pair residual once its intrinsic automorphism group is identified. -/
public theorem residualY_not_alternatingPair_of_not_wreath
    (M Mc : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M (localModule T M))
    (hVY : localModule T M ≤ (residualY M Mc).pCoreIn 2)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (eAut : MulAut AlternatingFourPair.Model ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)))
    (hexclude : ¬ Nonempty (M ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)))) :
    ¬ Nonempty (residualY M Mc ≃* AlternatingFourPair.Model) := by
  intro hY
  exact hexclude (residualY_wreath_of_alternatingPair M Mc T hTM d hVY hc hY eAut)

/-- The core-equality branch is the actual alternating pair. The kernel
equality follows from characteristic two; the image equality is from 15.3.7. -/
public theorem alternatingPair_of_core_eq
    (M Y V : Subgroup G) (d : NaturalOrthogonalAction M V)
    (hYM : Y ≤ M) (hn : (Y.subgroupOf M).Normal)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (himage : (Y.subgroupOf M).map d.actor =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hV : V = Y.pCoreIn 2) :
    Nonempty (Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  exact residual_model_of_natural_action d hYM
    (hV.le.trans (pCoreIn_le 2 Y))
    (module_centralizer_eq_of_core_eq M Y V hYM hn d hc hV) himage

/-- Construct the literal wreath equivalence in the contrary branch of
15.3.9. Normality, the residual model, and the full automorphism action
are all proved; only the genuine earlier action-image input is retained. -/
public noncomputable def residualY_wreathEquiv_of_core_eq
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hVlocal : V = localModule T M)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hVcore : V = (residualY M Mc).pCoreIn 2) :
    M ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)) := by
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hn := residualY_normal M Mc
  have hVY := hVcore.le.trans (pCoreIn_le 2 (residualY M Mc))
  have hZY : centralInvolutions T ≤ residualY M Mc := by
    apply le_trans (le_conjugateSpanBy _ _)
    exact hVlocal ▸ hVY
  let eY := Classical.choice (alternatingPair_of_core_eq
    M (residualY M Mc) V d hYM hn hc himage hVcore)
  exact wreathEquiv_of_alternatingPair M (residualY M Mc) V T hTM hYM hn d
    (hVY.trans hYM) hZY hc eY AlternatingFourPair.mulAut_equiv_regularWreath

/-- The second contrary branch also gives an actual wreath model, with no
assumed automorphism identification or equivalence of the two branches. -/
public theorem residualY_wreath_of_pair_model
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hVlocal : V = localModule T M)
    (hVY : V ≤ (residualY M Mc).pCoreIn 2)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hY : Nonempty (residualY M Mc ≃*
      (alternatingGroup (Fin 4) × alternatingGroup (Fin 4)))) :
    Nonempty (M ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))) := by
  subst V
  exact residualY_wreath_of_alternatingPair M Mc T hTM d hVY hc hY
    AlternatingFourPair.mulAut_equiv_regularWreath

/-- Justify the source's equivalence of contrary branches by two independent
arguments: compatible affine recognition and transport of the core order. -/
public theorem residualY_core_eq_iff_pair_model
    (M Mc V : Subgroup G) (d : NaturalOrthogonalAction M V)
    (hVY : V ≤ (residualY M Mc).pCoreIn 2)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    V = (residualY M Mc).pCoreIn 2 ↔
      Nonempty (residualY M Mc ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  constructor
  · exact alternatingPair_of_core_eq M (residualY M Mc) V d
      (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) (residualY_normal M Mc) hc himage
  · rintro ⟨eY⟩
    exact module_eq_core_of_alternatingPair M (residualY M Mc) V d hVY eY

/-- Both conclusions of 15.3.9, conditional on the genuine earlier inputs
and the exact wreath exclusion of 13.9.1. No model or faithfulness premise
remains to be discharged in this recognition step. -/
public theorem residualY_exclusions
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hVlocal : V = localModule T M)
    (hVY : V ≤ (residualY M Mc).pCoreIn 2)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hexclude : ¬ Nonempty (M ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)))) :
    V < (residualY M Mc).pCoreIn 2 ∧
      ¬ Nonempty (residualY M Mc ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  constructor
  · refine lt_of_le_of_ne hVY ?_
    intro heq
    exact hexclude ⟨residualY_wreathEquiv_of_core_eq M Mc V T hTM d hVlocal hc himage heq⟩
  · intro hY
    exact hexclude (residualY_wreath_of_pair_model M Mc V T hTM d hVlocal hVY hc hY)


end CFSG.Quasithin.Chapter15.Section03.WreathRecognition
