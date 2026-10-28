module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Splitting
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.Inputs
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup

/-!
# Residual and fixed-space transport in the repeated-natural branch

The proved splitting of W_L retains C_{W_L}(L). Restricting the projection
centralizer equality to Y₊ identifies the two literal centralizers and hence
their two-residuals. The earlier equalities M_c = C_G(Z) and
M ∩ M_c = C_M(V)T make the action image of C_{Y₊}(Z) a two-group;
its two-residual therefore lies in O²(C_{Y₊}(V)).

The elementary alternative of 15.3.7 cannot contain a nontrivial such
residual. In the other alternative the actual quotient of Y has order 27,
whereas the prepared quotient of Y₊ has order nine. This derives the
second choice of Hypothesis 15.3.10. The genuine plane-normalizer bound
then contradicts the outside component once its fixed space is calculated.

The final transport lemma uses two intrinsic calculations on the marked
plane parabolic. Their unconditional proofs are in PlaneGeometry, and the
Repeated assembly discharges these premises. No source theorem is asserted
by the conditional transport lemmas alone.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.4,
15.3.7, 15.3.10–12 and the repeated-natural paragraph of 15.3.24,
printed pp.1121–1125 and 1129 (PDF pp.1138–1142 and 1146).
-/

public section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated
open OutsideStructure
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The proved projection preserves the actual relative centralizer in Y₊. -/
theorem projected_centralizer_eq [IsElementaryAbelian 2 (d.componentSpan L)]
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    {r : ℕ} (h : RepeatedNatural d L r) (hYL : d.Yplus ≤ L) :
    d.Yplus ⊓ centralizer (projectedCenter d L : Set G) =
      d.Yplus ⊓ centralizer (d.Z : Set G) := by
  have he := projectedCenter_centralizer d L
    (centralSupplement_split_of_span_split (repeated_span_split hcore hR h))
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, (he.le ⟨hYL hy.1, hy.2⟩).2⟩
  · intro hy
    exact ⟨hy.1, (he.ge ⟨hYL hy.1, hy.2⟩).2⟩

/-- Taking two-residuals preserves the literal projected-centralizer equality. -/
theorem projected_residual_eq [IsElementaryAbelian 2 (d.componentSpan L)]
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    {r : ℕ} (h : RepeatedNatural d L r) (hYL : d.Yplus ≤ L) :
    twoResidualAmbient (d.Yplus ⊓ centralizer (projectedCenter d L : Set G)) =
      twoResidualAmbient (d.Yplus ⊓ centralizer (d.Z : Set G)) := by
  rw [projected_centralizer_eq hcore hR h hYL]

/-- Z_L is fixed by S ∩ L: both Z and the central supplement are fixed there. -/
theorem projected_center_fixed_sylow :
    projectedCenter d L ≤ centralizer ((d.S ⊓ L : Subgroup G) : Set G) := by
  apply inf_le_right.trans
  apply sup_le
  · exact (centralInvolutions_le_centralizer_sylow d.T).trans
      (centralizer_le (inf_le_left.trans inf_le_left))
  · exact inf_le_right.trans (centralizer_le inf_le_right)

/-- The source intersection factorization kills the residual action on V. -/
theorem center_residual_le_module_residual [Finite G]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hinter : d.M ⊓ d.Mc = (d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G)) :
    twoResidualAmbient (d.Yplus ⊓ centralizer (d.Z : Set G)) ≤
      twoResidualAmbient (d.Yplus ⊓ centralizer (d.V : Set G)) := by
  have hYM : d.Yplus ≤ d.M :=
    (choice_le _ _ _ _ _ d.choice).trans
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
  have hX : d.Yplus ⊓ centralizer (d.Z : Set G) ≤
      (d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G) := by
    rw [← hinter, hMc]
    exact inf_le_inf_right _ hYM
  have hker : d.action.image (d.M ⊓ centralizer (d.V : Set G)) = ⊥ :=
    (d.action.image_eq_bot_iff inf_le_left).mpr inf_le_right
  have hsup : d.action.image
      ((d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G)) =
      d.action.image (d.T : Subgroup G) := by
    unfold NaturalOrthogonalAction.image at *
    rw [subgroupOf_sup inf_le_left d.sylow_le, Subgroup.map_sup, hker]
    exact bot_sup_eq _
  have himage : d.action.image (d.Yplus ⊓ centralizer (d.Z : Set G)) ≤
      d.action.image (d.T : Subgroup G) :=
    (map_mono (comap_mono hX)).trans_eq hsup
  have htwo : IsPGroup 2 (d.action.image (d.T : Subgroup G)) :=
    (d.T.isPGroup'.comap_subtype (K := d.M)).map d.action.actor
  have hc := d.action.residual_le_centralizer_of_image_isTwoGroup
    (inf_le_left.trans hYM) (htwo.to_le himage)
  calc
    _ = twoResidualAmbient
        (twoResidualAmbient (d.Yplus ⊓ centralizer (d.Z : Set G))) :=
      (residual_idempotent _).symm
    _ ≤ _ := residual_mono
      (le_inf ((residual_le _).trans inf_le_left) (hc.trans inf_le_right))

private theorem residual_eq_bot_of_two_group [Finite G] (X : Subgroup G)
    (hX : IsPGroup 2 X) : twoResidualAmbient X = ⊥ := by
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hr : twoResidualSubgroup X = ⊥ := by
    apply bot_unique
    apply sInf_le
    exact ⟨inferInstance, n, by simpa using hn⟩
  rw [twoResidualAmbient, hr, Subgroup.map_bot]

/-- A nontrivial centralizer two-residual rules out the complete elementary alternative. -/
theorem extraspecial_of_center_residual_ne_bot [Finite G]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hinter : d.M ⊓ d.Mc = (d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G))
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (hne : twoResidualAmbient (d.Yplus ⊓ centralizer (d.Z : Set G)) ≠ ⊥) :
    ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action := by
  rcases h7 with h7 | h7
  · exfalso
    apply hne
    apply bot_unique
    have hle : d.Yplus ⊓ centralizer (d.V : Set G) ≤ d.Y.pCoreIn 2 := by
      rw [h7.1]
      exact inf_le_inf_right _ (choice_le _ _ _ _ _ d.choice)
    have htwo : IsPGroup 2 (d.Yplus ⊓ centralizer (d.V : Set G) : Subgroup G) :=
      (pCore_isPGroup.map d.Y.subtype).to_le hle
    exact (center_residual_le_module_residual hMc hinter).trans_eq
      (residual_eq_bot_of_two_group _ htwo)
  · exact h7

/-- The actual quotients of orders nine and 27 force Y₊ < Y and the second choice. -/
theorem second_choice_of_extraspecial [Finite G]
    (h7 : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (h9 : Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃*
      Multiplicative (Fin 2 → ZMod 3))) :
    d.Yplus < d.Y ∧ SecondChoice d := by
  have hne : d.Yplus ≠ d.Y := by
    intro he
    obtain ⟨e9⟩ := h9
    obtain ⟨e27⟩ := h7.1
    have hcard9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 := by
      rw [Nat.card_congr e9.toEquiv]
      change Nat.card (Fin 2 → ZMod 3) = 9
      simp
    have hcard27 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 27 := by
      rw [Nat.card_congr e27.toEquiv, HeisenbergPrime.card]
      norm_num
    rw [he, hcard27] at hcard9
    omega
  refine ⟨lt_of_le_of_ne (choice_le _ _ _ _ _ d.choice) hne, ?_⟩
  exact d.choice.resolve_left hne

/-- Vanishing on U_L identifies the fixed spaces in W_L while retaining its central factor. -/
theorem span_fixed_eq_of_commutator_fixed_eq_bot
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    {r : ℕ} (h : RepeatedNatural d L r) (hYL : d.Yplus ≤ L)
    (hfixed : spanCommutator d L ⊓ centralizer (d.Yplus : Set G) = ⊥) :
    d.componentSpan L ⊓ centralizer (d.Yplus : Set G) =
      d.componentSpan L ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · intro w hw
    have hn : d.componentSpan L ⊓ centralizer (L : Set G) ≤
        normalizer (spanCommutator d L : Set G) :=
      (inf_le_left.trans ((d.componentSpan L).le_centralizer.trans
        (centralizer_le (spanCommutator_le_span d L)))).trans
          (Subgroup.centralizer_le_normalizer _)
    have hm : w ∈ (spanCommutator d L : Set G) *
        ((d.componentSpan L ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
      exact (repeated_span_split hcore hR h).le hw.1
    obtain ⟨u, hu, c, hc, rfl⟩ := hm
    have huc : u ∈ centralizer (d.Yplus : Set G) :=
      (mul_mem_cancel_right (centralizer_le hYL hc.2)).mp hw.2
    have hu1 : u = 1 := by
      have hb : u ∈ (⊥ : Subgroup G) := hfixed ▸
        (show u ∈ spanCommutator d L ⊓ centralizer (d.Yplus : Set G) from ⟨hu, huc⟩)
      exact hb
    simpa only [hu1, one_mul] using
      (show c ∈ d.componentSpan L ⊓ centralizer (L : Set G) from hc)
  · exact inf_le_inf_left _ (centralizer_le hYL)

/-- The source plane lies in the component fixed space, contradicting its normalizer bound. -/
theorem contradiction_of_second_choice_and_fixed_space [Finite G]
    {I : Subgroup G} (c : ComponentWitness d I)
    (hchoice : SecondChoice d)
    (hfixed : d.componentSpan c.L ⊓ centralizer (d.Yplus : Set G) =
      d.componentSpan c.L ⊓ centralizer (c.L : Set G)) : False := by
  have hVY : d.V₁ ≤ centralizer (d.Yplus : Set G) := by
    apply le_centralizer_iff.mp
    rw [hchoice.2]
    exact (residual_le _).trans inf_le_right
  have hVW : d.V₁ ≤ d.componentSpan c.L :=
    (d.action.plane_le 1).trans (le_conjugateSpanBy d.V c.L)
  have hVL : d.V₁ ≤ centralizer (c.L : Set G) :=
    ((le_inf hVW hVY).trans_eq hfixed).trans inf_le_right
  exact c.outside (((le_centralizer_iff.mp hVL).trans
    (Subgroup.centralizer_le_normalizer _)).trans
      (LocalBranches.second_choice_plane_normalizers d hchoice).1)

private theorem isTwoGroup_of_residual_eq_bot [Finite G] (X : Subgroup G)
    (h : twoResidualAmbient X = ⊥) : IsPGroup 2 X := by
  have he : BenderSuzuki.External.hktPResidual 2 X = ⊥ := by
    apply map_injective X.subtype_injective
    rw [← Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual', Subgroup.map_bot]
    exact h
  let _ : (BenderSuzuki.External.hktPResidual 2 X).Normal :=
    BenderSuzuki.External.hktPResidual_normal
  exact BenderSuzuki.External.hktPResidual_quotient_isPGroup.of_equiv
    ((QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot)

/-- An element with cubic image prevents the source subgroup from being a two-group. -/
theorem residual_ne_bot_of_cubic_image [Finite G]
    {H : Type*} [Group H] (X : Subgroup G) (f : X →* H) (x : X)
    (ho : orderOf (f x) = 3) : twoResidualAmbient X ≠ ⊥ := by
  intro hz
  obtain ⟨k, hk⟩ := isTwoGroup_of_residual_eq_bot X hz x
  have hp : (f x) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [ho] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem commutatorAction_fixed (u : spanCommutator d L) (l : L)
    (hu : (u : G) ∈ centralizer ({(l : G)} : Set G)) :
    commutatorAction d L l u = u := by
  apply Subtype.ext
  change (l : G) * (u : G) * (l : G)⁻¹ = (u : G)
  rw [hu l (Set.mem_singleton _), mul_inv_cancel_right]

/-- Equivariant repeated natural coordinates transfer vanishing of fixed vectors to U_L. -/
theorem commutator_fixed_eq_bot_of_natural_fixed {r : ℕ} (h : RepeatedNatural d L r)
    (hfixed : ∀ v : Space 4,
      (∀ l : L, (l : G) ∈ d.Yplus → linearAction (by decide) h.model l v = v) → v = 0) :
    spanCommutator d L ⊓ centralizer (d.Yplus : Set G) = ⊥ := by
  apply bot_unique
  intro u hu
  let u' : spanCommutator d L := ⟨u, hu.1⟩
  have hc : h.coordinates u' = 1 := by
    apply Multiplicative.toAdd.injective
    change (h.coordinates u').toAdd = 0
    funext i
    apply hfixed
    intro l hl
    rw [← h.equivariant]
    have he : commutatorAction d L l u' = u' :=
      commutatorAction_fixed u' l (fun _ hy => (Set.mem_singleton_iff.mp hy) ▸ hu.2 l hl)
    rw [he]
  exact congrArg Subtype.val
    (h.coordinates.injective (hc.trans h.coordinates.map_one.symm))

/-- A cubic image fixing every projected coordinate gives a nontrivial centralizer residual. -/
theorem projected_residual_ne_bot_of_cubic [Finite G]
    {r : ℕ} (h : RepeatedNatural d L r) (l : L) (hl : (l : G) ∈ d.Yplus)
    (ho : orderOf (linearAction (by decide) h.model l) = 3)
    (hfix : ∀ u : spanCommutator d L, (u : G) ∈ projectedCenter d L →
      ∀ i : Fin r, linearAction (by decide) h.model l ((h.coordinates u).toAdd i) =
        (h.coordinates u).toAdd i) :
    twoResidualAmbient (d.Yplus ⊓ centralizer (projectedCenter d L : Set G)) ≠ ⊥ := by
  have hc : (l : G) ∈ centralizer (projectedCenter d L : Set G) := by
    intro z hz
    let u : spanCommutator d L := ⟨z, hz.1⟩
    have he : commutatorAction d L l u = u := by
      apply h.coordinates.injective
      apply Multiplicative.toAdd.injective
      funext i
      rw [h.equivariant]
      exact hfix u hz i
    have he' := congrArg Subtype.val he
    change (l : G) * z * (l : G)⁻¹ = z at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  let X := d.Yplus ⊓ centralizer (projectedCenter d L : Set G)
  let X' := X ⊓ L
  let f : X' →* LinearGroup 4 :=
    (linearAction (by decide) h.model).comp (inclusion inf_le_right)
  have hne : twoResidualAmbient X' ≠ ⊥ :=
    residual_ne_bot_of_cubic_image X' f ⟨l, ⟨hl, hc⟩, l.property⟩ ho
  intro hz
  exact hne (bot_unique ((residual_mono (show X' ≤ X from inf_le_left)).trans_eq hz))

/-- Transport the two plane calculations through the actual Sylow and Y₊ images. -/
theorem repeated_geometry_of_plane_calculations [Finite G]
    {I : Subgroup G} {c : ComponentWitness d I} (e : Preparation.Earlier d c)
    {r : ℕ} (h : RepeatedNatural d c.L r) (p : PlaneParabolic d c.L h.model)
    (hno : ∀ v : Space 4,
      (∀ g ∈ theta (BinaryLinear.parabolic p.plane), g v = v) → v = 0)
    (hcubic : ∀ B : Sylow 2 (LinearGroup 4),
      (B : Subgroup (LinearGroup 4)) ≤ BinaryLinear.parabolic p.plane →
      ∃ g ∈ BinaryLinear.parabolic p.plane, orderOf g = 3 ∧
        ∀ v : Space 4, (∀ b : B, (b : LinearGroup 4) v = v) → g v = v) :
    (spanCommutator d c.L ⊓ centralizer (d.Yplus : Set G) = ⊥) ∧
      twoResidualAmbient (d.Yplus ⊓ centralizer (projectedCenter d c.L : Set G)) ≠ ⊥ := by
  have himage := Preparation.yplusImage_eq_planeTheta e p
  constructor
  · apply commutator_fixed_eq_bot_of_natural_fixed h
    intro v hv
    apply hno v
    intro g hg
    rw [← himage] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    exact hv l hl
  · obtain ⟨P, hP⟩ := e.sylow_component
    let f := linearAction (by decide) h.model
    let B := P.mapSurjective (linearAction_surjective (by decide) h.model)
    have hPL : (P : Subgroup c.L) = (d.S ⊓ c.L).subgroupOf c.L := by
      apply map_injective c.L.subtype_injective
      rw [hP, map_subgroupOf_eq_of_le inf_le_right]
    have hBP : (B : Subgroup (LinearGroup 4)) ≤ BinaryLinear.parabolic p.plane := by
      change (P : Subgroup c.L).map f ≤ _
      rw [hPL, ← Preparation.planeParabolic_image p]
      exact map_mono (comap_mono (inf_le_inf_right c.L
        (show d.S ≤ d.M from inf_le_left.trans d.sylow_le)))
    obtain ⟨g, hg, ho, hfix⟩ := hcubic B hBP
    have hgY : g ∈ Preparation.modelImage (by decide) h.model d.Yplus := by
      rw [himage]
      exact subset_closure ⟨hg, ho⟩
    obtain ⟨l, hl, he⟩ := hgY
    apply projected_residual_ne_bot_of_cubic h l hl
    · rw [he]
      exact ho
    · intro u hu i
      rw [he]
      apply hfix
      intro b
      obtain ⟨s, hs, hsB⟩ := b.property
      rw [← hsB]
      rw [hPL] at hs
      have hcu := projected_center_fixed_sylow (d := d) (L := c.L) hu s hs
      have heq : commutatorAction d c.L s u = u :=
        commutatorAction_fixed u s (fun _ hy => (Set.mem_singleton_iff.mp hy) ▸ hcu)
      rw [← h.equivariant, heq]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated

end
