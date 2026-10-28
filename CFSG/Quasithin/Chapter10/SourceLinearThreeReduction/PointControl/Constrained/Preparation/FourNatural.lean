module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Local
public import CFSG.Quasithin.Chapter10.SourceA5LocalSeedSplit
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.ConjugateNormalizerIndexTwo
public import Theory.Representation.BinaryOffender.Homogeneous.InnerFactor

/-!
# Preparing the retained four-natural point orbit

Crossed centralization separates the original Irr⁺ seed: its commutator with
L is either the whole seed or central, and perfectness eliminates a nonzero
central commutator. The four-natural marking forces inner normalizer action
on L/O₂(L). Correcting that action on the seed's irreducible central image
and using homogeneity proves that N_T(L) fixes the original seed, in either
support orientation.

The local moved subgroup is consequently a single Irr⁺ seed. Its fixed
kernel vanishes in the constrained context, so the nonzero point-Sylow fixed
subgroup generates it under L inside VI. Half-Sylow uniqueness controls the
centralizer of VI, and the proved cubic Thompson equality completes its
preparation. No equality of the local and full moved subgroups is asserted.

The final theorem applies the complete FF classification to the actual
reduced orbit. Original row exhaustion and the remaining A₇/binary containing
exclusions stay with qt-d-10-nona5-point-constrained. Source connects this
preparation to the original point-control assembly.
Source: Aschbacher--Smith D.3.6, 10.1.1(6), 10.2.9, pp.196,741,751--753.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The original crossed hypothesis also centralizes the opposite factor before conjugation. -/
theorem Context.moved_centralizes_opposite (c : Context D t v I) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  have hR : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hW := conjugate_twice_eq_of_index_two ⁅D.fullModule,L⁆ (T : Subgroup G)
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
      (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem))) hR c.escaping.t_mem
  have hz := congrArg (map (MulAut.conj t).toMonoidHom)
    (commutator_eq_bot_iff_le_centralizer.mpr c.escaping.crossed)
  rw [map_commutator,hW,Subgroup.map_bot] at hz
  exact commutator_eq_bot_iff_le_centralizer.mp hz

/-- Irr⁺ minimality and perfectness separate the original seed into one component support. -/
theorem Context.seed_separated (c : Context D t v I) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)
  have hS : ⁅D.seed,L⁆ ≤ D.seed := le_normalizer_iff_commutator_le_left.mp
    ((le_componentOrbit L T).trans D.orbit_normalizes_seed)
  have hN : localOrbit T L ≤ normalizer (↑(⁅D.seed,L⁆ : Subgroup G) : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (D.orbit_normalizes_seed hx),
      mem_normalizer_iff_map_conj_eq.mp (source_nonnormal_orbit_le_normalizer D hn hx)]
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus ⁅D.seed,L⁆ hS hN with he | hc
  · left
    change ⁅D.seed,L⁆ = D.seed at he
    rw [←he]
    exact (commutator_mono ((le_componentOrbit D.seed T).trans
      (le_componentOrbit _ D.maximalLocal)) le_rfl).trans c.moved_centralizes_opposite
  · right
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_iterated_eq_bot
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (centralizer_le (le_componentOrbit L T)))

section LocalSeed
variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

include D hn ht htn in
private theorem original_pair :
    localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
  componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
    inf_le_right ht htn

include hn ht htn in
private theorem local_moved_eq_seed
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    ⁅D.moduleSubgroup,L⁆ = D.seed := by
  have hpair := original_pair (D := D) hn ht htn
  have hseed : D.seed = ⁅D.seed,localOrbit T L⁆ :=
    ReducedNormal.subspaceImage_eq_commutator (localJoin T L) D.seedSpace
      (localOrbit T L) le_sup_left D.homogeneous.invariant
      D.homogeneous.isIrrPlus.choose_spec.1
  have hLS : L ≤ normalizer (D.seed : Set G) :=
    (le_componentOrbit L T).trans D.orbit_normalizes_seed
  have hcomm : ⁅D.seed,L⁆ = D.seed := by
    rw [commutator_eq_of_centralizing_sup (by simpa only [sup_comm] using hpair.symm)
      (le_centralizer_iff.mp hsep) hLS, ←hseed]
  have hsplit : D.moduleSubgroup = D.seed ⊔ D.seed.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two D.seed T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      hstab ht htn
  have hSL : D.seed ≤ normalizer (L : Set G) :=
    (le_componentOrbit D.seed T).trans
      (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hc := commutator_eq_of_centralizing_sup
    (by simpa only [sup_comm] using hsplit.symm)
    (source_local_seed_conjugate_centralizes D hn ht hsep) hSL
  rw [commutator_comm,←hc,commutator_comm,hcomm]

include hn ht htn in
private theorem local_opposite_seed_movement_and_minimality
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (hsep : D.seed ≤ centralizer (L : Set G)) :
    ⁅D.moduleSubgroup,L⁆ = D.seed.map (MulAut.conj t).toMonoidHom ∧
      ∀ J : Subgroup G, J ≤ ⁅D.moduleSubgroup,L⁆ → L ≤ normalizer (J : Set G) →
        J = ⁅D.moduleSubgroup,L⁆ ∨ J ≤ centralizer (L : Set G) := by
  let H := localJoin T L
  let τ := ReducedNormal.representation H
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let I := D.seedSpace.map (τ tH)
  let U := D.seed.map (MulAut.conj t).toMonoidHom
  have hi : IsIrrPlus τ ((localOrbit T L).subgroupOf H) I :=
    D.homogeneous.isIrrPlus.map_normalizer τ
      (D.homogeneous.normalizes (show tH ∈ (T : Subgroup G).subgroupOf H from ht))
  have himage : ReducedNormal.subspaceImage H I = U :=
    ReducedNormal.subspaceImage_map H D.seedSpace tH
  have hpair := original_pair (D := D) hn ht htn
  have hsep' : U ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hsep
    rw [Theory.GroupTheory.map_centralizer_equiv] at hh
    exact hh
  have hUO : U = ⁅U,localOrbit T L⁆ := by
    have hh := ReducedNormal.subspaceImage_eq_commutator H I (localOrbit T L)
      le_sup_left hi.choose hi.choose_spec.1
    rwa [himage] at hh
  have hOU : localOrbit T L ≤ normalizer (U : Set G) := by
    rw [←himage]
    exact ReducedNormal.subspaceImage_normalizes H (localOrbit T L) le_sup_left I hi.choose
  have hcomm : ⁅U,L⁆ = U := by
    rw [commutator_eq_of_centralizing_sup (by simpa only [sup_comm] using hpair.symm)
      (le_centralizer_iff.mp hsep') ((le_componentOrbit L T).trans hOU), ←hUO]
  have hsplit : D.moduleSubgroup = D.seed ⊔ U :=
    componentOrbit_eq_sup_of_index_two D.seed T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      hstab ht htn
  have hUL : U ≤ normalizer (L : Set G) :=
    ((le_sup_right : U ≤ D.seed ⊔ U).trans hsplit.ge).trans
      (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hW : ⁅D.moduleSubgroup,L⁆ = U := by
    have hc := commutator_eq_of_centralizing_sup hsplit.symm hsep hUL
    rw [commutator_comm,←hc,commutator_comm,hcomm]
  refine ⟨hW,?_⟩
  intro J hJW hLJ
  have hJU : J ≤ U := hJW.trans_eq hW
  have hBJ : L.map (MulAut.conj t).toMonoidHom ≤ normalizer (J : Set G) :=
    ((le_centralizer_iff.mp hsep').trans (centralizer_le hJU)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hOJ : localOrbit T L ≤ normalizer (J : Set G) := by
    rw [hpair]
    exact sup_le hLJ hBJ
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer H (localOrbit T L)
      le_sup_left hi J (hJU.trans_eq himage.symm) hOJ with he | hc
  · exact Or.inl ((he.trans himage).trans hW.symm)
  · exact Or.inr (hc.trans (centralizer_le (le_componentOrbit L T)))

end LocalSeed

/-- A stable original seed makes every proper invariant subgroup of the local moved factor central. -/
theorem Context.local_moved_minimal_of_seed_stable (c : Context D t v I)
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (A : Subgroup G) (hA : A ≤ ⁅D.moduleSubgroup,L⁆)
    (hLA : L ≤ normalizer (A : Set G)) :
    A = ⁅D.moduleSubgroup,L⁆ ∨ A ≤ centralizer (L : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)
  rcases c.seed_separated with hs | hs
  · have he := local_moved_eq_seed D hn c.escaping.t_mem c.escaping.t_not_normalizes hstab hs
    rw [he] at hA ⊢
    exact source_local_seed_minimal D hn c.escaping.t_mem c.escaping.t_not_normalizes hs A hA hLA
  · exact (local_opposite_seed_movement_and_minimality D hn c.escaping.t_mem
      c.escaping.t_not_normalizes hstab hs).2 A hA hLA

/-- The nonzero point-fixed subgroup generates the local moved factor when the seed is stable. -/
theorem Context.local_moved_le_of_seed_stable (c : Context D t v I)
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G)) :
    ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I := by
  let W := ⁅D.moduleSubgroup,L⁆
  have hWF : W ≤ ⁅D.fullModule,L⁆ := commutator_mono (le_componentOrbit _ _) le_rfl
  have hz : W ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hWF).trans_eq c.moved_fixed_eq_bot)
  let P := pointSylow T v
  have hPH : P ≤ halfJoin T L :=
    (le_inf inf_le_left c.escaping.sylow_normalizes).trans le_sup_right
  have hPW : P ≤ normalizer (W : Set G) := hPH.trans c.halfJoin_normalizes_local_moved
  have hWV : W ≤ D.moduleSubgroup := le_normalizer_iff_commutator_le_left.mp
    ((le_componentOrbit L T).trans D.orbit_normalizes_module)
  have hfix := inf_centralizer_ne_bot_of_pGroups P W (T.isPGroup'.to_le inf_le_left)
    (D.module_elementary.isPGroup.to_le hWV) hPW
    (Selection.ModuleChoice.local_moved_ne_bot D)
  let A := conjugateSpanBy (W ⊓ centralizer (P : Set G)) L
  have hA : A = W := by
    rcases c.local_moved_minimal_of_seed_stable hstab A
      (conjugateSpanBy_le inf_le_left
        (((le_componentOrbit L T).trans le_sup_left).trans c.halfJoin_normalizes_local_moved))
      (le_normalizer_conjugateSpanBy _ _) with he | hc
    · exact he
    · have hAW : A ≤ W := conjugateSpanBy_le inf_le_left
        (((le_componentOrbit L T).trans le_sup_left).trans c.halfJoin_normalizes_local_moved)
      exact (hfix (bot_unique ((le_conjugateSpanBy _ _).trans
        ((le_inf hAW hc).trans_eq hz)))).elim
  change W ≤ orbitModule D v I
  rw [←hA]
  exact conjugateSpanBy_mono (inf_le_inf_right _ hWF) c.escaping.strict.le

open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
private theorem seed_normalized_of_active_twists
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (A B S : Subgroup G) (hpair : A ⊔ B = localOrbit T L)
    (hB : D.seed ≤ centralizer (B : Set G))
    (hST : S ≤ T) (hSA : S ≤ normalizer (A : Set G))
    (hSB : S ≤ normalizer (B : Set G))
    (htwist : ∀ (s : S) {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) A W)
      [σ.IsIrreducible], ∃ f : W ≃ₗ[ZMod 2] W,
      ∀ g v, f (σ g v) = σ (A.normalizerMonoidHom ⟨s,hSA s.property⟩ g) (f v)) :
    S ≤ normalizer (D.seed : Set G) := by
  let H := localJoin T L
  let ρ := ReducedNormal.representation H
  have hAH : A ≤ H := (le_sup_left.trans hpair.le).trans le_sup_left
  have hBH : B ≤ H := (le_sup_right.trans hpair.le).trans le_sup_left
  have hpairH : A.subgroupOf H ⊔ B.subgroupOf H = (localOrbit T L).subgroupOf H := by
    rw [← subgroupOf_sup hAH hBH, hpair]
  have hfix : D.seedSpace ≤ fixedSpace ρ (B.subgroupOf H) := by
    intro v hv
    apply (ReducedNormal.mem_reduced_fixedSpace_iff H B hBH v).mpr
    exact hB (mem_map_of_mem H.subtype (mem_map_of_mem (ReducedNormal.ModuleGroup H).subtype hv))
  let eA := subgroupOfEquivOfLe hAH
  intro s hs
  let sH : H := ⟨s, (show (T : Subgroup G) ≤ H from le_sup_right) (hST hs)⟩
  let sT : (T : Subgroup G).subgroupOf H := ⟨sH, hST hs⟩
  have hA : sH ∈ normalizer (A.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hAH]
    exact hSA hs
  have hB' : sH ∈ normalizer (B.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hBH]
    exact hSB hs
  have he := D.homogeneous.map_eq_of_active_factor_twist_at ρ sT
    (A.subgroupOf H) (B.subgroupOf H) hpairH hfix hA hB'
    (fun σ _ => by
      let τ := σ.comp eA.symm.toMonoidHom
      let : IsIrreducible τ :=
        (irreducible_comp_surjective_iff eA.symm.toMonoidHom eA.symm.surjective σ).mpr
          inferInstance
      obtain ⟨f,hf⟩ := htwist (⟨s⁻¹,S.inv_mem hs⟩ : S) τ
      exact ⟨f,fun g v => hf (eA g) v⟩)
  have himage := congrArg (ReducedNormal.subspaceImage H) he
  rw [ReducedNormal.subspaceImage_map] at himage
  exact mem_normalizer_iff_map_conj_eq.mpr himage


/-- The inner component action fixes the original homogeneous seed in both support orientations. -/
theorem Context.seed_normalized_of_four_natural_cover (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G) := by
  let B := L.map (MulAut.conj t).toMonoidHom
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have hp : L ⊔ B = localOrbit T L :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G)) hi inf_le_right
      c.escaping.t_mem c.escaping.t_not_normalizes).symm
  have hSB : S ≤ normalizer (B : Set G) :=
    normalizes_conjugate_of_index_two L T hi c.escaping.t_mem
  rcases c.seed_separated with hs | hs
  · apply seed_normalized_of_active_twists D L B S hp hs inf_le_left inf_le_right hSB
    intro n W _ _ _ σ _
    exact irreducible_twist_of_inner_twoCore σ _
      (c.normalizer_inner_of_four_natural_cover e s ⟨n,n.property.2⟩)
  · apply seed_normalized_of_active_twists D B L S (by simpa only [sup_comm] using hp)
      hs inf_le_left hSB inf_le_right
    intro n W _ _ _ σ _
    have hnmap : (n : G) ∈ (normalizer (L : Set G)).map (MulAut.conj t).toMonoidHom := by
      rw [map_equiv_normalizer_eq]
      exact hSB n.property
    obtain ⟨p,hp',hpn⟩ := hnmap
    let f : L ≃* B := L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
    let τ := σ.comp f.toMonoidHom
    let : IsIrreducible τ :=
      (irreducible_comp_surjective_iff f.toMonoidHom f.surjective σ).mpr inferInstance
    let a := L.normalizerMonoidHom ⟨p,hp'⟩
    obtain ⟨b,hb⟩ := irreducible_twist_of_inner_twoCore τ a
      (c.normalizer_inner_of_four_natural_cover e s ⟨p,hp'⟩)
    refine ⟨b,?_⟩
    intro g w
    have hh := hb (f.symm g) w
    change b (σ (f (f.symm g)) w) = σ (f (a (f.symm g))) (b w) at hh
    rw [f.apply_symm_apply] at hh
    rw [hh]
    congr 2
    apply Subtype.ext
    have hg := congrArg Subtype.val (f.apply_symm_apply g)
    change t * (f.symm g : G) * t⁻¹ = (g : G) at hg
    change t * (p * (f.symm g : G) * p⁻¹) * t⁻¹ = (n : G) * (g : G) * (n : G)⁻¹
    change t * p * t⁻¹ = (n : G) at hpn
    rw [←hpn,←hg]
    group


/-- Homogeneous seed stability puts the original local moved subgroup in VI. -/
theorem Context.local_moved_le_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) : ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I := by
  obtain ⟨e,⟨s⟩⟩ := h
  exact c.local_moved_le_of_seed_stable (c.seed_normalized_of_four_natural_cover e s)

/-- The retained four-natural row prepares the literal orbit without identifying
its local seed with the full twelve-dimensional moved subgroup. -/
theorem Context.prepared_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) : Prepared D v I := by
  obtain ⟨e,⟨s⟩⟩ := h
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  exact c.prepared_of_local_moved_le_of_three hd
    (c.local_moved_le_of_seed_stable (c.seed_normalized_of_four_natural_cover e s))

/-- The four-natural source marking now supplies the original FF action. -/
theorem Context.actionFacts_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) : ActionFacts c :=
  c.actionFacts (c.prepared_of_four_natural_cover h)

/-- Every marked original source alternative is prepared; exhaustion of this
list and the remaining containing-action exclusion stay with this owner. -/
theorem Context.prepared_of_original_moved_cover (c : Context D t v I)
    (h : OriginalMovedCover D) : Prepared D v I :=
  c.prepared_of_four_natural_cover (c.four_natural_of_original_moved_cover h)

/-- Apply four-natural preparation to the complete marked containing-action
sieve on the literal reduced module. Excluding these containing rows remains
with qt-d-10-nona5-point-constrained. -/
theorem Context.binary_or_seven_action_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map
      (ChapterB.InternalThompsonAction.actionMk (internalModule D v I))
    let N := Representation.BinaryOffender.offenderSubgroup
      (ChapterB.InternalThompsonAction.action (internalModule D v I))
    ∃ r : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((ChapterB.InternalThompsonAction.action (internalModule D v I)).comp N.subtype)
        (A.subgroupOf N), BinaryOrSevenAction r.sectionData := by
  obtain ⟨e,⟨s⟩⟩ := h
  exact c.binary_or_seven_action_of_binaryThree_quotient
    (c.actionFacts_of_four_natural_cover ⟨e,⟨s⟩⟩) e

end CFSG.Quasithin.Chapter10.PointControl.Constrained
