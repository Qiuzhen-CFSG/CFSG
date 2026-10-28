module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.FourNatural
public import Theory.Representation.BinaryConjugationSection.SimpleRepeated
public import Theory.Representation.PSL3Two.NaturalSylowFixed

/-!
# The local natural copy in a four-natural cover

The original local moved subgroup is a minimal invariant subgroup in the
four-copy coordinates, hence an actual natural three-space. Its point
Sylow fixed subgroup has order two. The nonidentity vector generates the
local three-space under L and its smaller orbit under I is reduced.
Its centralizer still lies in the original maximal local subgroup.

Only the local moved subgroup is used here. No containment of the full
four-copy moved subgroup in the original reduced orbit is asserted.
Source: Aschbacher--Smith 10.1.1(6), printed p.741, and the local-orbit
argument of 10.2.9, printed pp.751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The local seed is one actual natural copy in the original four-copy cover. -/
theorem Context.local_natural_of_four_natural_cover (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  have hWF : ⁅D.moduleSubgroup,L⁆ ≤ ⁅D.fullModule,L⁆ :=
    commutator_mono (le_componentOrbit _ _) le_rfl
  have hstab := c.seed_normalized_of_four_natural_cover e s
  refine (c.moved_fixed_eq_bot ▸ s).single_copy_of_minimal
    (ρ := (specialLinearNatural 3).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) (fun _ _ _ => rfl) ?_
    hWF (normalizer_commutator_ge_right _ _) (Selection.ModuleChoice.local_moved_ne_bot D) ?_
  · intro x y hx hy
    obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx hy
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    exact ⟨l, (congrArg (fun g => specialLinearNatural 3 g x) hl).trans hg⟩
  · intro K hK hNK
    rcases c.local_moved_minimal_of_seed_stable hstab K hK hNK with he | hc
    · exact Or.inl he
    · exact Or.inr (bot_unique ((le_inf (hK.trans hWF) hc).trans_eq c.moved_fixed_eq_bot))

/-- The actual local moved subgroup has order eight. -/
theorem Context.local_moved_card_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) : Nat.card (⁅D.moduleSubgroup,L⁆ : Subgroup G) = 8 := by
  obtain ⟨e,⟨s⟩⟩ := h
  obtain ⟨r⟩ := c.local_natural_of_four_natural_cover e s
  have hc := r.card_section
  simpa using hc

/-- The point Sylow fixes precisely one line in the literal local natural copy. -/
theorem Context.local_point_fixed_card_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) :
    Nat.card (⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G) : Subgroup G) = 2 := by
  obtain ⟨e,⟨s⟩⟩ := h
  obtain ⟨r⟩ := c.local_natural_of_four_natural_cover e s
  let W := ⁅D.moduleSubgroup,L⁆
  let P := pointSylow T v
  let F := W ⊓ centralizer (P : Set G)
  have hWF : W ≤ ⁅D.fullModule,L⁆ := commutator_mono (le_componentOrbit _ _) le_rfl
  have hWP : P ≤ normalizer (W : Set G) :=
    ((le_inf inf_le_left c.escaping.sylow_normalizes).trans le_sup_right).trans
      c.halfJoin_normalizes_local_moved
  have hfix : F ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups P W
    (T.isPGroup'.to_le inf_le_left)
    ((source_original_full_moved_elementary D).isPGroup.to_le hWF) hWP
    (Selection.ModuleChoice.local_moved_ne_bot D)
  have hlo : 1 < Nat.card F := (one_lt_card_iff_ne_bot F).mpr hfix
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hc : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  obtain ⟨R,hR⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (H := localJoin T L)
    ⟨T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right),
      map_subgroupOf_eq_of_le le_sup_right⟩ hLH hc.subnormal
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := R.mapSurjective hq
  have hRP : (R : Subgroup L).map L.subtype ≤ P := by
    rw [hR]
    exact le_inf inf_le_left (inf_le_right.trans
      (c.escaping.strict.le.trans c.escaping.le_centralizer))
  let f : F → fixedSpace BinaryLinearThree.W (Q : Subgroup BinaryLinearThree.Group) :=
    fun z => ⟨(r.coordinates ⟨z,z.property.1⟩).toAdd,by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      have hh := r.equivariant l ⟨z,z.property.1⟩
      have hz : (⟨(l:G)*z*(l:G)⁻¹,
          (mem_normalizer_iff.mp (r.normalized l.property) (z:G)).mp z.property.1⟩ : W) = ⟨z,z.property.1⟩ := by
        apply Subtype.ext
        change (l:G)*(z:G)*(l:G)⁻¹ = (z:G)
        rw [z.property.2 l (hRP (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]
      rw [hz] at hh
      change (r.coordinates ⟨z,z.property.1⟩).toAdd =
        BinaryLinearThree.W (q l) (r.coordinates ⟨z,z.property.1⟩).toAdd at hh
      rw [he] at hh
      exact hh.symm⟩
  have hrinj : Function.Injective r.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [r.kernel_eq,bot_subgroupOf])
  have hi : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact congrArg (fun a : W => (a:G)) (hrinj (congrArg Subtype.val he))
  have hup := (Nat.card_le_card_of_injective f hi).trans
    (BinaryLinearThree.card_sylow_natural_fixed_le_two Q)
  change Nat.card F ≤ 2 at hup
  change Nat.card F = 2
  omega

/-- A nonzero vector of the local point-fixed line generates the whole local copy under L. -/
theorem Context.local_moved_eq_span_of_four_natural_seed (c : Context D t v I)
    (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) : conjugateSpanBy (zpowers u) L = ⁅D.moduleSubgroup,L⁆ := by
  obtain ⟨e,⟨s⟩⟩ := h
  have hstab := c.seed_normalized_of_four_natural_cover e s
  let A := conjugateSpanBy (zpowers u) L
  have hAW : A ≤ ⁅D.moduleSubgroup,L⁆ :=
    conjugateSpanBy_le (zpowers_le.mpr hu.1) (normalizer_commutator_ge_right _ _)
  rcases c.local_moved_minimal_of_seed_stable hstab A hAW
      (le_normalizer_conjugateSpanBy _ _) with he | hc
  · exact he
  · have hz : A = ⊥ := bot_unique
      ((le_inf (hAW.trans (commutator_mono (le_componentOrbit _ _) le_rfl)) hc).trans_eq
        c.moved_fixed_eq_bot)
    have huA : u ∈ A := le_conjugateSpanBy _ _ (mem_zpowers u)
    exact (hne (mem_bot.mp (hz ▸ huA))).elim

/-- The local I-orbit can be generated by its single point-fixed involution. -/
theorem Context.local_orbit_eq_seed_orbit_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    conjugateSpanBy ⁅D.moduleSubgroup,L⁆ I = conjugateSpanBy (zpowers u) I := by
  apply le_antisymm
  · apply conjugateSpanBy_le ?_ (le_normalizer_conjugateSpanBy _ _)
    rw [←c.local_moved_eq_span_of_four_natural_seed h hu hne]
    exact conjugateSpanBy_mono le_rfl c.escaping.strict.le
  · exact conjugateSpanBy_mono (zpowers_le.mpr hu.1) le_rfl

/-- The smaller orbit retains ambient centralizer control on the original point configuration. -/
theorem Context.local_orbit_centralizer_le_of_four_natural_cover (c : Context D t v I)
    (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    centralizer (conjugateSpanBy (zpowers u) I : Set G) ≤ D.maximalLocal := by
  rw [←c.local_orbit_eq_seed_orbit_of_four_natural_cover h hu hne]
  exact (centralizer_le (le_conjugateSpanBy _ _)).trans
    ((Subgroup.centralizer_le_normalizer _).trans c.local_moved_normalizer_le)

/-- A point-Sylow-fixed elementary seed retains reducedness on its own orbit. -/
theorem Context.reduced_of_point_fixed_seed (c : Context D t v I)
    (Z : Subgroup G)
    (hZ : Z ≤ ⁅D.fullModule,L⁆ ⊓ centralizer (pointSylow T v : Set G)) :
    IsPReduced 2 ((conjugateSpanBy Z I).subgroupOf (pointJoin T v I)) := by
  let H := pointJoin T v I
  let P := pointSylow T v
  let R := conjugateSpanBy Z I
  have hZH : Z ≤ H := (hZ.trans inf_le_left).trans
    ((source_full_moved_le_component D).trans (c.escaping.strict.le.trans le_sup_left))
  have hWT : ⁅D.fullModule,L⁆ ≤ (T : Subgroup G) :=
    (le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)).trans
      (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D))
  have hZP : Z ≤ P := le_inf ((hZ.trans inf_le_left).trans hWT)
    ((hZ.trans inf_le_left).trans ((source_full_moved_le_component D).trans
      (c.escaping.strict.le.trans c.escaping.le_centralizer)))
  have hspan : conjugateSpanBy Z H = R :=
    conjugateSpanBy_sup_of_normalizes_seed Z I P
      ((le_centralizer_iff.mp (hZ.trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _))
      (inf_le_right.trans c.escaping.normalizes)
  have hR : R ≤ orbitModule D v I := conjugateSpanBy_mono hZ le_rfl
  have he : normalClosure (Z.subgroupOf H : Set H) = R.subgroupOf H := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy Z H hZH,hspan]
  let := c.reduced.elementary
  let : IsElementaryAbelian 2 (R.subgroupOf H) := IsElementaryAbelian.of_le
    (show R.subgroupOf H ≤ internalModule D v I from comap_mono hR)
  let : IsElementaryAbelian 2 (normalClosure (Z.subgroupOf H : Set H)) := he.symm ▸ inferInstance
  let : IsElementaryAbelian 2 (Z.subgroupOf H) := IsElementaryAbelian.of_le
    (show Z.subgroupOf H ≤ R.subgroupOf H from comap_mono (le_conjugateSpanBy Z I))
  obtain ⟨S,hS⟩ := c.join_sylow
  have hS' : (S : Subgroup H) = P.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  have hr := isPReduced_normalClosure_of_sylow_central S (Z.subgroupOf H)
    (by rw [hS']; exact comap_mono hZP)
    (by
      intro z hz p hp
      apply Subtype.ext
      exact (hZ hz).2 p (show p ∈ P.subgroupOf H from hS' ▸ hp))
  rwa [he] at hr

/-- The single local fixed involution has a reduced orbit inside the original VI. -/
theorem Context.local_seed_orbit_reduced (c : Context D t v I)
    {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G)) :
    IsPReduced 2 ((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)) :=
  c.reduced_of_point_fixed_seed (zpowers u) (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,hu.2⟩)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
