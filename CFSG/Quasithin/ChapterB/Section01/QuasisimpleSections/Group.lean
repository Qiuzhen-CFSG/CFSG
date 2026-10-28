module

public import GorensteinWalter.Section2.Bender1970_18
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The group argument for quasisimple sections

We identify the intrinsic component and generalized-Fitting definitions with
those of the proved Gorenstein–Walter self-centralization theorem. This bridge
stays above `Theory` because that theorem belongs to the Gorenstein–Walter
campaign. Both component definitions use relative subnormality and actual
simplicity of the quotient by the center.

A normal kernel not containing the quasisimple generalized Fitting subgroup
centralizes it, hence lies in its center. Its intersection with any 2-subgroup
is trivial when the two-core is trivial: the centralizer is normal abelian,
and its two-core maps into the ambient two-core. The component commutator
dichotomy then shows that a nontrivial 2-subgroup generates the component by
commutation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.5(8),
printed pp. 69–70; generalized-Fitting self-centralization as proved in
`GorensteinWalter.Section2.Bender1970_18` (KS 6.5.8).
-/

public section

namespace CFSG.Quasithin.ChapterB.QuasisimpleSections
open Subgroup Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

private theorem map_fitting_le (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom ≤ fittingSubgroup H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply Subgroup.map_le_iff_le_comap.mp
  let _ := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem map_fitting_eq (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
  apply le_antisymm (map_fitting_le e)
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_fitting_le e.symm)
  have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  simpa only [Subgroup.map_map, he, Subgroup.map_id] using h

theorem quasisimple_iff_legacy (G : Type*) [Group G] :
    Theory.GroupTheory.IsQuasisimple G ↔ GorensteinWalter.IsQuasisimple G := by
  constructor
  · intro h
    let _ := h
    let _ := h.simple
    have hn : Nontrivial G := (QuotientGroup.mk'_surjective (center G)).nontrivial
    exact ⟨hn, Group.IsPerfect.commutator_eq_top, h.simple⟩
  · rintro ⟨_, hp, hs⟩
    exact { toIsPerfect := ⟨hp⟩, simple := hs }

theorem component_iff_legacy (L : Subgroup G) :
    IsComponent G L ↔ GorensteinWalter.IsComponentOf L ⊤ := by
  constructor
  · rintro ⟨hn, hq⟩
    exact ⟨le_top, hn.subgroupOf, (quasisimple_iff_legacy L).mp hq⟩
  · rintro ⟨_, hn, hq⟩
    exact ⟨hn.trans le_top Subgroup.IsSubnormal.top,
      (quasisimple_iff_legacy L).mpr hq⟩

theorem generalizedFitting_eq_legacy :
    generalizedFitting G = GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) := by
  have hf : GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup G) = fittingSubgroup G :=
    map_fitting_eq Subgroup.topEquiv
  have hc : componentLayer G = GorensteinWalter.componentLayerOf (⊤ : Subgroup G) := by
    unfold componentLayer GorensteinWalter.componentLayerOf
    congr 1
    ext L
    exact component_iff_legacy L
  simp only [generalizedFitting, GorensteinWalter.generalizedFittingSubgroupOf, hf, hc]

theorem centralizer_generalizedFitting_le [Finite G] :
    centralizer (generalizedFitting G : Set G) ≤ generalizedFitting G := by
  rw [generalizedFitting_eq_legacy]
  exact GorensteinWalter.fstar_self_centralizing


variable [Finite G]

/-- The centralizer of the generalized Fitting subgroup meets every 2-subgroup
trivially when the two-core is trivial. -/
theorem disjoint_centralizer_fitting (hcore : pCore 2 G = ⊥)
    (A : Subgroup G) (hA : IsPGroup 2 A) :
    Disjoint A (centralizer (generalizedFitting G : Set G)) := by
  let L := generalizedFitting G
  let C := centralizer (L : Set G)
  have hCL : C ≤ L := centralizer_generalizedFitting_le
  let _ : L.Normal := generalizedFitting_normal (G := G)
  let _ : C.Normal := inferInstance
  let _ : IsMulCommutative C := ⟨⟨fun x y => Subtype.ext
    ((mem_centralizer_iff.mp x.property) y (hCL y.property)).symm⟩⟩
  have hpc : (pCore 2 C).map C.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map C.subtype⟩
  have hac : A.subgroupOf C ≤ pCore 2 C :=
    le_sSup ⟨inferInstance, hA.comap_subtype⟩
  apply disjoint_iff_inf_le.mpr
  intro a ha
  have hmem : a ∈ (pCore 2 C).map C.subtype := ⟨⟨a, ha.2⟩, hac ha.1, rfl⟩
  have := hpc hmem
  rwa [hcore] at this

/-- A nontrivial 2-subgroup generates the quasisimple generalized Fitting
subgroup by commutation. -/
theorem commutator_fitting_eq (hcore : pCore 2 G = ⊥)
    (hL : Theory.GroupTheory.IsQuasisimple (generalizedFitting G))
    {A : Subgroup G} (hne : A ≠ ⊥) (hA : IsPGroup 2 A) :
    ⁅generalizedFitting G, A⁆ = generalizedFitting G := by
  let L := generalizedFitting G
  let _ : L.Normal := generalizedFitting_normal (G := G)
  have hc : IsComponent G L := ⟨Subgroup.Normal.isSubnormal inferInstance, hL⟩
  rcases hc.commutator_dichotomy A with hz | he
  · have hAC : A ≤ centralizer (L : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm A L).trans hz)
    exact (hne ((disjoint_centralizer_fitting hcore A hA).eq_bot_of_le hAC)).elim
  · simpa only [MulEquiv.toMonoidHom_eq_coe, Subgroup.Normal.map_conj_eq, iSup_const] using he

/-- Every normal kernel not containing the quasisimple generalized Fitting
subgroup is contained in its actual center. -/
theorem kernel_le_fitting_center
    (hL : Theory.GroupTheory.IsQuasisimple (generalizedFitting G))
    (φ : G →* H) (hnontriv : ¬ generalizedFitting G ≤ φ.ker) :
    φ.ker ≤ (center (generalizedFitting G)).map (generalizedFitting G).subtype := by
  let L := generalizedFitting G
  let _ : L.Normal := generalizedFitting_normal (G := G)
  have hc : IsComponent G L := ⟨Subgroup.Normal.isSubnormal inferInstance, hL⟩
  have hker : φ.ker ≤ centralizer (L : Set G) := by
    rcases hc.normal_dichotomy φ.ker with h | h
    · exact (hnontriv h).elim
    · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm φ.ker L).trans h)
  intro x hx
  have hxL : x ∈ L := centralizer_generalizedFitting_le (hker hx)
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  change (⟨x, hxL⟩ : L) ∈ center L
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext ((mem_centralizer_iff.mp (hker hx)) y y.property)

/-- A 2-subgroup acts faithfully under any homomorphism nontrivial on the
quasisimple generalized Fitting subgroup. -/
theorem faithful_on_nontrivial_fitting_image (hcore : pCore 2 G = ⊥)
    (hL : Theory.GroupTheory.IsQuasisimple (generalizedFitting G))
    (φ : G →* H) (hnontriv : ¬ generalizedFitting G ≤ φ.ker)
    {A : Subgroup G} (hA : IsPGroup 2 A) :
    ∀ a ∈ A, φ a = 1 → a = 1 := by
  have hk := kernel_le_fitting_center hL φ hnontriv
  intro a ha hφ
  obtain ⟨z, hz, he⟩ := hk hφ
  have hc : a ∈ centralizer (generalizedFitting G : Set G) := by
    subst a
    intro l hl
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨l, hl⟩)
  exact (disjoint_iff_inf_le.mp (disjoint_centralizer_fitting hcore A hA)) ⟨ha, hc⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSections
