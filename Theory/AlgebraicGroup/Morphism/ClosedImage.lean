module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Theory.AlgebraicGroup.CoordinateRing.Point
public import Theory.AlgebraicGroup.Dimension.Group
public import Theory.AlgebraicGroup.Morphism.CodRestrict

universe u

/-! Constructible ranges and closed images of algebraic-group morphisms -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-! ## Constructibility and closed images of algebraic-group morphisms -/

lemma Variety.Morphism.range_eq_pointPrime_preimage {V W : Variety k}
    [IsAlgClosed k] (f : Variety.Morphism V W) :
    Set.range f.toFun = W.pointPrime ⁻¹'
      Set.range (PrimeSpectrum.comap f.pullbackRingHom) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨V.pointPrime x, f.pointPrime_image x |>.symm⟩
  · intro hy
    rcases hy with ⟨q, hq⟩
    obtain ⟨m, hmmax, hqm⟩ :=
      Ideal.exists_le_maximal q.asIdeal q.2.ne_top
    obtain ⟨x, hx⟩ := V.exists_pointPrime_eq_of_isMaximal m hmmax
    refine ⟨x, ?_⟩
    apply W.pointPrime_injective
    rw [f.pointPrime_image, hx]
    apply PrimeSpectrum.ext
    exact ((W.pointPrime_isMaximal y).eq_of_le
      (Ideal.comap_ne_top f.pullbackRingHom hmmax.ne_top)
      (by
        rw [← hq]
        exact Ideal.comap_mono hqm)).symm

/-- The range of a morphism between presented affine varieties is
constructible. -/
public theorem Variety.Morphism.range_isConstructible {V W : Variety k}
    [IsAlgClosed k] (f : Variety.Morphism V W) :
    Topology.IsConstructible (Set.range f.toFun) := by
  rw [f.range_eq_pointPrime_preimage]
  apply (PrimeSpectrum.isConstructible_range_comap
    f.pullbackRingHom_finitePresentation).preimage W.continuous_pointPrime
  intro S hSopen hSretro U hUcompact hUopen
  exact TopologicalSpace.NoetherianSpace.isCompact _

/-- In a nonempty preirreducible space, a dense constructible set contains a
nonempty open subset. -/
private lemma dense_constructible_contains_open
    {X : Type*} [TopologicalSpace X] [Nonempty X] [PreirreducibleSpace X]
    {S : Set X} (hS : Topology.IsConstructible S) (hSdense : Dense S) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  induction hS using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUretro =>
      exact ⟨U, hUopen, hSdense.nonempty, Set.Subset.rfl⟩
  | union S hS T hT hSih hTih =>
      by_cases hSc : closure S = Set.univ
      · obtain ⟨U, hUopen, hUne, hUS⟩ :=
          hSih (dense_iff_closure_eq.mpr hSc)
        exact ⟨U, hUopen, hUne, hUS.trans Set.subset_union_left⟩
      · have hTc : closure T = Set.univ := by
          by_contra hTc
          have hSopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
          have hTopen : IsOpen (closure T)ᶜ := isClosed_closure.isOpen_compl
          have hSne : (closure S)ᶜ.Nonempty := Set.nonempty_compl.mpr hSc
          have hTne : (closure T)ᶜ.Nonempty := Set.nonempty_compl.mpr hTc
          obtain ⟨x, hxS, hxT⟩ :=
            nonempty_preirreducible_inter hSopen hTopen hSne hTne
          have hxrange : x ∈ closure (S ∪ T) := by
            rw [hSdense.closure_eq]
            trivial
          rw [closure_union] at hxrange
          exact hxrange.elim hxS hxT
        obtain ⟨U, hUopen, hUne, hUT⟩ :=
          hTih (dense_iff_closure_eq.mpr hTc)
        exact ⟨U, hUopen, hUne, hUT.trans Set.subset_union_right⟩
  | compl S hS hSih =>
      by_cases hSc : closure S = Set.univ
      · have hSdense' : Dense S := dense_iff_closure_eq.mpr hSc
        obtain ⟨U, hUopen, hUne, hUS⟩ := hSih hSdense'
        obtain ⟨x, hxU, hxSc⟩ :=
          hSdense.inter_open_nonempty U hUopen hUne
        exact False.elim (hxSc (hUS hxU))
      · refine ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl,
          Set.nonempty_compl.mpr hSc, ?_⟩
        exact Set.compl_subset_compl.mpr subset_closure

/-- The identity component of an algebraic group is open. -/
public theorem identityComponent_isOpen
    (G : Variety k) [AlgebraicGroup G] :
    IsOpen (Theory.AlgebraicGroup.identityComponent G) := by
  obtain ⟨U, hUopen, hUne, hUG₀⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (Theory.AlgebraicGroup.identityComponent G)
      (Theory.AlgebraicGroup.identityComponent_mem_irreducibleComponents G)
  obtain ⟨g, hgU⟩ := hUne
  let H := Theory.AlgebraicGroup.identityComponentSubgroup G
  have hgH : g ∈ H := hUG₀ hgU
  have htranslated : IsOpen ((fun x : Variety.Point G => g⁻¹ * x) '' U) := by
    exact (isOpenMap_mul_left g⁻¹) U hUopen
  have hsubset : (fun x : Variety.Point G => g⁻¹ * x) '' U ⊆ H := by
    rintro _ ⟨x, hxU, rfl⟩
    exact H.mul_mem (H.inv_mem hgH) (hUG₀ hxU)
  have hone : (1 : Variety.Point G) ∈
      (fun x : Variety.Point G => g⁻¹ * x) '' U :=
    ⟨g, hgU, by simp⟩
  exact Subgroup.isOpen_of_mem_nhds H
    (Filter.mem_of_superset (htranslated.mem_nhds hone) hsubset)

/-- A constructible subgroup of an algebraic group is Zariski closed. -/
public theorem constructible_subgroup_isClosed
    (G : Variety k) [AlgebraicGroup G]
    (H : Subgroup (Variety.Point G))
    (hH : Topology.IsConstructible (H : Set (Variety.Point G))) :
    IsClosed (H : Set (Variety.Point G)) := by
  let Ksub : Subgroup (Variety.Point G) :=
    { carrier := closure (H : Set (Variety.Point G))
      one_mem' := subset_closure H.one_mem
      mul_mem' := by
        intro x y hx hy
        exact map_mem_closure₂'
          (fun x => continuous_const_mul x)
          (fun y => continuous_mul_const y)
          hx hy (fun a ha b hb => H.mul_mem ha hb)
      inv_mem' := by
        intro x hx
        apply map_mem_closure (Theory.AlgebraicGroup.invMorphism G).continuous hx
        intro z hz
        change z⁻¹ ∈ (H : Set (Variety.Point G))
        exact H.inv_mem hz }
  let K : ClosedSubgroup G := ClosedSubgroup.ofSubgroup Ksub
    (Variety.isClosed_iff_isZariskiClosed.mp isClosed_closure)
  let HK : Subgroup (Variety.Point K.carrierVariety) :=
    H.comap K.inclusion.onPoints
  have hHKconstructible : Topology.IsConstructible
      (HK : Set (Variety.Point K.carrierVariety)) := by
    change Topology.IsConstructible
      (K.inclusion.onPoints ⁻¹' (H : Set (Variety.Point G)))
    apply hH.preimage K.inclusion.toVariety.continuous
    intro S hSopen hSretro U hUcompact hUopen
    exact TopologicalSpace.NoetherianSpace.isCompact _
  let eK := Variety.closedSubvarietyPointHomeomorph K.isZariskiClosed
  have hKinc : K.inclusion.onPoints =
      (fun x : Variety.Point K.carrierVariety => (eK x).1) := rfl
  have hKinducing : Topology.IsInducing K.inclusion.onPoints := by
    rw [hKinc]
    exact Topology.IsInducing.subtypeVal.comp eK.isInducing
  have hHKimage : K.inclusion.onPoints ''
      (HK : Set (Variety.Point K.carrierVariety)) =
        (H : Set (Variety.Point G)) := by
    change K.inclusion.onPoints ''
      (K.inclusion.onPoints ⁻¹' (H : Set (Variety.Point G))) = H
    rw [Set.image_preimage_eq_inter_range, K.range_inclusion]
    exact Set.inter_eq_left.mpr subset_closure
  have hHKdense : Dense (HK : Set (Variety.Point K.carrierVariety)) := by
    rw [hKinducing.dense_iff]
    intro x
    rw [hHKimage]
    exact (K.pointEquiv x).property
  let L : ClosedSubgroup K.carrierVariety :=
    Theory.AlgebraicGroup.identityComponentClosedSubgroup K.carrierVariety
  let : AlgebraicGroup L.carrierVariety := L.carrierAlgebraicGroup
  let T : Subgroup (Variety.Point L.carrierVariety) :=
    HK.comap L.inclusion.onPoints
  have hTconstructible : Topology.IsConstructible
      (T : Set (Variety.Point L.carrierVariety)) := by
    change Topology.IsConstructible
      (L.inclusion.onPoints ⁻¹'
        (HK : Set (Variety.Point K.carrierVariety)))
    apply hHKconstructible.preimage L.inclusion.toVariety.continuous
    intro S hSopen hSretro U hUcompact hUopen
    exact TopologicalSpace.NoetherianSpace.isCompact _
  let eL := Variety.closedSubvarietyPointHomeomorph L.isZariskiClosed
  have hLinc : L.inclusion.onPoints =
      (fun x : Variety.Point L.carrierVariety => (eL x).1) := rfl
  have hLinducing : Topology.IsInducing L.inclusion.onPoints := by
    rw [hLinc]
    exact Topology.IsInducing.subtypeVal.comp eL.isInducing
  have hLrangeOpen : IsOpen (Set.range L.inclusion.onPoints) := by
    rw [L.range_inclusion]
    exact Theory.AlgebraicGroup.identityComponent_isOpen K.carrierVariety
  have hLopenMap : IsOpenMap L.inclusion.onPoints :=
    hLinducing.isOpenMap hLrangeOpen
  have hTdense : Dense (T : Set (Variety.Point L.carrierVariety)) := by
    change Dense (L.inclusion.onPoints ⁻¹'
      (HK : Set (Variety.Point K.carrierVariety)))
    exact hHKdense.preimage hLopenMap
  have hLcarrier : (L : Set (Variety.Point K.carrierVariety)) =
      Theory.AlgebraicGroup.identityComponent K.carrierVariety := by
    ext x
    rfl
  have hLirr : IsIrreducible
      (L : Set (Variety.Point K.carrierVariety)) := by
    rw [hLcarrier]
    exact Theory.AlgebraicGroup.identityComponent_isIrreducible K.carrierVariety
  let : IrreducibleSpace
      {x : Variety.Point K.carrierVariety // x ∈
        (L : Set (Variety.Point K.carrierVariety))} :=
    Subtype.irreducibleSpace hLirr
  let : IrreducibleSpace (Variety.Point L.carrierVariety) :=
    eL.irreducibleSpace_iff.mpr inferInstance
  obtain ⟨U, hUopen, hUne, hUT⟩ :=
    dense_constructible_contains_open hTconstructible hTdense
  have hUimageOpen : IsOpen (L.inclusion.onPoints '' U) :=
    hLopenMap U hUopen
  have hUimageNe : (L.inclusion.onPoints '' U).Nonempty := hUne.image _
  have hUimageSub : L.inclusion.onPoints '' U ⊆ HK := by
    rintro _ ⟨x, hxU, rfl⟩
    exact hUT hxU
  obtain ⟨y, hyU⟩ := hUimageNe
  have hHKopen : IsOpen (HK : Set (Variety.Point K.carrierVariety)) :=
    Subgroup.isOpen_of_mem_nhds HK
      (Filter.mem_of_superset (hUimageOpen.mem_nhds hyU) hUimageSub)
  have hHKclosed : IsClosed (HK : Set (Variety.Point K.carrierVariety)) :=
    Subgroup.isClosed_of_isOpen HK hHKopen
  have hHKeq : (HK : Set (Variety.Point K.carrierVariety)) = Set.univ := by
    rw [← hHKdense.closure_eq, hHKclosed.closure_eq]
  have hKH : Ksub ≤ H := by
    intro x hxK
    obtain ⟨y, hy⟩ := K.range_inclusion.ge hxK
    have hyHK : y ∈ HK := by
      change y ∈ (HK : Set (Variety.Point K.carrierVariety))
      rw [hHKeq]
      trivial
    change K.inclusion.onPoints y ∈ H at hyHK
    rwa [hy] at hyHK
  have hHKsub : H = Ksub := SetLike.coe_injective
    (Set.Subset.antisymm subset_closure hKH)
  rw [hHKsub]
  exact isClosed_closure

/-- The image of every algebraic-group morphism is Zariski closed. -/
public theorem Morphism.image_isZariskiClosed
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H] [IsAlgClosed k]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    IsZariskiClosed H (f.image : Set (Variety.Point H)) := by
  rw [← Variety.isClosed_iff_isZariskiClosed]
  apply constructible_subgroup_isClosed H f.image
  rw [f.image_carrier]
  exact f.toVariety.range_isConstructible

/-- The image of an arbitrary algebraic-group morphism as a closed subgroup. -/
@[expose]
public def Morphism.imageClosedSubgroup
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H] [IsAlgClosed k]
    (f : Theory.AlgebraicGroup.Morphism G H) : ClosedSubgroup H :=
  ClosedSubgroup.ofSubgroup f.image f.image_isZariskiClosed

public lemma Morphism.imageClosedSubgroup_carrier
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H] [IsAlgClosed k]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    (f.imageClosedSubgroup.toSubgroup : Set (Variety.Point H)) =
      (f.image : Set (Variety.Point H)) := rfl

/-- A dense regular image in a nonempty preirreducible affine-variety point
space contains a nonempty open subset. -/
public lemma Variety.Morphism.exists_nonempty_open_subset_range_of_dense
    {V W : Variety k} [Nonempty (Variety.Point W)]
    [IsAlgClosed k] [PreirreducibleSpace (Variety.Point W)]
    (f : Variety.Morphism V W) (hf : Dense (Set.range f.toFun)) :
    ∃ U : Set (Variety.Point W),
      IsOpen U ∧ U.Nonempty ∧ U ⊆ Set.range f.toFun := by
  exact dense_constructible_contains_open f.range_isConstructible hf

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Restricting a morphism to its closed image is surjective on points. -/
public lemma Morphism.codRestrictImageClosedSubgroup_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hmap : ∀ x, f.onPoints x ∈ f.imageClosedSubgroup.toSubgroup) :
    Function.Surjective
      (f.codRestrictClosedSubgroup f.imageClosedSubgroup hmap).onPoints := by
  intro y
  have hy : f.imageClosedSubgroup.inclusion.onPoints y ∈ f.image :=
    (f.imageClosedSubgroup.pointEquiv y).property
  rcases hy with ⟨x, hx⟩
  refine ⟨x, f.imageClosedSubgroup.inclusion_injective ?_⟩
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  exact hx

/-- The closed image of a connected algebraic group is connected. -/
public theorem Morphism.imageClosedSubgroup_isConnected
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (hG : Variety.IsConnected G) :
    _root_.IsConnected
      (f.imageClosedSubgroup : Set (Variety.Point H)) := by
  have hIset :
      (f.imageClosedSubgroup : Set (Variety.Point H)) =
        Set.range f.onPoints := by
    exact f.imageClosedSubgroup_carrier.trans f.image_carrier
  rw [hIset]
  let : ConnectedSpace (Variety.Point G) :=
    connectedSpace_iff_univ.mpr hG
  exact isConnected_range f.toVariety.continuous

/-- The closed image of a solvable algebraic group has solvable points. -/
public theorem Morphism.imageClosedSubgroup_isSolvable
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hG : Group.IsSolvable (Variety.Point G)) :
    Group.IsSolvable (Variety.Point f.imageClosedSubgroup.carrierVariety) := by
  let I := f.imageClosedSubgroup
  let : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let hmap : ∀ x, f.onPoints x ∈ I.toSubgroup := fun x => ⟨x, rfl⟩
  let fI : AlgebraicGroup.Morphism G I.carrierVariety :=
    f.codRestrictClosedSubgroup I hmap
  let : Group.IsSolvable (Variety.Point G) := hG
  exact Group.isSolvable_of_surjective
    (f := fI.onPoints) (f.codRestrictImageClosedSubgroup_surjective hmap)

end

/-! Canonical surjective projection onto the closed image of a morphism. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma Morphism.closedImageProjection_exists
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) :
    ∃ π : AlgebraicGroup.Morphism G f.imageClosedSubgroup.carrierVariety,
      Function.Surjective π.onPoints ∧
      π.kernel = f.kernel ∧
      ∀ x, f.imageClosedSubgroup.inclusion.onPoints (π.onPoints x) = f.onPoints x := by
  let hmap : ∀ x, f.onPoints x ∈ f.imageClosedSubgroup.toSubgroup := fun x => ⟨x, rfl⟩
  let π := f.codRestrictClosedSubgroup f.imageClosedSubgroup hmap
  refine ⟨π, f.codRestrictImageClosedSubgroup_surjective hmap, ?_, ?_⟩
  · exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_kernel_eq f
      f.imageClosedSubgroup hmap
  · intro x
    exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply f
      f.imageClosedSubgroup hmap x

end
end Theory.AlgebraicGroup
