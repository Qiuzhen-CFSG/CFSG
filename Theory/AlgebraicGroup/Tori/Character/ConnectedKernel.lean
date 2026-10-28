module

public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Tori.Character.Basis
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Semisimple

/-!
Connected kernels of nontrivial torus characters.

This module formalizes Borel, *Linear Algebraic Groups*, Chapter IV, 13.2:
if `chi` is a nontrivial character of a torus `T`, then `(ker chi)^0` is a
subtorus of codimension one.  The character classification shows that `chi` is
surjective onto the one-dimensional torus, so the morphism dimension formula
gives the codimension statement.  Connectedness is built into the identity
component, while commutativity and semisimplicity descend from `T` and identify
that component as a torus.

For use in centralizer geometry, `ambientConnectedKernel` maps the connected
kernel through a closed-subgroup inclusion.  The main theorem also records its
exact points, containment, connectedness, torus structure, and unchanged
dimension in the ambient algebraic group.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma closedSubgroup_carrier_isConnected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private lemma TorusCharacter.onPoints_surjective_of_ne_one
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    (chi : TorusCharacter T) (hchi : chi ≠ 1) :
    Function.Surjective chi.onPoints := by
  intro y
  let c : k := dPointEquiv 1 y 0
  have hc : c ≠ 0 := Units.ne_zero (dPointEquiv 1 y 0)
  obtain ⟨x, hx⟩ := chi.exists_pointCharacter_eq_of_ne_one hT hchi c hc
  refine ⟨x, ?_⟩
  apply (dPointEquiv 1).injective
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply Units.ext
  exact hx

private noncomputable def topClosedSubgroupIso
    (G : Variety k) [AlgebraicGroup G] :
    AlgebraicGroup.Iso G (ClosedSubgroup.top (G := G)).carrierVariety := by
  let topG : ClosedSubgroup G := ClosedSubgroup.top
  let toTop : AlgebraicGroup.Morphism G topG.carrierVariety :=
    (AlgebraicGroup.Morphism.id G).codRestrictClosedSubgroup topG
      (fun _ => trivial)
  exact
    { hom := toTop
      inv := topG.inclusion
      hom_inv_id := by intro x; rfl
      inv_hom_id := by
        intro y
        apply topG.inclusion_injective
        rfl }

private lemma TorusCharacter.image_dimension_eq_one_of_ne_one
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    (chi : TorusCharacter T) (hchi : chi ≠ 1) :
    Variety.dimension chi.imageClosedSubgroup.carrierVariety = 1 := by
  have hsurj := chi.onPoints_surjective_of_ne_one hT hchi
  have himage : chi.imageClosedSubgroup = ClosedSubgroup.top := by
    apply SetLike.coe_injective
    ext y
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨x, rfl⟩ := hsurj y
      change chi.onPoints x ∈ chi.image
      exact ⟨x, rfl⟩
  let topKMult : ClosedSubgroup (KMult k) := ClosedSubgroup.top
  letI : AlgebraicGroup topKMult.carrierVariety :=
    topKMult.carrierAlgebraicGroup
  have htopDimension :
      Variety.dimension topKMult.carrierVariety =
        Variety.dimension (KMult k) :=
    (algebraicGroupIso_dimension_eq
      (topClosedSubgroupIso (KMult k))).symm
  rw [himage]
  rw [htopDimension]
  exact dVariety_dimension_eq 1

private lemma Morphism.imageClosedSubgroup_dimension_eq_of_injective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (hf : Function.Injective f.onPoints) :
    Variety.dimension f.imageClosedSubgroup.carrierVariety =
      Variety.dimension G := by
  letI : Subsingleton f.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hf
    have hx : f.onPoints x.val = 1 := x.property
    have hy : f.onPoints y.val = 1 := y.property
    rw [hx, hy]
  letI : Subsingleton
      (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
    f.kernelClosedSubgroup.pointEquiv.subsingleton
  letI : Finite (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
    Finite.of_subsingleton
  have hker : Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points f.kernelClosedSubgroup.carrierVariety).2
      inferInstance
  have hdim := morphism_dimension_eq_kernel_add_image f
  rw [hker, zero_add] at hdim
  exact hdim.symm

/-- The identity component of the kernel of a torus character. -/
@[expose]
public noncomputable def TorusCharacter.connectedKernel
    {T : Variety k} [AlgebraicGroup T] (chi : TorusCharacter T) :
    ClosedSubgroup T :=
  chi.kernelClosedSubgroup.identityComponentAmbient

/-- The connected character kernel mapped through a closed-subgroup inclusion. -/
@[expose]
public noncomputable def TorusCharacter.ambientConnectedKernel
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (chi : TorusCharacter T.carrierVariety) : ClosedSubgroup G := by
  let Kchi := chi.connectedKernel
  letI : AlgebraicGroup Kchi.carrierVariety :=
    Kchi.carrierAlgebraicGroup
  exact (T.inclusion.comp Kchi.inclusion).imageClosedSubgroup

/-- The geometric package attached to a nontrivial character kernel. -/
public structure TorusCharacter.ConnectedKernelCodimensionOne
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (chi : TorusCharacter T.carrierVariety) : Prop where
  connectedKernel_isSubtorus : IsSubtorus chi.connectedKernel
  ambientConnectedKernel_isSubtorus : IsSubtorus (chi.ambientConnectedKernel T)
  connectedKernel_connected :
    _root_.IsConnected
      (chi.connectedKernel : Set (Variety.Point T.carrierVariety))
  ambientConnectedKernel_connected :
    _root_.IsConnected
      (chi.ambientConnectedKernel T : Set (Variety.Point G))
  ambientConnectedKernel_le : chi.ambientConnectedKernel T ≤ T
  mem_ambientConnectedKernel_iff (x : Variety.Point G) :
    x ∈ chi.ambientConnectedKernel T ↔
      ∃ y : Variety.Point T.carrierVariety,
        y ∈ chi.connectedKernel ∧ T.inclusion.onPoints y = x
  connectedKernel_dimension_add_one :
    Variety.dimension chi.connectedKernel.carrierVariety + 1 =
      Variety.dimension T.carrierVariety
  ambientConnectedKernel_dimension_add_one :
    Variety.dimension (chi.ambientConnectedKernel T).carrierVariety + 1 =
      Variety.dimension T.carrierVariety

/-- The connected kernel of a nontrivial character of a torus, and its image
in any ambient algebraic group, are codimension-one subtori. -/
public theorem TorusCharacter.connectedKernel_codimension_one
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsSubtorus T) (chi : TorusCharacter T.carrierVariety)
    (hchi : chi ≠ 1) : chi.ConnectedKernelCodimensionOne T := by
  let Kchi := chi.connectedKernel
  letI : AlgebraicGroup Kchi.carrierVariety :=
    Kchi.carrierAlgebraicGroup
  let j : AlgebraicGroup.Morphism Kchi.carrierVariety G :=
    T.inclusion.comp Kchi.inclusion
  have hAmbientEq : chi.ambientConnectedKernel T = j.imageClosedSubgroup := by
    rfl
  have hKconnected :
      _root_.IsConnected (Kchi : Set (Variety.Point T.carrierVariety)) :=
    chi.kernelClosedSubgroup.identityComponentAmbient_isConnected
  have hKconnectedVariety : Variety.IsConnected Kchi.carrierVariety :=
    closedSubgroup_carrier_isConnected Kchi hKconnected
  have hKcomm : IsMulCommutative (Variety.Point Kchi.carrierVariety) := by
    rw [isMulCommutative_iff]
    intro x y
    apply Kchi.inclusion_injective
    simpa only [map_mul] using
      (isMulCommutative_iff.mp hT.isMulCommutative
        (Kchi.inclusion.onPoints x) (Kchi.inclusion.onPoints y))
  have hKsemi : ∀ x : Variety.Point Kchi.carrierVariety,
      IsSemisimpleElement Kchi.carrierVariety x := by
    intro x
    have hxT := hT.all_semisimple (Kchi.inclusion.onPoints x)
    simpa using
      (closedSubgroup_semisimpleElement_iff Kchi
        (Kchi.pointEquiv x).property).mp hxT
  have hKtorus : IsSubtorus Kchi :=
    isTorus_of_isConnected_isMulCommutative_all_semisimple
      hKconnectedVariety hKcomm hKsemi
  have hStor : IsSubtorus (chi.ambientConnectedKernel T) := by
    rw [hAmbientEq]
    exact morphism_image_isTorus j hKtorus
  have hSconnected :
      _root_.IsConnected
        (chi.ambientConnectedKernel T : Set (Variety.Point G)) := by
    rw [hAmbientEq]
    exact j.imageClosedSubgroup_isConnected hKtorus.isConnected
  have hmem (x : Variety.Point G) :
      x ∈ chi.ambientConnectedKernel T ↔
        ∃ y : Variety.Point T.carrierVariety,
          y ∈ Kchi ∧ T.inclusion.onPoints y = x := by
    rw [hAmbientEq]
    change (∃ y : Variety.Point Kchi.carrierVariety,
      j.onPoints y = x) ↔ _
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Kchi.inclusion.onPoints y, (Kchi.pointEquiv y).property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      let yK : Variety.Point Kchi.carrierVariety :=
        Kchi.pointEquiv.symm ⟨y, hy⟩
      refine ⟨yK, ?_⟩
      change T.inclusion.onPoints (Kchi.inclusion.onPoints yK) =
        T.inclusion.onPoints y
      congr 1
  have hSle : chi.ambientConnectedKernel T ≤ T := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := (hmem x).mp hx
    exact (T.pointEquiv y).property
  have hImageDim : Variety.dimension chi.imageClosedSubgroup.carrierVariety = 1 :=
    chi.image_dimension_eq_one_of_ne_one hT hchi
  have hdim := morphism_dimension_eq_kernel_add_image chi
  rw [hImageDim] at hdim
  have hKdim : Variety.dimension Kchi.carrierVariety + 1 =
      Variety.dimension T.carrierVariety := by
    have hKchiDimension :=
      ClosedSubgroup.dimension_identityComponentAmbient
        chi.kernelClosedSubgroup
    change Variety.dimension Kchi.carrierVariety =
      Variety.dimension chi.kernelClosedSubgroup.carrierVariety at hKchiDimension
    calc
      Variety.dimension Kchi.carrierVariety + 1 =
          Variety.dimension chi.kernelClosedSubgroup.carrierVariety + 1 := by
            rw [hKchiDimension]
      _ = Variety.dimension T.carrierVariety := hdim.symm
  have hSdim : Variety.dimension (chi.ambientConnectedKernel T).carrierVariety =
      Variety.dimension Kchi.carrierVariety := by
    rw [hAmbientEq]
    exact j.imageClosedSubgroup_dimension_eq_of_injective
      (T.inclusion_injective.comp Kchi.inclusion_injective)
  exact
    { connectedKernel_isSubtorus := hKtorus
      ambientConnectedKernel_isSubtorus := hStor
      connectedKernel_connected := hKconnected
      ambientConnectedKernel_connected := hSconnected
      ambientConnectedKernel_le := hSle
      mem_ambientConnectedKernel_iff := hmem
      connectedKernel_dimension_add_one := hKdim
      ambientConnectedKernel_dimension_add_one := by rw [hSdim]; exact hKdim }

end Theory.AlgebraicGroup
