module

public import Theory.AlgebraicGroup.Tori.Centralizer
public import Theory.AlgebraicGroup.Tori.Character.Basis
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Semisimple

universe u

set_option linter.style.haveILetI false

/-! Character and commutator methods for extensions with torus kernel. -/

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def commutatorToKernel
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hTcomm : IsMulCommutative (Variety.Point T))
    (hker : IsSubtorus f.kernelClosedSubgroup)
    (y : Variety.Point G) :
    AlgebraicGroup.Morphism G f.kernelClosedSubgroup.carrierVariety := by
  rw [isMulCommutative_iff] at hTcomm
  let N := f.kernelClosedSubgroup
  letI : AlgebraicGroup N.carrierVariety := N.carrierAlgebraicGroup
  let slice := (AlgebraicGroup.commutatorMorphism G).comp
    ((Variety.Morphism.id G).pair (Variety.Morphism.const G G y))
  have hmap (x : Variety.Point G) : slice.toFun x ∈ N.toSubgroup := by
    change f.onPoints (x * y * x⁻¹ * y⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hTcomm (f.onPoints x) (f.onPoints y)]
    group
  let sliceN : Variety.Morphism G N.carrierVariety :=
    { toFun := fun x => N.pointEquiv.symm ⟨slice.toFun x, hmap x⟩
      regular := by
        intro i
        obtain ⟨p, hp⟩ := slice.regular i
        refine ⟨p, ?_⟩
        intro x
        change (N.pointEquiv
          (N.pointEquiv.symm ⟨slice.toFun x, hmap x⟩)).val.val i =
          evalPolynomial x.val p
        rw [N.pointEquiv.apply_symm_apply]
        exact hp x }
  have hsliceN (x : Variety.Point G) :
      N.inclusion.onPoints (sliceN.toFun x) = slice.toFun x := by
    change (N.pointEquiv
      (N.pointEquiv.symm ⟨slice.toFun x, hmap x⟩)).val = slice.toFun x
    rw [N.pointEquiv.apply_symm_apply]
  exact
    { toVariety := sliceN
      map_one := by
        apply N.inclusion_injective
        rw [hsliceN]
        change (AlgebraicGroup.commutatorMorphism G).toFun
          ((Variety.prodPointEquiv G G).symm (1, y)) = 1
        rw [AlgebraicGroup.commutatorMorphism_apply]
        simp
      map_mul := by
        intro a b
        apply N.inclusion_injective
        rw [map_mul, hsliceN, hsliceN, hsliceN]
        change ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hbmem : ⁅b, y⁆ ∈ N.toSubgroup := hmap b
        let bN : Variety.Point N.carrierVariety :=
          N.pointEquiv.symm ⟨⁅b, y⁆, hbmem⟩
        have hbcentral := connected_centralizes_normal_subtorus
          hG N hker f.kernelClosedSubgroup_isNormal a bN
        have hbval : N.inclusion.onPoints bN = ⁅b, y⁆ := by
          change (N.pointEquiv bN).val = ⁅b, y⁆
          simp [bN]
        rw [hbval] at hbcentral
        rw [hbcentral]
        have hamem : ⁅a, y⁆ ∈ N.toSubgroup := hmap a
        let aN : Variety.Point N.carrierVariety :=
          N.pointEquiv.symm ⟨⁅a, y⁆, hamem⟩
        have hkercomm := hker.isMulCommutative
        rw [isMulCommutative_iff] at hkercomm
        have hab := hkercomm aN bN
        have hab' := congrArg N.inclusion.onPoints hab
        simp only [map_mul] at hab'
        have haval : N.inclusion.onPoints aN = ⁅a, y⁆ := by
          change (N.pointEquiv aN).val = ⁅a, y⁆
          simp [aN]
        rw [haval, hbval] at hab'
        exact hab'.symm }

private noncomputable def commutatorCharacter
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hTcomm : IsMulCommutative (Variety.Point T))
    (hker : IsSubtorus f.kernelClosedSubgroup)
    (χ : TorusCharacter f.kernelClosedSubgroup.carrierVariety)
    (y : Variety.Point G) : TorusCharacter G :=
  χ.comp (commutatorToKernel f hG hTcomm hker y)

omit [IsAlgClosed k] in
private lemma commutatorToKernel_inclusion_apply
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hTcomm : IsMulCommutative (Variety.Point T))
    (hker : IsSubtorus f.kernelClosedSubgroup)
    (x y : Variety.Point G) :
    f.kernelClosedSubgroup.inclusion.onPoints
      ((commutatorToKernel f hG hTcomm hker y).onPoints x) = ⁅x, y⁆ := by
  rw [commutatorToKernel]
  change (f.kernelClosedSubgroup.pointEquiv
    (f.kernelClosedSubgroup.pointEquiv.symm ⟨_, _⟩)).val = ⁅x, y⁆
  rw [f.kernelClosedSubgroup.pointEquiv.apply_symm_apply]
  exact AlgebraicGroup.commutatorMorphism_apply G x y

omit [IsAlgClosed k] in
private lemma commutatorCharacter_range_finite
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hTcomm : IsMulCommutative (Variety.Point T))
    (hker : IsSubtorus f.kernelClosedSubgroup)
    (χ : TorusCharacter f.kernelClosedSubgroup.carrierVariety) :
    (Set.range fun y : Variety.Point G =>
      commutatorCharacter f hG hTcomm hker χ y).Finite := by
  let N := f.kernelClosedSubgroup
  letI : AlgebraicGroup N.carrierVariety := N.carrierAlgebraicGroup
  obtain ⟨q, hq⟩ :=
    N.exists_polynomialFunction_extension χ.scalarPolynomialFunction
  obtain ⟨W, hWfg, hW⟩ :=
    (AlgebraicGroup.commutatorMorphism G).secondSlices_mem_finiteSubmodule q
  have hmem (y : Variety.Point G) :
      (commutatorCharacter f hG hTcomm hker χ y).scalarPolynomialFunction ∈
        W := by
    have hs := hW y
    convert hs using 1
    apply Variety.PolynomialFunction.ext
    intro x
    change χ.scalarPolynomialFunction
      ((commutatorToKernel f hG hTcomm hker y).onPoints x) = q _
    symm
    rw [show ((AlgebraicGroup.commutatorMorphism G).comp
      ((Variety.Morphism.id G).pair
        (Variety.Morphism.const G G y))).toFun x = ⁅x, y⁆ by
          exact AlgebraicGroup.commutatorMorphism_apply G x y]
    rw [← commutatorToKernel_inclusion_apply f hG hTcomm hker x y]
    exact hq _
  let C : Set (TorusCharacter G) := Set.range fun y : Variety.Point G =>
    commutatorCharacter f hG hTcomm hker χ y
  let v : C → W := fun c =>
    ⟨c.1.scalarPolynomialFunction, by
      rcases c.2 with ⟨y, hy⟩
      rw [← hy]
      exact hmem y⟩
  have hvAmbient : LinearIndependent k
      (fun c : C => c.1.scalarPolynomialFunction) :=
    (torusCharacter_scalarPolynomialFunction_linearIndependent G).comp
      (fun c : C => c.1) Subtype.val_injective
  have hv : LinearIndependent k v := by
    apply LinearIndependent.of_comp W.subtype
    exact hvAmbient
  let : Module.Finite k W :=
    Module.Finite.of_fg_top ((Submodule.fg_top W).mpr hWfg)
  let : IsNoetherian k W :=
    isNoetherian_of_isNoetherianRing_of_finite k W
  let : Finite C := hv.finite_of_isNoetherian
  change C.Finite
  exact Set.finite_coe_iff.mp inferInstance

omit [IsAlgClosed k] in
private lemma commutatorCharacter_eq_one_of_connected
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hTcomm : IsMulCommutative (Variety.Point T))
    (hker : IsSubtorus f.kernelClosedSubgroup)
    (χ : TorusCharacter f.kernelClosedSubgroup.carrierVariety)
    (y : Variety.Point G) :
    commutatorCharacter f hG hTcomm hker χ y = 1 := by
  have hTcomm' := hTcomm
  rw [isMulCommutative_iff] at hTcomm'
  let N := f.kernelClosedSubgroup
  letI : AlgebraicGroup N.carrierVariety := N.carrierAlgebraicGroup
  let characterFamily (z : Variety.Point G) : TorusCharacter G :=
    commutatorCharacter f hG hTcomm hker χ z
  have hfamilyFinite : (Set.range characterFamily).Finite :=
    commutatorCharacter_range_finite f hG hTcomm hker χ
  apply AlgebraicGroup.Morphism.ext
  funext x
  let slice := (AlgebraicGroup.commutatorMorphism G).comp
    ((Variety.Morphism.const G G x).pair (Variety.Morphism.id G))
  have hmap (z : Variety.Point G) : slice.toFun z ∈ N.toSubgroup := by
    change f.onPoints (x * z * x⁻¹ * z⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hTcomm' (f.onPoints x) (f.onPoints z)]
    group
  let sliceN : Variety.Morphism G N.carrierVariety :=
    { toFun := fun z => N.pointEquiv.symm ⟨slice.toFun z, hmap z⟩
      regular := by
        intro i
        obtain ⟨p, hp⟩ := slice.regular i
        refine ⟨p, ?_⟩
        intro z
        change (N.pointEquiv
          (N.pointEquiv.symm ⟨slice.toFun z, hmap z⟩)).val.val i =
          evalPolynomial z.val p
        rw [N.pointEquiv.apply_symm_apply]
        exact hp z }
  let valueMorphism : Variety.Morphism G (KMult k) :=
    χ.toVariety.comp sliceN
  have hvalue (z : Variety.Point G) :
      valueMorphism.toFun z = (characterFamily z).onPoints x := by
    change χ.toVariety.toFun (sliceN.toFun z) =
      χ.toVariety.toFun ((commutatorToKernel f hG hTcomm hker z).onPoints x)
    congr 1
  have hvalueFinite : (Set.range valueMorphism.toFun).Finite := by
    apply (hfamilyFinite.image fun ψ : TorusCharacter G => ψ.onPoints x).subset
    rintro w ⟨z, rfl⟩
    exact ⟨characterFamily z, ⟨z, rfl⟩, (hvalue z).symm⟩
  have hsub := connected_finite_morphism_range_subsingleton
    valueMorphism hG hvalueFinite
  have heq := hsub ⟨y, rfl⟩ ⟨1, rfl⟩
  rw [hvalue y, hvalue 1] at heq
  have hone : (characterFamily 1).onPoints x = 1 := by
    change χ.onPoints
      ((commutatorToKernel f hG hTcomm hker 1).onPoints x) = 1
    have hcOne :
        (commutatorToKernel f hG hTcomm hker 1).onPoints x = 1 := by
      apply N.inclusion_injective
      rw [commutatorToKernel_inclusion_apply f hG hTcomm hker x 1]
      simp
    rw [hcOne, map_one]
  exact heq.trans hone

omit [IsAlgClosed k] in
private lemma connected_isMulCommutative_of_torus_kernel
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hTcomm : IsMulCommutative (Variety.Point T))
    (hker : IsSubtorus f.kernelClosedSubgroup) :
    IsMulCommutative (Variety.Point G) := by
  rw [isMulCommutative_iff]
  intro x y
  let N := f.kernelClosedSubgroup
  letI : AlgebraicGroup N.carrierVariety := N.carrierAlgebraicGroup
  have hc : (commutatorToKernel f hG hTcomm hker y).onPoints x = 1 := by
    have hkerModel := hker
    obtain ⟨n, ⟨e⟩⟩ := hkerModel
    have hinv : Function.Injective e.inv.onPoints :=
      Function.LeftInverse.injective (fun z => e.inv_hom_id z)
    apply hinv
    apply (dPointEquiv n).injective
    funext i
    let χ : TorusCharacter N.carrierVariety :=
      (dCoordinateCharacter n i).comp e.inv
    have hχ := commutatorCharacter_eq_one_of_connected
      f hG hTcomm hker χ y
    have hv := congrArg (fun ψ : TorusCharacter G => ψ.onPoints x) hχ
    change (dCoordinateCharacter n i).onPoints
      (e.inv.onPoints
        ((commutatorToKernel f hG hTcomm hker y).onPoints x)) = 1 at hv
    have hv' := congrFun (congrArg (dPointEquiv 1) hv) 0
    change dPointEquiv n
      (e.inv.onPoints
        ((commutatorToKernel f hG hTcomm hker y).onPoints x)) i = 1 at hv'
    rw [map_one, dPointEquiv_one]
    exact hv'
  have hamb := congrArg N.inclusion.onPoints hc
  rw [commutatorToKernel_inclusion_apply f hG hTcomm hker x y,
    map_one] at hamb
  exact commutatorElement_eq_one_iff_mul_comm.mp hamb

private lemma connected_isTorus_of_finiteKernel_to_torus_of_kernel_semisimple
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hker : Finite f.kernel)
    (hkerSemi : ∀ x, x ∈ f.kernel → IsSemisimpleElement G x)
    (hT : IsTorus T) :
    IsTorus G := by
  have hGcomm : IsMulCommutative (Variety.Point G) :=
    connected_isMulCommutative_of_finiteKernel
      f hG hker hT.isMulCommutative
  have hGsemi : ∀ x : Variety.Point G, IsSemisimpleElement G x := by
    intro x
    let dG := jordanDecomposition x
    let imageDecomposition : JordanDecomposition (f.onPoints x) :=
      { semisimplePart := f.onPoints dG.semisimplePart
        unipotentPart := f.onPoints dG.unipotentPart
        eq_mul := by
          calc
            f.onPoints x = f.onPoints
                (dG.semisimplePart * dG.unipotentPart) :=
              congrArg f.onPoints dG.eq_mul
            _ = f.onPoints dG.semisimplePart *
                f.onPoints dG.unipotentPart := map_mul f.onPoints _ _
        commute := dG.commute.map f.onPoints
        semisimple :=
          morphism_preserves_semisimpleElement f _ dG.semisimple
        unipotent := morphism_preserves_unipotentElement f _ dG.unipotent }
    let trivialDecomposition : JordanDecomposition (f.onPoints x) :=
      { semisimplePart := f.onPoints x
        unipotentPart := 1
        eq_mul := by simp
        commute := Commute.one_right _
        semisimple := hT.all_semisimple (f.onPoints x)
        unipotent := one_isUnipotentElement T }
    have himage : imageDecomposition = trivialDecomposition :=
      imageDecomposition.unique trivialDecomposition
    have hxuKer : dG.unipotentPart ∈ f.kernel := by
      change f.onPoints dG.unipotentPart = 1
      exact congrArg JordanDecomposition.unipotentPart himage
    have hxueq : dG.unipotentPart = 1 :=
      semisimple_unipotent_eq_one dG.unipotentPart
        (hkerSemi dG.unipotentPart hxuKer) dG.unipotent
    rw [dG.eq_mul, hxueq, mul_one]
    exact dG.semisimple
  exact isTorus_of_isConnected_isMulCommutative_all_semisimple
    hG hGcomm hGsemi

private lemma connected_isTorus_of_finiteKernel_to_torus
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hker : Finite f.kernel)
    (hT : IsTorus T) :
    IsTorus G :=
  connected_isTorus_of_finiteKernel_to_torus_of_kernel_semisimple
    f hG hker
      (connected_finiteKernel_to_torus_kernel_isSemisimple f hG hker hT) hT

/-- The identity component of the closed preimage of a subtorus under a
finite-kernel morphism is a subtorus. -/
public theorem closedSubgroupPreimage_identityComponent_isSubtorus
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (hker : Finite f.kernel)
    (S : ClosedSubgroup H) (hS : IsSubtorus S) :
    let P := f.closedSubgroupPreimage S
    IsSubtorus
      (AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety) := by
  dsimp only
  let P := f.closedSubgroupPreimage S
  let P₀ := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P₀.carrierVariety := P₀.carrierAlgebraicGroup
  let fP₀ : AlgebraicGroup.Morphism P₀.carrierVariety H :=
    f.comp (P.inclusion.comp P₀.inclusion)
  have hfP₀mem (x : Variety.Point P₀.carrierVariety) :
      fP₀.onPoints x ∈ S.toSubgroup :=
    (P.pointEquiv (P₀.inclusion.onPoints x)).property
  let r : AlgebraicGroup.Morphism P₀.carrierVariety S.carrierVariety :=
    fP₀.codRestrictClosedSubgroup S hfP₀mem
  have hrker : Finite r.kernel := by
    let embed : r.kernel → f.kernel := fun x => ⟨
      P.inclusion.onPoints (P₀.inclusion.onPoints x.1), by
        have hx := x.2
        change r.onPoints x.1 = 1 at hx
        have hx' := congrArg S.inclusion.onPoints hx
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
          at hx'
        exact hx'⟩
    exact Finite.of_injective embed (by
      intro x y hxy
      apply Subtype.ext
      apply P₀.inclusion_injective
      apply P.inclusion_injective
      exact congrArg (fun z : f.kernel => z.1) hxy)
  have hP₀conn : Variety.IsConnected P₀.carrierVariety :=
    identityComponentClosedSubgroup_carrier_isConnected P.carrierVariety
  exact connected_isTorus_of_finiteKernel_to_torus r hP₀conn hrker hS

/-- A connected algebraic group with torus closed kernel and torus target is
a torus. -/
public theorem connected_isTorus_of_torus_kernel_to_torus
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hker : IsSubtorus f.kernelClosedSubgroup)
    (hT : IsTorus T) :
    IsTorus G := by
  have hGcomm : IsMulCommutative (Variety.Point G) :=
    connected_isMulCommutative_of_torus_kernel
      f hG hT.isMulCommutative hker
  have hGsemi := semisimple_of_torus_kernel_to_torus f hker hT
  exact isTorus_of_isConnected_isMulCommutative_all_semisimple
    hG hGcomm hGsemi

/-- If a morphism has torus closed kernel, then the closed kernel of its
restriction from the identity component of a closed preimage is a torus. -/
public theorem Morphism.preimageRestriction_identityComponent_kernel_isSubtorus
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q)
    (S : ClosedSubgroup Q)
    (hker : IsSubtorus q.kernelClosedSubgroup) :
    let P := q.closedSubgroupPreimage S
    let _ : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
    let P₀ := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
    let _ : AlgebraicGroup P₀.carrierVariety := P₀.carrierAlgebraicGroup
    let r := (q.preimageRestriction S).comp P₀.inclusion
    IsSubtorus r.kernelClosedSubgroup := by
  let K := q.kernelClosedSubgroup
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  let P := q.closedSubgroupPreimage S
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let P₀ := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P₀.carrierVariety := P₀.carrierAlgebraicGroup
  let r := (q.preimageRestriction S).comp P₀.inclusion
  change IsSubtorus r.kernelClosedSubgroup
  have hKP (z : Variety.Point K.carrierVariety) :
      K.inclusion.onPoints z ∈ P.toSubgroup := by
    change q.onPoints (K.inclusion.onPoints z) ∈ S.toSubgroup
    have hz : q.onPoints (K.inclusion.onPoints z) = 1 :=
      (K.pointEquiv z).property
    rw [hz]
    exact S.toSubgroup.one_mem
  let kP : AlgebraicGroup.Morphism K.carrierVariety P.carrierVariety :=
    K.inclusion.codRestrictClosedSubgroup P hKP
  have hKP₀ (z : Variety.Point K.carrierVariety) :
      kP.onPoints z ∈ P₀.toSubgroup := by
    change kP.onPoints z ∈ AlgebraicGroup.identityComponent P.carrierVariety
    have hz₀ : z ∈ AlgebraicGroup.identityComponent K.carrierVariety := by
      rw [(identityComponent_eq_univ_iff_isConnected K.carrierVariety).mpr
        hker.isConnected]
      trivial
    exact kP.image_identityComponent_subset ⟨z, hz₀, rfl⟩
  let j : AlgebraicGroup.Morphism K.carrierVariety P₀.carrierVariety :=
    kP.codRestrictClosedSubgroup P₀ hKP₀
  have hjImage : r.kernelClosedSubgroup = j.imageClosedSubgroup := by
    apply SetLike.coe_injective
    ext z
    change r.onPoints z = 1 ↔ z ∈ j.image
    constructor
    · intro hz
      have hqz : q.onPoints
          (P.inclusion.onPoints (P₀.inclusion.onPoints z)) = 1 := by
        rw [← q.preimageRestriction_inclusion_apply S]
        change (q.preimageRestriction S).onPoints
            (P₀.inclusion.onPoints z) = 1 at hz
        rw [hz]
        exact S.inclusion.map_one
      let zK : Variety.Point K.carrierVariety := K.pointEquiv.symm
        ⟨P.inclusion.onPoints (P₀.inclusion.onPoints z), hqz⟩
      refine ⟨zK, ?_⟩
      apply P₀.inclusion_injective
      apply P.inclusion_injective
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      change K.inclusion.onPoints zK =
        P.inclusion.onPoints (P₀.inclusion.onPoints z)
      change (K.pointEquiv zK).val = _
      simp [zK]
    · rintro ⟨zK, rfl⟩
      change (q.preimageRestriction S).onPoints
        (P₀.inclusion.onPoints (j.onPoints zK)) = 1
      apply S.inclusion_injective
      rw [q.preimageRestriction_inclusion_apply]
      trans 1
      · rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        exact (K.pointEquiv zK).property
      · exact S.inclusion.map_one.symm
  rw [hjImage]
  exact morphism_image_isTorus j hker

end Theory.AlgebraicGroup
