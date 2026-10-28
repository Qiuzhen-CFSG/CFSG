module

public import Mathlib.Algebra.Lie.Weights.Killing
public import Theory.AlgebraicGroup.Reductive.LieRadical
public import Theory.AlgebraicGroup.RootSubgroups.TangentLieRootSpace

/-!
# The semisimple tangent quotient of a reductive algebraic group

In characteristic zero, reductivity identifies the radical of the canonical
identity-tangent Lie algebra with its center.  This module therefore uses the
central quotient, rather than the generally non-semisimple full tangent Lie
algebra, as the semisimple tangent object.  It proves that this quotient has
trivial radical and hence Mathlib's nondegenerate-Killing-form structure.
The quotient map is the canonical Lie homomorphism associated to the center.

For a maximal torus, its tangent image descends to an abelian, nilpotent
subalgebra of the quotient.  Every torus weight that actually occurs in the
identity tangent descends with its character differential, and its image is
identified with the corresponding generalized Lie root space under the same
faithful-differentiation, spanning, and differentiated-bracket hypotheses used
by the canonical tangent API.  An explicit zero-weight exhaustion hypothesis
then identifies the torus image as a Cartan subalgebra; this is kept explicit
because its geometric proof belongs to the separate maximal-torus centralizer
development.  The Killing theorem consequently gives one-dimensional nonzero
quotient root spaces.

The radical input is
`identityTangent_hasCentralRadical_of_reductive`; the weight and bracket inputs
come from `TangentLieRootSpace`.  No Killing instance is asserted for the full
identity tangent, and no root-subgroup classification result is used.
-/

open scoped LieRing

universe u v

namespace Theory.AlgebraicGroup

section Abstract

variable {F : Type u} [Field F]
variable {L : Type v} [LieRing L] [LieAlgebra F L]

/-- The canonical Lie-algebra quotient map. -/
@[expose]
public def lieIdealQuotientMap (I : LieIdeal F L) : L →ₗ⁅F⁆ L ⧸ I where
  toLinearMap := I.toSubmodule.mkQ
  map_lie' := by
    intro x y
    exact LieSubmodule.Quotient.mk_bracket I x y

@[simp]
public theorem lieIdealQuotientMap_apply (I : LieIdeal F L) (x : L) :
    lieIdealQuotientMap I x = (LieSubmodule.Quotient.mk x : L ⧸ I) := rfl

public theorem hasTrivialRadical_quotient_center
    [LieAlgebra.HasCentralRadical F L] :
    LieAlgebra.HasTrivialRadical F (L ⧸ LieAlgebra.center F L) := by
  let Z : LieIdeal F L := LieAlgebra.center F L
  let q : L →ₗ⁅F⁆ L ⧸ Z := lieIdealQuotientMap Z
  rw [LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals]
  intro J hJ
  let P : LieIdeal F L := J.comap q
  let f : P →ₗ⁅F⁆ J :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact q.map_add x y
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact q.map_smul c x
      map_lie' := by
        intro x y
        apply Subtype.ext
        exact q.map_lie x y }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' Z (y : L ⧸ Z)
    have hxq : q x = (y : L ⧸ Z) := by
      simpa only [q, lieIdealQuotientMap_apply,
        LieSubmodule.Quotient.mk'_apply] using hx
    have hxJ : q x ∈ J := by
      rw [hxq]
      exact y.property
    refine ⟨⟨x, hxJ⟩, ?_⟩
    apply Subtype.ext
    exact hxq
  have hker : f.ker ≤ LieAlgebra.center F P := by
    intro x hx
    rw [LieHom.mem_ker] at hx
    have hxq : q (x : L) = 0 := by
      have hxval := congrArg Subtype.val hx
      change q (x : L) = ((0 : J) : L ⧸ Z) at hxval
      exact hxval.trans (by rfl)
    have hxZ : (x : L) ∈ Z := by
      rw [← LieSubmodule.Quotient.mk_eq_zero Z]
      simpa only [q, lieIdealQuotientMap_apply,
        LieSubmodule.Quotient.mk'_apply] using hxq
    intro y
    apply Subtype.ext
    exact hxZ y
  have hP : LieAlgebra.IsSolvable P := by
    obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable F J
    refine LieAlgebra.IsSolvable.mk (R := F) (L := P) (k := n + 1) ?_
    rw [LieAlgebra.derivedSeries_def,
      LieAlgebra.derivedSeriesOfIdeal_succ]
    have hdn : LieAlgebra.derivedSeries F P n ≤ f.ker := by
      rw [← LieIdeal.map_eq_bot_iff,
        LieIdeal.derivedSeries_map_eq n hf, hn]
    have hcenter : LieAlgebra.derivedSeries F P n ≤
        LieAlgebra.center F P := hdn.trans hker
    rw [← LieSubmodule.lie_abelian_iff_lie_self_eq_bot]
    exact LieAlgebra.abelian_of_le_center F P
      (LieAlgebra.derivedSeries F P n) hcenter
  have hPZ : P ≤ Z := by
    change P ≤ LieAlgebra.center F L
    rw [← LieAlgebra.radical_eq_center (R := F) (L := L)]
    exact le_sSup hP
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z y
  rw [LieSubmodule.mem_bot, LieSubmodule.Quotient.mk_eq_zero]
  apply hPZ
  change q x ∈ J
  simpa only [q, lieIdealQuotientMap_apply,
    LieSubmodule.Quotient.mk'_apply] using hy

end Abstract

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- The semisimple tangent Lie algebra attached to a reductive algebraic
group: the canonical identity tangent modulo its Lie center. -/
public abbrev IdentityTangentSemisimpleQuotient
    (G : Variety k) [AlgebraicGroup G] :=
  IdentityPointDerivation G ⧸
    LieAlgebra.center k (IdentityPointDerivation G)

/-- The canonical projection from the identity tangent to its semisimple
central quotient. -/
@[expose]
public noncomputable def identityTangentSemisimpleQuotientMap
    (G : Variety k) [AlgebraicGroup G] :
    IdentityPointDerivation G →ₗ⁅k⁆ IdentityTangentSemisimpleQuotient G :=
  lieIdealQuotientMap (LieAlgebra.center k (IdentityPointDerivation G))

omit [IsAlgClosed k] [CharZero k] in
/-- The central tangent quotient projection is surjective. -/
public theorem identityTangentSemisimpleQuotientMap_surjective
    (G : Variety k) [AlgebraicGroup G] :
    Function.Surjective (identityTangentSemisimpleQuotientMap G) := by
  intro y
  obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk'
    (LieAlgebra.center k (IdentityPointDerivation G)) y
  refine ⟨x, ?_⟩
  simpa only [identityTangentSemisimpleQuotientMap,
    lieIdealQuotientMap_apply,
    LieSubmodule.Quotient.mk'_apply] using hx

/-- Reductivity makes the central quotient of the identity tangent
semisimple in the Lie-theoretic sense. -/
public theorem identityTangentSemisimpleQuotient_hasTrivialRadical
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) :
    LieAlgebra.HasTrivialRadical k (IdentityTangentSemisimpleQuotient G) := by
  let _ : LieAlgebra.HasCentralRadical k (IdentityPointDerivation G) :=
    identityTangent_hasCentralRadical_of_reductive hG
  exact hasTrivialRadical_quotient_center

/-- The Killing form on the semisimple tangent quotient is nondegenerate.
This deliberately supplies no Killing instance on the full tangent. -/
public theorem identityTangentSemisimpleQuotient_isKilling
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) :
    LieAlgebra.IsKilling k (IdentityTangentSemisimpleQuotient G) := by
  let _ : LieAlgebra.HasTrivialRadical k
      (IdentityTangentSemisimpleQuotient G) :=
    identityTangentSemisimpleQuotient_hasTrivialRadical hG
  infer_instance

/-- The image of the maximal-torus tangent in the central tangent quotient. -/
@[expose]
public noncomputable def maximalTorusSemisimpleCartan
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    LieSubalgebra k (IdentityTangentSemisimpleQuotient G) :=
  ((identityTangentSemisimpleQuotientMap G).comp
    (maximalTorusCartan T).incl).range

/-- The canonical surjection from the maximal-torus tangent image to its
image in the central tangent quotient. -/
@[expose]
public noncomputable def maximalTorusSemisimpleCartanMap
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    maximalTorusCartan T →ₗ⁅k⁆ maximalTorusSemisimpleCartan T :=
  (((identityTangentSemisimpleQuotientMap G).comp
    (maximalTorusCartan T).incl).rangeRestrict)

omit [IsAlgClosed k] [CharZero k] in
/-- The maximal-torus tangent map onto the quotient Cartan candidate is
surjective by construction. -/
public theorem maximalTorusSemisimpleCartanMap_surjective
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :
    Function.Surjective (maximalTorusSemisimpleCartanMap T) :=
  LieHom.surjective_rangeRestrict _

omit [IsAlgClosed k] [CharZero k] in
/-- The quotient maximal-torus tangent is abelian. -/
public theorem maximalTorusSemisimpleCartan_isLieAbelian
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsMaximalTorus T) :
    IsLieAbelian (maximalTorusSemisimpleCartan T) :=
  (maximalTorusSemisimpleCartanMap_surjective T).isLieAbelian
    (maximalTorusCartan_isLieAbelian T hT)

omit [IsAlgClosed k] [CharZero k] in
/-- The quotient maximal-torus tangent is nilpotent. -/
public theorem maximalTorusSemisimpleCartan_isNilpotent
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsMaximalTorus T) :
    LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) := by
  let _ : IsLieAbelian (maximalTorusSemisimpleCartan T) :=
    maximalTorusSemisimpleCartan_isLieAbelian T hT
  exact LieModule.trivialIsNilpotent _ _

/-- Torus characters that actually occur in the identity tangent
representation.  Restricting to this support is essential: an arbitrary
character need not have differential zero on the central quotient kernel. -/
public abbrev MaximalTorusSupportedIdentityTangentWeight
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :=
  { chi : TorusWeight T //
    weightSpace (identityTangentRepresentation G) T chi ≠ ⊥ }

omit [IsAlgClosed k] [CharZero k] in
/-- A supported tangent weight has differential zero on the kernel of the
maximal-torus tangent map to the central quotient. -/
public theorem maximalTorusCartanCharacterDifferential_ker_le_of_supported
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : MaximalTorusSupportedIdentityTangentWeight T) :
    (maximalTorusSemisimpleCartanMap T).toLinearMap.ker ≤
      (maximalTorusCartanCharacterDifferential T chi.1).ker := by
  intro h hh
  change maximalTorusSemisimpleCartanMap T h = 0 at hh
  change maximalTorusCartanCharacterDifferential T chi.1 h = 0
  have hqzero : identityTangentSemisimpleQuotientMap G
      (h : IdentityPointDerivation G) = 0 := by
    have hhval := congrArg Subtype.val hh
    change identityTangentSemisimpleQuotientMap G
        (h : IdentityPointDerivation G) =
      ((0 : maximalTorusSemisimpleCartan T) :
        IdentityTangentSemisimpleQuotient G) at hhval
    exact hhval.trans (by rfl)
  have hcentral : (h : IdentityPointDerivation G) ∈
      LieAlgebra.center k (IdentityPointDerivation G) := by
    rw [← LieSubmodule.Quotient.mk_eq_zero
      (LieAlgebra.center k (IdentityPointDerivation G))]
    simpa only [identityTangentSemisimpleQuotientMap,
      lieIdealQuotientMap_apply, LieSubmodule.Quotient.mk'_apply] using hqzero
  obtain ⟨v, hv, hvne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot chi.2
  have hscalar :
      maximalTorusCartanCharacterDifferential T chi.1 h = 0 := by
    have hzero :
        maximalTorusCartanCharacterDifferential T chi.1 h • v = 0 := by
      rw [← identityTangentWeightBracketCompatibility_apply
        T hcompat chi.1 v hv h]
      calc
        ⁅(h : IdentityPointDerivation G), v⁆ =
            -⁅v, (h : IdentityPointDerivation G)⁆ := (lie_skew _ _).symm
        _ = 0 := by rw [hcentral v, neg_zero]
    exact (smul_eq_zero.mp hzero).resolve_right hvne
  exact hscalar

/-- The differential of a supported tangent character, descended to the
maximal-torus image in the central quotient. -/
public noncomputable def maximalTorusSemisimpleCartanCharacterDifferential
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : MaximalTorusSupportedIdentityTangentWeight T) :
    maximalTorusSemisimpleCartan T →ₗ[k] k :=
  let m := (maximalTorusSemisimpleCartanMap T).toLinearMap
  let d := maximalTorusCartanCharacterDifferential T chi.1
  ((LinearMap.ker m).liftQ d
      (maximalTorusCartanCharacterDifferential_ker_le_of_supported
        T hcompat chi)).comp
    ((m.quotKerEquivOfSurjective
      (maximalTorusSemisimpleCartanMap_surjective T)).symm.toLinearMap)

omit [IsAlgClosed k] [CharZero k] in
/-- Evaluation of a descended supported character differential on a lifted
maximal-torus tangent. -/
@[simp]
public theorem maximalTorusSemisimpleCartanCharacterDifferential_apply
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : MaximalTorusSupportedIdentityTangentWeight T)
    (h : maximalTorusCartan T) :
    maximalTorusSemisimpleCartanCharacterDifferential T hcompat chi
        (maximalTorusSemisimpleCartanMap T h) =
      maximalTorusCartanCharacterDifferential T chi.1 h := by
  let m := (maximalTorusSemisimpleCartanMap T).toLinearMap
  let d := maximalTorusCartanCharacterDifferential T chi.1
  change ((LinearMap.ker m).liftQ d
      (maximalTorusCartanCharacterDifferential_ker_le_of_supported
        T hcompat chi))
      ((m.quotKerEquivOfSurjective
        (maximalTorusSemisimpleCartanMap_surjective T)).symm (m h)) = d h
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.liftQ_apply]

omit [IsAlgClosed k] [CharZero k] in
/-- Faithful differentiation remains faithful after restricting to supported
weights and descending their differentials to the quotient Cartan. -/
public theorem maximalTorusSemisimpleCartanCharacterDifferential_injective
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hdiff : Function.Injective
      (maximalTorusCartanCharacterDifferential T))
    (hcompat : IdentityTangentWeightBracketCompatibility T) :
    Function.Injective
      (maximalTorusSemisimpleCartanCharacterDifferential T hcompat) := by
  intro chi psi hchi
  apply Subtype.ext
  apply hdiff
  apply LinearMap.ext
  intro h
  rw [← maximalTorusSemisimpleCartanCharacterDifferential_apply
      T hcompat chi h,
    ← maximalTorusSemisimpleCartanCharacterDifferential_apply
      T hcompat psi h]
  exact LinearMap.congr_fun hchi (maximalTorusSemisimpleCartanMap T h)

/-- The image in the central tangent quotient of a supported torus weight
space. -/
@[expose]
public noncomputable def maximalTorusSemisimpleWeightSpace
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (chi : MaximalTorusSupportedIdentityTangentWeight T) :
    Submodule k (IdentityTangentSemisimpleQuotient G) :=
  (weightSpace (identityTangentRepresentation G) T chi.1).map
    (identityTangentSemisimpleQuotientMap G).toLinearMap

omit [IsAlgClosed k] [CharZero k] in
/-- A spanning identity-tangent weight decomposition maps to a spanning
supported-weight decomposition of the central quotient. -/
public theorem maximalTorusSemisimpleWeightSpace_iSup_eq_top
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hspan : (⨆ chi : TorusWeight T,
      weightSpace (identityTangentRepresentation G) T chi) = ⊤) :
    (⨆ chi : MaximalTorusSupportedIdentityTangentWeight T,
      maximalTorusSemisimpleWeightSpace T chi) = ⊤ := by
  change (⨆ chi : {chi : TorusWeight T //
      weightSpace (identityTangentRepresentation G) T chi ≠ ⊥},
    (weightSpace (identityTangentRepresentation G) T chi.1).map
      (identityTangentSemisimpleQuotientMap G).toLinearMap) = ⊤
  rw [← Submodule.map_iSup, iSup_ne_bot_subtype, hspan]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    (identityTangentSemisimpleQuotientMap_surjective G)

omit [IsAlgClosed k] [CharZero k] in
/-- A mapped supported tangent weight lies in the corresponding generalized
root space for the quotient maximal-torus tangent. -/
public theorem maximalTorusSemisimpleWeightSpace_le_rootSpace
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsMaximalTorus T)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : MaximalTorusSupportedIdentityTangentWeight T) :
    let _ : LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) :=
      maximalTorusSemisimpleCartan_isNilpotent T hT
    maximalTorusSemisimpleWeightSpace T chi ≤
      (LieAlgebra.rootSpace (maximalTorusSemisimpleCartan T)
        (maximalTorusSemisimpleCartanCharacterDifferential
          T hcompat chi)).toSubmodule := by
  dsimp only
  let _ : LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) :=
    maximalTorusSemisimpleCartan_isNilpotent T hT
  intro y hy
  apply LieModule.weightSpace_le_genWeightSpace
    (IdentityTangentSemisimpleQuotient G)
    (maximalTorusSemisimpleCartanCharacterDifferential T hcompat chi)
  rw [LieModule.mem_weightSpace]
  intro h
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨h0, rfl⟩ := maximalTorusSemisimpleCartanMap_surjective T h
  change ⁅identityTangentSemisimpleQuotientMap G
      (h0 : IdentityPointDerivation G),
      identityTangentSemisimpleQuotientMap G v⁆ =
    maximalTorusSemisimpleCartanCharacterDifferential T hcompat chi
        (maximalTorusSemisimpleCartanMap T h0) •
      identityTangentSemisimpleQuotientMap G v
  rw [← (identityTangentSemisimpleQuotientMap G).map_lie,
    identityTangentWeightBracketCompatibility_apply T hcompat chi.1 v hv h0,
    map_smul,
    maximalTorusSemisimpleCartanCharacterDifferential_apply]

section AbstractRootSpaceTransport

variable {F : Type*} [Field F]

private theorem submodule_family_eq_rootSpace_of_iSup_eq_top_of_injective
    {L : Type*} [LieRing L] [LieAlgebra F L]
    (H : LieSubalgebra F L) [LieRing.IsNilpotent H]
    {I : Type*} (W : I → Submodule F L) (d : I → H → F)
    (hd : Function.Injective d)
    (hspan : (⨆ i, W i) = ⊤)
    (hle : ∀ i, W i ≤
      (LieAlgebra.rootSpace H (d i)).toSubmodule) :
    ∀ i, W i = (LieAlgebra.rootSpace H (d i)).toSubmodule := by
  have hindepLie : iSupIndep (fun i => LieAlgebra.rootSpace H (d i)) :=
    (LieModule.iSupIndep_genWeightSpace F H L).comp hd
  have hindep : iSupIndep
      (fun i => (LieAlgebra.rootSpace H (d i)).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr hindepLie
  have hfamily : W = fun i =>
      (LieAlgebra.rootSpace H (d i)).toSubmodule :=
    (hindep.le_iff_eq_of_iSup_eq_top hspan).mp hle
  exact congrFun hfamily

end AbstractRootSpaceTransport

omit [IsAlgClosed k] [CharZero k] in
/-- Under the same faithful-differentiation, spanning, and differentiated
bracket hypotheses as the full-tangent comparison, each mapped supported
weight is exactly the corresponding quotient Lie root space. -/
public theorem maximalTorusSemisimpleWeightSpace_eq_rootSpace
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsMaximalTorus T)
    (hdiff : Function.Injective
      (maximalTorusCartanCharacterDifferential T))
    (hspan : (⨆ psi : TorusWeight T,
      weightSpace (identityTangentRepresentation G) T psi) = ⊤)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : MaximalTorusSupportedIdentityTangentWeight T) :
    let _ : LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) :=
      maximalTorusSemisimpleCartan_isNilpotent T hT
    maximalTorusSemisimpleWeightSpace T chi =
      (LieAlgebra.rootSpace (maximalTorusSemisimpleCartan T)
        (maximalTorusSemisimpleCartanCharacterDifferential
          T hcompat chi)).toSubmodule := by
  dsimp only
  let _ : LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) :=
    maximalTorusSemisimpleCartan_isNilpotent T hT
  exact submodule_family_eq_rootSpace_of_iSup_eq_top_of_injective
    (maximalTorusSemisimpleCartan T)
    (maximalTorusSemisimpleWeightSpace T)
    (fun psi h =>
      maximalTorusSemisimpleCartanCharacterDifferential
        T hcompat psi h)
    (by
      intro psi phi heq
      apply maximalTorusSemisimpleCartanCharacterDifferential_injective
        T hdiff hcompat
      apply LinearMap.ext
      intro h
      exact congrFun heq h)
    (maximalTorusSemisimpleWeightSpace_iSup_eq_top T hspan)
    (maximalTorusSemisimpleWeightSpace_le_rootSpace T hT hcompat) chi

/-- The mapped supported tangent weight is linearly equivalent to its
quotient Lie root space. -/
public noncomputable def maximalTorusSemisimpleWeightSpaceRootSpaceEquiv
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsMaximalTorus T)
    (hdiff : Function.Injective
      (maximalTorusCartanCharacterDifferential T))
    (hspan : (⨆ psi : TorusWeight T,
      weightSpace (identityTangentRepresentation G) T psi) = ⊤)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (chi : MaximalTorusSupportedIdentityTangentWeight T) :
    let _ : LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) :=
      maximalTorusSemisimpleCartan_isNilpotent T hT
    maximalTorusSemisimpleWeightSpace T chi ≃ₗ[k]
      LieAlgebra.rootSpace (maximalTorusSemisimpleCartan T)
        (maximalTorusSemisimpleCartanCharacterDifferential
          T hcompat chi) := by
  let _ : LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) :=
    maximalTorusSemisimpleCartan_isNilpotent T hT
  exact LinearEquiv.ofEq _ _
    (maximalTorusSemisimpleWeightSpace_eq_rootSpace
      T hT hdiff hspan hcompat chi)

/-- The exact remaining zero-weight input for the quotient Cartan statement:
the trivial tangent weight occurs and its image in the central quotient is
precisely the quotient maximal-torus tangent. -/
public def MaximalTorusSemisimpleZeroWeightExhaustion
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) : Prop :=
  ∃ hone : weightSpace (identityTangentRepresentation G) T 1 ≠ ⊥,
    maximalTorusSemisimpleWeightSpace T ⟨1, hone⟩ =
      (maximalTorusSemisimpleCartan T).toSubmodule

omit [IsAlgClosed k] [CharZero k] in
/-- The descended differential of the supported trivial character is zero. -/
public theorem maximalTorusSemisimpleCartanCharacterDifferential_one
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (hone : weightSpace (identityTangentRepresentation G) T 1 ≠ ⊥) :
    maximalTorusSemisimpleCartanCharacterDifferential
      T hcompat ⟨1, hone⟩ = 0 := by
  apply LinearMap.ext
  intro h
  obtain ⟨h0, rfl⟩ := maximalTorusSemisimpleCartanMap_surjective T h
  change maximalTorusSemisimpleCartanCharacterDifferential
      T hcompat ⟨1, hone⟩ (maximalTorusSemisimpleCartanMap T h0) = 0
  rw [maximalTorusSemisimpleCartanCharacterDifferential_apply,
    LinearMap.congr_fun (maximalTorusCartanCharacterDifferential_one T)]
  exact LinearMap.zero_apply _

omit [IsAlgClosed k] [CharZero k] in
/-- With zero-weight exhaustion, the quotient maximal-torus tangent is a
Mathlib Cartan subalgebra.  The exhaustion is kept explicit because proving it
geometrically requires the separate maximal-torus centralizer theorem. -/
public theorem maximalTorusSemisimpleCartan_isCartanSubalgebra
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsMaximalTorus T)
    (hdiff : Function.Injective
      (maximalTorusCartanCharacterDifferential T))
    (hspan : (⨆ psi : TorusWeight T,
      weightSpace (identityTangentRepresentation G) T psi) = ⊤)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (hzero : MaximalTorusSemisimpleZeroWeightExhaustion T) :
    (maximalTorusSemisimpleCartan T).IsCartanSubalgebra := by
  let _ : LieRing.IsNilpotent (maximalTorusSemisimpleCartan T) :=
    maximalTorusSemisimpleCartan_isNilpotent T hT
  obtain ⟨hone, hzero⟩ := hzero
  have hweight := maximalTorusSemisimpleWeightSpace_eq_rootSpace
    T hT hdiff hspan hcompat ⟨1, hone⟩
  have hdiffzero :=
    maximalTorusSemisimpleCartanCharacterDifferential_one
      T hcompat hone
  have hdiffzero_fun :
      (maximalTorusSemisimpleCartanCharacterDifferential
        T hcompat ⟨1, hone⟩ : maximalTorusSemisimpleCartan T → k) = 0 := by
    funext h
    rw [LinearMap.congr_fun hdiffzero h]
    exact LinearMap.zero_apply h
  rw [hdiffzero_fun] at hweight
  apply (LieAlgebra.eq_rootSpace_zero_iff_isCartan
    (R := k) (L := IdentityTangentSemisimpleQuotient G)
    (H := maximalTorusSemisimpleCartan T)).mp
  rw [← LieSubmodule.toSubmodule_inj]
  change (maximalTorusSemisimpleCartan T).toSubmodule =
    (LieAlgebra.rootSpace (maximalTorusSemisimpleCartan T) 0).toSubmodule
  exact hzero.symm.trans hweight

/-- A nontrivial supported quotient weight with nonzero image has a
one-dimensional root space.  This is the direct Killing-theoretic consumer of
the semisimple central quotient and the transported Cartan API. -/
public theorem finrank_maximalTorusSemisimple_rootSpace_eq_one
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdiff : Function.Injective
      (maximalTorusCartanCharacterDifferential T))
    (hspan : (⨆ psi : TorusWeight T,
      weightSpace (identityTangentRepresentation G) T psi) = ⊤)
    (hcompat : IdentityTangentWeightBracketCompatibility T)
    (hzero : MaximalTorusSemisimpleZeroWeightExhaustion T)
    (chi : MaximalTorusSupportedIdentityTangentWeight T)
    (hchi : chi.1 ≠ 1)
    (hquot : maximalTorusSemisimpleWeightSpace T chi ≠ ⊥) :
    let _ : (maximalTorusSemisimpleCartan T).IsCartanSubalgebra :=
      maximalTorusSemisimpleCartan_isCartanSubalgebra
        T hT hdiff hspan hcompat hzero
    Module.finrank k (LieAlgebra.rootSpace
      (maximalTorusSemisimpleCartan T)
      (maximalTorusSemisimpleCartanCharacterDifferential
        T hcompat chi)) = 1 := by
  dsimp only
  let _ : LieAlgebra.HasTrivialRadical k
      (IdentityTangentSemisimpleQuotient G) :=
    identityTangentSemisimpleQuotient_hasTrivialRadical hG
  let _ : LieAlgebra.IsKilling k
      (IdentityTangentSemisimpleQuotient G) :=
    identityTangentSemisimpleQuotient_isKilling hG
  let _ : (maximalTorusSemisimpleCartan T).IsCartanSubalgebra :=
    maximalTorusSemisimpleCartan_isCartanSubalgebra
      T hT hdiff hspan hcompat hzero
  obtain ⟨hone, _⟩ := hzero
  have hroot := maximalTorusSemisimpleWeightSpace_eq_rootSpace
    T hT hdiff hspan hcompat chi
  have hrootne : LieAlgebra.rootSpace
      (maximalTorusSemisimpleCartan T)
      (maximalTorusSemisimpleCartanCharacterDifferential
        T hcompat chi) ≠ ⊥ := by
    intro hz
    apply hquot
    calc
      maximalTorusSemisimpleWeightSpace T chi =
          (LieAlgebra.rootSpace (maximalTorusSemisimpleCartan T)
            (maximalTorusSemisimpleCartanCharacterDifferential
              T hcompat chi)).toSubmodule := hroot
      _ = ⊥ := by rw [hz]; rfl
  let alpha : LieModule.Weight k (maximalTorusSemisimpleCartan T)
      (IdentityTangentSemisimpleQuotient G) :=
    ⟨maximalTorusSemisimpleCartanCharacterDifferential T hcompat chi,
      hrootne⟩
  have halpha : alpha.IsNonZero := by
    intro halphaZero
    have hdlin :
        maximalTorusSemisimpleCartanCharacterDifferential T hcompat chi = 0 := by
      apply LinearMap.ext
      intro h
      exact congrFun halphaZero h
    have hdone := maximalTorusSemisimpleCartanCharacterDifferential_one
      T hcompat hone
    have hchiOne : chi = ⟨1, hone⟩ :=
      maximalTorusSemisimpleCartanCharacterDifferential_injective
        T hdiff hcompat (hdlin.trans hdone.symm)
    exact hchi (congrArg Subtype.val hchiOne)
  exact LieAlgebra.IsKilling.finrank_rootSpace_eq_one alpha halpha

end Theory.AlgebraicGroup
