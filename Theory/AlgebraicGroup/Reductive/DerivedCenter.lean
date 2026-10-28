module

public import Theory.AlgebraicGroup.Borel.SemisimpleCenter
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.Reductive.Basic
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight
public import Theory.AlgebraicGroup.RightTranslation.SemisimpleCoordinate
public import Theory.AlgebraicGroup.Solvable.Basic
public import Theory.AlgebraicGroup.Tori.Character.Basis
public import Theory.AlgebraicGroup.Tori.Character.FiniteGeneration

/-!
# The derived subgroup of a reductive group

Over an algebraically closed field, the Zariski closure of the abstract derived
subgroup of a reductive algebraic group is semisimple.  Consequently its center
is finite, as is the center of the abstract derived subgroup.

The proof follows the reductive decomposition discussion in GLS, *The
Classification of the Finite Simple Groups*, Part I, Chapter 2, Section 6.5.
A radical of the closed derived subgroup has normal ambient image and therefore
lies in the connected center of the reductive group.  This image is a central
torus.  The faithful coordinate-translation representation rules out a
nontrivial central torus inside the closed derived subgroup: determinant
characters of its nonzero weight spaces vanish on the derived closure, so the
torsion-free character group forces every weight to be trivial.

The final comparison identifies the intrinsic center of the closed derived
subgroup with its ambient intersection with its centralizer.  The corresponding
intersection for the abstract derived subgroup is a subset, because an element
centralizing a subgroup centralizes its Zariski closure.
-/

universe u

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem representation_determinantCharacter_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho) :
    exists chi : TorusCharacter K, forall g,
      chi.pointCharacter g = LinearMap.det (rho.action g : Module.End k V) := by
  classical
  obtain ⟨e, f, hf⟩ := hrho
  let M : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V))
      K.PolynomialFunction := fun i j =>
    rationalRepresentationMatrixCoefficient rho e f i j
  let scalar : K.PolynomialFunction := Matrix.det M
  have scalar_apply (g : Variety.Point K) :
      scalar g = LinearMap.det (rho.action g : Module.End k V) := by
    let ev : K.PolynomialFunction →+* k := {
      toFun := fun q => q g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    change ev (Matrix.det M) = _
    rw [RingHom.map_det, ← LinearMap.det_toMatrix e]
    congr 1
    funext i j
    change (M i j).toFun g = (LinearMap.toMatrix e e
      (rho.action g : Module.End k V)) i j
    dsimp only [M]
    rw [LinearMap.toMatrix_apply]
    exact rationalRepresentationMatrixCoefficient_apply rho e f hf i j g
  let determinantHom : LinearMap.GeneralLinearGroup k V →* kˣ :=
    LinearEquiv.det.comp
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom
  let scalarUnit (g : Variety.Point K) : kˣ := determinantHom (rho.action g)
  have scalarUnit_val (g : Variety.Point K) :
      (scalarUnit g : k) = scalar g := by
    rw [scalar_apply]
    dsimp only [scalarUnit, determinantHom, MonoidHom.comp_apply]
    rw [LinearEquiv.coe_det]
    exact congrArg LinearMap.det
      (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap
        (rho.action g))
  have scalarInv_apply (g : Variety.Point K) :
      (scalarUnit g).inv = scalar g⁻¹ := by
    rw [← scalarUnit_val]
    exact congrArg Units.val
      (map_inv (determinantHom.comp rho.action) g).symm
  let pointMap (g : Variety.Point K) : Variety.Point (KMult k) :=
    (dPointEquiv 1).symm (fun _ => scalarUnit g)
  let scalarInv : K.PolynomialFunction :=
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism K) scalar
  let chi : TorusCharacter K := {
    toVariety := {
      toFun := pointMap
      regular := by
        intro c
        cases c with
        | inl i =>
            rcases i with ⟨i⟩
            fin_cases i
            rcases scalar.representedBy with ⟨p, hp⟩
            exact ⟨p, fun g => by
              change (scalarUnit g : k) = evalPolynomial g.val p
              rw [scalarUnit_val, hp]⟩
        | inr i =>
            rcases i with ⟨i⟩
            fin_cases i
            rcases scalarInv.representedBy with ⟨p, hp⟩
            exact ⟨p, fun g => by
              change (scalarUnit g).inv = evalPolynomial g.val p
              rw [← hp]
              exact scalarInv_apply g⟩ }
    map_one := by
      apply (dPointEquiv 1).injective
      funext i
      fin_cases i
      change scalarUnit 1 = 1
      simp [scalarUnit]
    map_mul := by
      intro g h
      apply (dPointEquiv 1).injective
      funext i
      fin_cases i
      change scalarUnit (g * h) = scalarUnit g * scalarUnit h
      exact map_mul (determinantHom.comp rho.action) g h }
  refine ⟨chi, fun g => ?_⟩
  change (scalarUnit g : k) = _
  exact (scalarUnit_val g).trans (scalar_apply g)

private theorem coordinate_weightSpace_iSup_eq_top
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsSubtorus T) :
    (iSup fun chi : TorusWeight T =>
      weightSpace (coordinateTranslationRationalRepresentation K) T chi) =
        (⊤ : Submodule k (coordinateTranslationSubmodule K)) := by
  let rho := coordinateTranslationRationalRepresentation K
  let V := coordinateTranslationSubmodule K
  letI : Module.Finite k V := coordinateTranslationSubmodule_finite K
  have hcomm (s t : Variety.Point T.carrierVariety) :
      Commute (rho.action (T.includePoint s) : Module.End k V)
        (rho.action (T.includePoint t) : Module.End k V) := by
    have hst : T.includePoint s * T.includePoint t =
        T.includePoint t * T.includePoint s := by
      have hTcomm := hT.isMulCommutative
      rw [isMulCommutative_iff] at hTcomm
      calc
        T.includePoint s * T.includePoint t = T.includePoint (s * t) :=
          (T.inclusion.map_mul s t).symm
        _ = T.includePoint (t * s) := congrArg T.includePoint (hTcomm s t)
        _ = T.includePoint t * T.includePoint s := T.inclusion.map_mul t s
    have hu : rho.action (T.includePoint s) * rho.action (T.includePoint t) =
        rho.action (T.includePoint t) * rho.action (T.includePoint s) := by
      simpa only [map_mul] using congrArg rho.action hst
    change ((rho.action (T.includePoint s) * rho.action (T.includePoint t) :
          LinearMap.GeneralLinearGroup k V) : Module.End k V) =
      ((rho.action (T.includePoint t) * rho.action (T.includePoint s) :
          LinearMap.GeneralLinearGroup k V) : Module.End k V)
    exact congrArg (fun a : LinearMap.GeneralLinearGroup k V =>
      (a : Module.End k V)) hu
  have hsemi (t : Variety.Point T.carrierVariety) :
      Module.End.IsSemisimple
        (rho.action (T.includePoint t) : Module.End k V) := by
    change (rightTranslationOnCoordinateSubmodule K (T.includePoint t)).IsSemisimple
    apply rightTranslationOnCoordinateSubmodule_isSemisimple
    exact morphism_preserves_semisimpleElement T.inclusion t (hT.all_semisimple t)
  have heigen := commutingSemisimple_iSup_eigenspace_eq_top
    (fun t : Variety.Point T.carrierVariety =>
      (rho.action (T.includePoint t) : Module.End k V)) hcomm hsemi
  apply le_antisymm le_top
  rw [← heigen]
  apply iSup_le
  intro mu v hv
  by_cases hvzero : v = 0
  · subst v
    exact Submodule.zero_mem _
  have hline : GeneratesInvariantLine rho T v := by
    refine ⟨hvzero, ?_⟩
    intro h hh
    let t : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨h, hh⟩
    refine ⟨mu t, ?_⟩
    have hvt : v ∈ Module.End.eigenspace
        (rho.action (T.includePoint t) : Module.End k V) (mu t) :=
      (iInf_le (fun s : Variety.Point T.carrierVariety =>
        Module.End.eigenspace
          (rho.action (T.includePoint s) : Module.End k V) (mu s)) t) hv
    have ht : T.includePoint t = h := by
      change (T.pointEquiv t).val = h
      simp [t]
    rw [← ht]
    exact Module.End.mem_eigenspace_iff.mp hvt
  obtain ⟨chi, hchi, _⟩ :=
    invariantLine_torusWeight_existsUnique_public rho
      (coordinateTranslationRationalRepresentation_isRational K) T v hline
  exact (le_iSup (fun psi : TorusWeight T => weightSpace rho T psi) chi) hchi.2

omit [IsAlgClosed k] in
private theorem character_eq_one_on_derivedClosure
    {K : Variety k} [AlgebraicGroup K] (chi : TorusCharacter K)
    {x : Variety.Point K}
    (hx : x ∈ (subgroupZariskiClosure K
      (_root_.commutator (Variety.Point K))).toSubgroup) :
    chi.onPoints x = 1 := by
  have hcomm : _root_.commutator (Variety.Point K) ≤ chi.kernel := by
    letI : IsMulCommutative (Variety.Point (KMult k)) :=
      dVariety_isMulCommutative (k := k) 1
    have hmapbot : (_root_.commutator (Variety.Point K)).map chi.onPoints = ⊥ := by
      rw [map_commutator_eq]
      apply le_antisymm
      · rw [Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' a b)
      · exact bot_le
    intro z hz
    change chi.onPoints z = 1
    have hzmap : chi.onPoints z ∈
        (_root_.commutator (Variety.Point K)).map chi.onPoints :=
      ⟨z, hz, rfl⟩
    rw [hmapbot, Subgroup.mem_bot] at hzmap
    exact hzmap
  change x ∈ closure
      (_root_.commutator (Variety.Point K) : Set (Variety.Point K)) at hx
  have hxker : x ∈ (chi.kernel : Set (Variety.Point K)) :=
    closure_minimal hcomm
      (Variety.isClosed_iff_isZariskiClosed.mpr chi.kernel_isZariskiClosed) hx
  exact hxker

private theorem central_subtorus_eq_bot_of_le_derivedClosure
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsSubtorus T)
    (hTcentral : T.toSubgroup ≤ Subgroup.center (Variety.Point K))
    (hTderived : T ≤ subgroupZariskiClosure K
      (_root_.commutator (Variety.Point K))) :
    T.toSubgroup = (⊥ : Subgroup (Variety.Point K)) := by
  let rho := coordinateTranslationRationalRepresentation K
  let V := coordinateTranslationSubmodule K
  letI : Module.Finite k V := coordinateTranslationSubmodule_finite K
  letI : Module.IsTorsionFree k V :=
    Module.IsTorsionFree.of_smul_eq_zero fun c v hcv => by
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        calc
          v = (c⁻¹ * c) • v := by rw [inv_mul_cancel₀ hc, one_smul]
          _ = c⁻¹ • (c • v) := by rw [mul_smul]
          _ = 0 := by rw [hcv, smul_zero]
  have hdecomp : (iSup fun chi : TorusWeight T => weightSpace rho T chi) = ⊤ :=
    coordinate_weightSpace_iSup_eq_top T hT
  have hweight (chi : TorusWeight T)
      (hchi : weightSpace rho T chi ≠ ⊥) : chi = 1 := by
    let W := weightSpace rho T chi
    letI : Module.Free k W := Module.Free.of_divisionRing k W
    have hWinvariant : IsInvariantSubmodule rho W := by
      intro g v hv t
      have htcenter : T.includePoint t ∈ Subgroup.center (Variety.Point K) :=
        hTcentral (T.pointEquiv t).property
      have htcomm : T.includePoint t * g = g * T.includePoint t :=
        (Subgroup.mem_center_iff.mp htcenter g).symm
      change (rho.action (T.includePoint t) : Module.End k V)
          ((rho.action g : Module.End k V) v) =
        chi.pointCharacter t • (rho.action g : Module.End k V) v
      calc
        (rho.action (T.includePoint t) : Module.End k V)
            ((rho.action g : Module.End k V) v) =
            (rho.action (T.includePoint t * g) : Module.End k V) v := by
              rw [map_mul]
              rfl
        _ = (rho.action (g * T.includePoint t) : Module.End k V) v := by
              rw [htcomm]
        _ = (rho.action g : Module.End k V)
            ((rho.action (T.includePoint t) : Module.End k V) v) := by
              rw [map_mul]
              rfl
        _ = chi.pointCharacter t • (rho.action g : Module.End k V) v := by
              rw [hv t, map_smul]
    obtain ⟨sigma, hsigma, hsigmaRational⟩ :=
      rationalRepresentation_restriction_exists rho
        (coordinateTranslationRationalRepresentation_isRational K)
        W hWinvariant
    obtain ⟨delta, hdelta⟩ :=
      representation_determinantCharacter_exists sigma hsigmaRational
    let n := Module.finrank k W
    have hn : n ≠ 0 := by
      exact Nat.ne_of_gt (Submodule.one_le_finrank_iff.mpr hchi)
    have hdeltaScalar (t : Variety.Point T.carrierVariety) :
        (chi.pointCharacter t) ^ n = 1 := by
      have hdeltaOne : delta.onPoints (T.includePoint t) = 1 :=
        character_eq_one_on_derivedClosure delta
          (hTderived (T.pointEquiv t).property)
      have hdeltaScalar : delta.pointCharacter (T.includePoint t) = 1 := by
        change (dPointEquiv 1 (delta.onPoints (T.includePoint t)) 0 : k) = 1
        rw [hdeltaOne, dPointEquiv_one]
        rfl
      rw [hdelta, show (sigma.action (T.includePoint t) : Module.End k W) =
          chi.pointCharacter t • LinearMap.id by
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        exact (hsigma (T.includePoint t) w).trans (w.2 t),
        LinearMap.det_smul, LinearMap.det_id, mul_one] at hdeltaScalar
      exact hdeltaScalar
    have hpower : chi ^ n = 1 := by
      apply (torusCharacter_scalarPolynomialFunction_linearIndependent
        T.carrierVariety).injective
      change (TorusCharacter.scalarPolynomialFunctionMonoidHom
          T.carrierVariety) (chi ^ n) =
        (TorusCharacter.scalarPolynomialFunctionMonoidHom
          T.carrierVariety) 1
      rw [map_pow, map_one]
      apply Variety.PolynomialFunction.ext
      intro t
      change (chi.scalarPolynomialFunction t) ^ n = 1
      rw [TorusCharacter.scalarPolynomialFunction_apply]
      exact hdeltaScalar t
    letI : IsMulTorsionFree (TorusCharacter T.carrierVariety) :=
      torusCharacter_isTorsionFree_of_isConnected
        T.carrierVariety hT.isConnected
    apply IsMulTorsionFree.pow_left_injective hn
    simpa using hpower
  have hactsOne (t : Variety.Point T.carrierVariety) :
      rho.action (T.includePoint t) = 1 := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ iSup fun chi : TorusWeight T => weightSpace rho T chi := by
      rw [hdecomp]
      exact Submodule.mem_top
    apply (Submodule.mem_iSup_iff_exists_finsupp
      (fun chi : TorusWeight T => weightSpace rho T chi) v).mp at hv
    obtain ⟨components, hcomponents, hsum⟩ := hv
    change (rho.action (T.includePoint t) : Module.End k V) v = v
    rw [← hsum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro chi hchiSupport
    by_cases hspace : weightSpace rho T chi = ⊥
    · have hzero : components chi = 0 := by
        have := hcomponents chi
        rw [hspace] at this
        exact this
      simp [hzero]
    · have hchiOne := hweight chi hspace
      subst chi
      have hcomponent := hcomponents 1 t
      have hone : (1 : TorusCharacter T.carrierVariety).pointCharacter t = 1 := by
        change (dPointEquiv 1 ((1 : TorusCharacter T.carrierVariety).onPoints t) 0 : k) = 1
        rfl
      rw [hone, one_smul] at hcomponent
      simpa using hcomponent
  apply le_antisymm
  · intro x hx
    let t : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hx⟩
    have htOne : T.includePoint t = 1 := by
      apply coordinateTranslationRepresentation_injective K
      change rho.action (T.includePoint t) = rho.action 1
      rw [hactsOne, map_one]
    change x = 1
    have htval : T.includePoint t = x := by
      change (T.pointEquiv t).val = x
      simp [t]
    exact htval.symm.trans htOne
  · exact bot_le

omit [IsAlgClosed k] in
private theorem closedSubgroup_carrier_isConnected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  letI : ConnectedSpace
      {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  letI : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem IsRadicalSubgroup.imageClosedSubgroup_le_of_surjective_clean
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hf : Function.Surjective f.onPoints)
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    {S : ClosedSubgroup H} (hS : IsRadicalSubgroup S) :
    (f.comp R.inclusion).imageClosedSubgroup ≤ S := by
  let q := f.comp R.inclusion
  let Q := q.imageClosedSubgroup
  have hQmap : Q.toSubgroup = R.toSubgroup.map f.onPoints := by
    ext y
    constructor
    · intro hy
      change y ∈ q.image at hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨R.inclusion.onPoints x, (R.pointEquiv x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      change f.onPoints x ∈ q.image
      let xR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨x, hx⟩
      refine ⟨xR, ?_⟩
      change f.onPoints (R.inclusion.onPoints xR) = f.onPoints x
      apply congrArg f.onPoints
      change (R.pointEquiv xR).val = x
      simp [xR]
  have hQnormal : Q.toSubgroup.Normal := by
    rw [hQmap]
    exact Subgroup.Normal.map hR.normal f.onPoints hf
  have hRconnected := closedSubgroup_carrier_isConnected R hR.connected
  have hQconnected := q.imageClosedSubgroup_isConnected hRconnected
  have hQsolvable := q.imageClosedSubgroup_isSolvable hR.solvable
  exact hS.maximal Q hQnormal hQconnected hQsolvable

/-- The Zariski closure of the abstract derived subgroup of a reductive
algebraic group is semisimple. -/
public theorem reductive_derivedClosure_isSemisimple
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsReductiveAlgebraicGroup K) :
    IsSemisimpleAlgebraicGroup
      (subgroupZariskiClosure K
        (_root_.commutator (Variety.Point K))).carrierVariety := by
  let D := subgroupZariskiClosure K
    (_root_.commutator (Variety.Point K))
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  have hDnormal : D.toSubgroup.Normal :=
    subgroupZariskiClosure_isNormal K _
      (derivedSeries_normal (Variety.Point K) 1)
  refine ⟨?_, ?_⟩
  · exact closedSubgroup_carrier_isConnected D
      (subgroupZariskiClosure_commutator_isConnected hK.1)
  · intro R hR
    letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
    let q : AlgebraicGroup.Morphism R.carrierVariety K :=
      D.inclusion.comp R.inclusion
    let S := q.imageClosedSubgroup
    have hSnormal : S.toSubgroup.Normal := by
      constructor
      intro x hx g
      change x ∈ q.image at hx
      rcases hx with ⟨r, rfl⟩
      let c := D.conjugationRestriction hDnormal g
      have hcsurjective : Function.Surjective c.onPoints := by
        intro y
        refine ⟨(D.conjugationRestriction hDnormal g⁻¹).onPoints y, ?_⟩
        apply D.inclusion_injective
        rw [D.conjugationRestriction_inclusion_apply,
          D.conjugationRestriction_inclusion_apply]
        group
      have hcRle : (c.comp R.inclusion).imageClosedSubgroup ≤ R :=
        hR.imageClosedSubgroup_le_of_surjective_clean c hcsurjective hR
      have hcr : c.onPoints (R.inclusion.onPoints r) ∈ R.toSubgroup := by
        apply hcRle
        change c.onPoints (R.inclusion.onPoints r) ∈
          (c.comp R.inclusion).image
        exact ⟨r, rfl⟩
      let r' : Variety.Point R.carrierVariety :=
        R.pointEquiv.symm ⟨c.onPoints (R.inclusion.onPoints r), hcr⟩
      change g * q.onPoints r * g⁻¹ ∈ q.image
      refine ⟨r', ?_⟩
      change D.inclusion.onPoints (R.inclusion.onPoints r') =
        g * D.inclusion.onPoints (R.inclusion.onPoints r) * g⁻¹
      rw [show R.inclusion.onPoints r' =
          c.onPoints (R.inclusion.onPoints r) by
        change (R.pointEquiv r').val = _
        simp [r']]
      exact D.conjugationRestriction_inclusion_apply hDnormal g _
    have hRconnected := closedSubgroup_carrier_isConnected R hR.connected
    have hSconnected := q.imageClosedSubgroup_isConnected hRconnected
    have hSsolvable := q.imageClosedSubgroup_isSolvable hR.solvable
    obtain ⟨A, hA⟩ := exists_radical K
    have hSA : S ≤ A := hA.maximal S hSnormal hSconnected hSsolvable
    let Z : ClosedSubgroup K := (ClosedSubgroup.top (G := K)).centralizer
    let Z0 : ClosedSubgroup K := Z.identityComponentAmbient
    have hAeq : A = Z0 :=
      radical_eq_center_identityComponent_of_reductive hK A hA
    have hSZ0 : S ≤ Z0 := by
      rw [← hAeq]
      exact hSA
    have hZcarrier : (Z.toSubgroup : Set (Variety.Point K)) =
        Subgroup.center (Variety.Point K) := by
      ext x
      change x ∈ Subgroup.centralizer
          (Set.univ : Set (Variety.Point K)) ↔
        x ∈ Subgroup.center (Variety.Point K)
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
      simp only [Set.mem_univ, forall_const]
    have hScentral : S.toSubgroup ≤
        Subgroup.center (Variety.Point K) := by
      intro x hx
      change x ∈ (Subgroup.center (Variety.Point K) : Set (Variety.Point K))
      rw [← hZcarrier]
      exact Z.identityComponentAmbient_le (hSZ0 hx)
    have hScomm : IsMulCommutative (Variety.Point S.carrierVariety) := by
      apply IsMulCommutative.of_comm
      intro x y
      apply S.inclusion_injective
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp
        (hScentral (S.pointEquiv x).property) (S.includePoint y)).symm
    have hZ0torus : IsSubtorus Z0 :=
      center_identityComponent_isSubtorus_of_reductive hK
    have hSsemi (s : Variety.Point S.carrierVariety) :
        IsSemisimpleElement S.carrierVariety s := by
      let z : Variety.Point Z0.carrierVariety :=
        Z0.pointEquiv.symm ⟨S.includePoint s, hSZ0 (S.pointEquiv s).property⟩
      have hzsemi := morphism_preserves_semisimpleElement Z0.inclusion z
        (hZ0torus.all_semisimple z)
      have hzinc : Z0.inclusion.onPoints z = S.includePoint s := by
        change (Z0.pointEquiv z).val = S.includePoint s
        simp [z]
      rw [hzinc] at hzsemi
      have hs := (closedSubgroup_semisimpleElement_iff S
        (S.pointEquiv s).property).mp hzsemi
      simpa using hs
    have hStorus : IsSubtorus S :=
      isTorus_of_isConnected_isMulCommutative_all_semisimple
        (closedSubgroup_carrier_isConnected S hSconnected) hScomm hSsemi
    have hSD : S ≤ D := by
      intro x hx
      change x ∈ q.image at hx
      rcases hx with ⟨r, rfl⟩
      exact (D.pointEquiv (R.inclusion.onPoints r)).property
    have hSbot : S.toSubgroup =
        (⊥ : Subgroup (Variety.Point K)) :=
      central_subtorus_eq_bot_of_le_derivedClosure S hStorus hScentral hSD
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      let r : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨x, hx⟩
      have hqmem : q.onPoints r ∈ S.toSubgroup := by
        change q.onPoints r ∈ q.image
        exact ⟨r, rfl⟩
      rw [hSbot, Subgroup.mem_bot] at hqmem
      have hrone : R.inclusion.onPoints r = 1 := by
        apply D.inclusion_injective
        change q.onPoints r = D.inclusion.onPoints 1
        rw [hqmem, map_one]
      calc
        x = R.inclusion.onPoints r := by
          symm
          change (R.pointEquiv r).val = x
          simp [r]
        _ = 1 := hrone
    · exact bot_le

omit [IsAlgClosed k] in
private theorem centralizer_le_centralizer_subgroupZariskiClosure
    {K : Variety k} [AlgebraicGroup K]
    (H : Subgroup (Variety.Point K)) :
    Subgroup.centralizer (H : Set (Variety.Point K)) ≤
      Subgroup.centralizer
        ((subgroupZariskiClosure K H).toSubgroup : Set (Variety.Point K)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  change y ∈ closure (H : Set (Variety.Point K)) at hy
  let C : Set (Variety.Point K) := {z | z * x = x * z}
  have hCclosed : IsClosed C := by
    apply Variety.isClosed_iff_isZariskiClosed.mpr
    simpa [C, AlgebraicGroup.leftMulMorphism_apply,
      AlgebraicGroup.rightMulMorphism_apply] using
      Variety.Morphism.isZariskiClosed_equalizer
        (AlgebraicGroup.rightMulMorphism K x)
        (AlgebraicGroup.leftMulMorphism K x)
  exact closure_minimal (fun z hz => hx z hz) hCclosed hy

omit [IsAlgClosed k] in
/-- The intrinsic center of a closed derived subgroup maps to its intersection
with its ambient centralizer. -/
public theorem derivedClosure_center_image_eq_ambient_intersection
    {K : Variety k} [AlgebraicGroup K] :
    let D := subgroupZariskiClosure K
      (_root_.commutator (Variety.Point K))
    D.inclusion.onPoints ''
        (Subgroup.center (Variety.Point D.carrierVariety) :
          Set (Variety.Point D.carrierVariety)) =
      (((D.toSubgroup ⊓ Subgroup.centralizer
          (D.toSubgroup : Set (Variety.Point K))) :
          Subgroup (Variety.Point K)) : Set (Variety.Point K)) := by
  let D := subgroupZariskiClosure K
    (_root_.commutator (Variety.Point K))
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    constructor
    · exact (D.pointEquiv d).property
    · change D.includePoint d ∈ Subgroup.centralizer
          (D.toSubgroup : Set (Variety.Point K))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yD : Variety.Point D.carrierVariety := D.pointEquiv.symm ⟨y, hy⟩
      have hdy := Subgroup.mem_center_iff.mp hd yD
      have hyinc : D.includePoint yD = y := by
        change (D.pointEquiv yD).val = y
        simp [yD]
      calc
        y * D.includePoint d = D.includePoint yD * D.includePoint d := by
          rw [hyinc]
        _ = D.includePoint (yD * d) := (D.inclusion.map_mul yD d).symm
        _ = D.includePoint (d * yD) := congrArg D.includePoint hdy
        _ = D.includePoint d * D.includePoint yD := D.inclusion.map_mul d yD
        _ = D.includePoint d * y := by rw [hyinc]
  · rintro ⟨hxD, hxcentral⟩
    let d : Variety.Point D.carrierVariety := D.pointEquiv.symm ⟨x, hxD⟩
    refine ⟨d, ?_, ?_⟩
    · change d ∈ Subgroup.center (Variety.Point D.carrierVariety)
      rw [Subgroup.mem_center_iff]
      intro y
      apply D.inclusion_injective
      rw [map_mul, map_mul]
      have hy := Subgroup.mem_centralizer_iff.mp hxcentral
        (D.includePoint y) (D.pointEquiv y).property
      have hdinc : D.includePoint d = x := by
        change (D.pointEquiv d).val = x
        simp [d]
      calc
        D.includePoint (y * d) = D.includePoint y * D.includePoint d :=
          D.inclusion.map_mul y d
        _ = D.includePoint y * x := by rw [hdinc]
        _ = x * D.includePoint y := hy
        _ = D.includePoint d * D.includePoint y := by rw [hdinc]
        _ = D.includePoint (d * y) := (D.inclusion.map_mul d y).symm
    · change (D.pointEquiv d).val = x
      simp [d]

/-- The closed derived subgroup of a reductive algebraic group has finite
ambient center. -/
public theorem reductive_derivedClosure_ambientCenter_finite
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsReductiveAlgebraicGroup K) :
    let D := subgroupZariskiClosure K
      (_root_.commutator (Variety.Point K))
    (((D.toSubgroup ⊓ Subgroup.centralizer
        (D.toSubgroup : Set (Variety.Point K))) :
        Subgroup (Variety.Point K)) : Set (Variety.Point K)).Finite := by
  let D := subgroupZariskiClosure K
    (_root_.commutator (Variety.Point K))
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  letI : Finite (Subgroup.center (Variety.Point D.carrierVariety)) :=
    connectedSemisimple_center_finite
      (reductive_derivedClosure_isSemisimple hK)
  have hfinite :
      (D.inclusion.onPoints ''
        (Subgroup.center (Variety.Point D.carrierVariety) :
          Set (Variety.Point D.carrierVariety))).Finite :=
    (Set.toFinite _).image D.inclusion.onPoints
  rwa [derivedClosure_center_image_eq_ambient_intersection] at hfinite

/-- The center of the abstract derived subgroup of a reductive algebraic group
is finite, expressed inside the ambient point group. -/
public theorem reductive_commutator_center_finite
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsReductiveAlgebraicGroup K) :
    (((_root_.commutator (Variety.Point K) ⊓
        Subgroup.centralizer
          (_root_.commutator (Variety.Point K) :
            Set (Variety.Point K))) : Subgroup (Variety.Point K)) :
      Set (Variety.Point K)).Finite := by
  let D := subgroupZariskiClosure K
    (_root_.commutator (Variety.Point K))
  apply (reductive_derivedClosure_ambientCenter_finite hK).subset
  rintro x ⟨hxderived, hxcentral⟩
  constructor
  · exact subset_closure hxderived
  · exact centralizer_le_centralizer_subgroupZariskiClosure
      (_root_.commutator (Variety.Point K)) hxcentral

end Theory.AlgebraicGroup
