module

import Theory.AlgebraicGroup.Morphism.IsoImageOfPullbackSurjective
import Theory.AlgebraicGroup.Quotient.TorusComparison
import Theory.AlgebraicGroup.Tori.TriangularDiagonalPullbackSurjective
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.ClosedSubgroup.InvariantQuotient
import Theory.AlgebraicGroup.Foundations
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.ClosedSubgroup.Normalizer
public import Theory.AlgebraicGroup.Tori.Maximal
public import Theory.AlgebraicGroup.Tori.SemisimpleElementMaximal
public import Theory.AlgebraicGroup.Unipotent.OneParameter
public import Theory.AlgebraicGroup.Unipotent.Radical
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Borel.IsogenyImage
public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Semisimple.Components
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Semisimple.Versions
public import Theory.AlgebraicGroup.Radical.Defs
public import Theory.AlgebraicGroup.Radical.Image
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight
public import Theory.AlgebraicGroup.Representations.Algebraic.RelativeRoot
public import Theory.AlgebraicGroup.Automorphisms.Graph
public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.Automorphisms.SteinbergSets
public import Theory.AlgebraicGroup.RootSystems.Classification
public import Theory.AlgebraicGroup.RootData.Chevalley
public import Theory.AlgebraicGroup.RootSystems.Dynkin
public import Theory.AlgebraicGroup.RootSystems.Weyl
public import Theory.AlgebraicGroup.RootSystems.AffinePath
public import Theory.AlgebraicGroup.BNPair.Defs
public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicLeviCharacters
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicLeviKernel
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicNormalizer
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicCoordinates
public import Theory.AlgebraicGroup.RootData.HeightSubgroup.Basic
public import Theory.AlgebraicGroup.RootData.BruhatRootFactor
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.RootData.Cocharacters
public import Theory.AlgebraicGroup.RootData.Standard
public import Theory.AlgebraicGroup.RootData.StandardParabolicGenerated
public import Theory.AlgebraicGroup.RootSubgroups.Conjugation
public import Theory.AlgebraicGroup.RootSubgroups.Generation
public import Theory.AlgebraicGroup.Semisimple.RootBlocks
public import Theory.AlgebraicGroup.Parabolic.Defs
public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Instance.PSL
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theory.AlgebraicGroup.Reductive.Basic
universe u v w

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-!  The following interfaces isolate the two geometric inputs which are
needed by the quotient statements.  The first is the already available
quotient theorem from the preceding section.  The remaining interfaces are
the regularity parts of the quotient-isomorphism and radical-quotient
arguments; their hypotheses are exactly the algebraic data used in those
arguments, so that the main theorems below do not hide any additional
assumptions. -/

private theorem quotient_unipotent_radical_is_reductive
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (Ru R : ClosedSubgroup G)
    (hG : Variety.IsConnected G)
    (hR : IsRadicalSubgroup R)
    (hRu : IsUnipotentRadicalOf R Ru)
    (_hRunormal : Ru.toSubgroup.Normal)
    (π : AlgebraicGroup.Morphism G Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel = Ru.toSubgroup) :
    /- Mathematical proof plan: first use `connected_of_surjective_morphism`
       for connectedness of `Q`.  For a radical `S ≤ Q`, pull it back along
       `π`; the pullback is solvable and its unipotent radical contains the
       kernel `Ru`.  The defining maximality of `Ru` then forces the pullback
       radical modulo `Ru` to be a torus, hence `S` is a subtorus. -/
    IsReductiveAlgebraicGroup Q := by

  have hQconnected : Variety.IsConnected Q := by
    exact connected_of_surjective_morphism π hG hπsurj
  refine ⟨hQconnected, ?_⟩
  intro S hS

  have hkerSolv : Group.IsSolvable π.kernel := by
    rw [hπker]
    letI : AlgebraicGroup Ru.carrierVariety := Ru.carrierAlgebraicGroup
    letI : Group.IsSolvable (Variety.Point Ru.carrierVariety) :=
      isSolvable_of_isUnipotentAlgebraicGroup hRu.2.1
    exact Group.isSolvable_of_surjective
      (f := (Equiv.mulEquiv Ru.pointEquiv).toMonoidHom)
      (Equiv.mulEquiv Ru.pointEquiv).surjective

  let K : Variety k := R.carrierVariety
  letI : AlgebraicGroup K := R.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism K Q := π.comp R.inclusion

  have hKconnected : Variety.IsConnected K := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    letI : ConnectedSpace
        {x : Variety.Point G // x ∈ (R : Set (Variety.Point G))} :=
      Subtype.connectedSpace hR.connected
    letI : ConnectedSpace (Variety.Point K) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance

  have hRS : f.imageClosedSubgroup = S := by
    let qR := f
    let I := qR.imageClosedSubgroup
    have hImap : I.toSubgroup = R.toSubgroup.map π.onPoints := by
      ext y
      constructor
      · intro hy
        change y ∈ qR.image at hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨R.inclusion.onPoints x, (R.pointEquiv x).property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        change π.onPoints x ∈ qR.image
        let xR : Variety.Point R.carrierVariety :=
          R.pointEquiv.symm ⟨x, hx⟩
        refine ⟨xR, ?_⟩
        change π.onPoints (R.inclusion.onPoints xR) = π.onPoints x
        apply congrArg π.onPoints
        change (R.pointEquiv xR).val = x
        simp [xR]
    have hInormal : I.toSubgroup.Normal := by
      rw [hImap]
      exact Subgroup.Normal.map hR.normal π.onPoints hπsurj
    have hIconnected : _root_.IsConnected
        (I : Set (Variety.Point Q)) := by
      exact qR.imageClosedSubgroup_isConnected hKconnected
    have hIsolvable : Group.IsSolvable (Variety.Point I.carrierVariety) := by
      exact qR.imageClosedSubgroup_isSolvable hR.solvable
    apply SetLike.coe_injective
    apply Set.Subset.antisymm
    · exact hS.maximal I hInormal hIconnected hIsolvable
    · let P := π.closedSubgroupPreimage S
      let J := P.identityComponentAmbient
      have hPsolvable : Group.IsSolvable
          (Variety.Point P.carrierVariety) :=
        π.closedSubgroupPreimage_isSolvable_of_kernel S hS.solvable
          (π.preimageRestriction_kernel_isSolvable_of_kernel S hkerSolv)
      let iP := J.inclusion.codRestrictClosedSubgroup P (fun x ↦
        P.identityComponentAmbient_le (J.pointEquiv x).property)
      have hiP : Function.Injective iP.onPoints := by
        intro x y hxy
        apply J.inclusion_injective
        have hxy' := congrArg P.inclusion.onPoints hxy
        simpa [iP, Morphism.codRestrictClosedSubgroup_inclusion_apply] using hxy'
      have hJsolvable : Group.IsSolvable
          (Variety.Point J.carrierVariety) :=
        Group.isSolvable_of_isSolvable_injective hiP
      have hJnormal : J.toSubgroup.Normal :=
        P.identityComponentAmbient_normal_of_normal
          (π.closedSubgroupPreimage_normal hS.normal)
      have hJconnected : _root_.IsConnected
          (J : Set (Variety.Point G)) :=
        P.identityComponentAmbient_isConnected
      have hJR : J ≤ R := hR.maximal J hJnormal hJconnected hJsolvable
      have hJimage : (π.comp J.inclusion).imageClosedSubgroup = S :=
        π.closedSubgroupPreimage_identityComponent_image_eq hπsurj S hS.connected
      intro y hy
      have hyJ : y ∈ (π.comp J.inclusion).imageClosedSubgroup := by
        rw [hJimage]
        exact hy
      change y ∈ (π.comp J.inclusion).image at hyJ
      rcases hyJ with ⟨x, hx⟩
      change y ∈ qR.image
      let xG := J.inclusion.onPoints x
      have hxR : xG ∈ R := hJR (J.pointEquiv x).property
      let xR : Variety.Point R.carrierVariety :=
        R.pointEquiv.symm ⟨xG, hxR⟩
      refine ⟨xR, ?_⟩
      change π.onPoints (R.inclusion.onPoints xR) = y
      have hxRAmb : R.inclusion.onPoints xR = xG := by
        change (R.pointEquiv xR).val = xG
        simp [xR]
      rw [hxRAmb]
      exact hx

  obtain ⟨U, hU, hUT⟩ :=
    theorem_1_5_1_d (K := K) hKconnected hR.solvable
  letI : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
  obtain ⟨T, hTmax⟩ := exists_maximalTorus K
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  obtain ⟨hfactor, _hinter⟩ := hUT T hTmax

  have hUnormal : U.toSubgroup.Normal :=
    hU.normal_of_solvable_connected hR.solvable hKconnected

  have hUunipotent : IsUnipotentAlgebraicGroup U.carrierVariety := by
    intro z
    let x := U.inclusion.onPoints z
    have hx : x ∈ U.toSubgroup := (U.pointEquiv z).property
    have hxunipotent := (hU x).mp hx
    have hz := (closedSubgroup_unipotentElement_iff U hx).mp hxunipotent
    have hpoint :
        U.pointEquiv.symm ⟨x, hx⟩ = z := by
      apply U.pointEquiv.injective
      rw [U.pointEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    rw [hpoint] at hz
    exact hz

  let gU : AlgebraicGroup.Morphism U.carrierVariety G :=
    R.inclusion.comp U.inclusion
  let V : ClosedSubgroup G := gU.imageClosedSubgroup
  letI : AlgebraicGroup V.carrierVariety := V.carrierAlgebraicGroup

  have hVleR : V ≤ R := by
    intro x hx
    change x ∈ R.toSubgroup
    change x ∈ gU.image at hx
    rcases hx with ⟨u, rfl⟩
    exact (R.pointEquiv (U.inclusion.onPoints u)).property

  have hVunipotent : IsUnipotentAlgebraicGroup V.carrierVariety := by
    obtain ⟨p, hp, -, _⟩ := gU.closedImageProjection_exists
    exact hUunipotent.of_surjective p hp

  have hVnormal : ∀ b, b ∈ R → ∀ v, v ∈ V →
      b * v * b⁻¹ ∈ V := by
    intro b hb v hv
    change b * v * b⁻¹ ∈ V.toSubgroup
    change v ∈ gU.image at hv
    rcases hv with ⟨u, rfl⟩
    let bK : Variety.Point K := R.pointEquiv.symm ⟨b, hb⟩
    let uK : Variety.Point K := U.inclusion.onPoints u
    have huK : uK ∈ U.toSubgroup := (U.pointEquiv u).property
    have hconjK : bK * uK * bK⁻¹ ∈ U.toSubgroup :=
      hUnormal.conj_mem uK huK bK
    let w : Variety.Point U.carrierVariety :=
      U.pointEquiv.symm ⟨bK * uK * bK⁻¹, hconjK⟩
    refine ⟨w, ?_⟩
    change R.inclusion.onPoints (U.inclusion.onPoints w) =
      b * R.inclusion.onPoints (U.inclusion.onPoints u) * b⁻¹
    have hw : U.inclusion.onPoints w = bK * uK * bK⁻¹ := by
      change (U.pointEquiv w).val = _
      simp [w]
    rw [hw]
    have hbK : R.inclusion.onPoints bK = b := by
      change (R.pointEquiv bK).val = b
      simp [bK]
    simp only [map_mul, map_inv, hbK]
    rfl

  have hVleRu : V ≤ Ru := hRu.2.2.2 V hVleR hVunipotent hVnormal

  have hUleker : U.toSubgroup ≤ f.kernel := by
    intro x hx
    let xU : Variety.Point U.carrierVariety :=
      U.pointEquiv.symm ⟨x, hx⟩
    have hxU : U.inclusion.onPoints xU = x := by
      change (U.pointEquiv xU).val = x
      simp [xU]
    have hxV : gU.onPoints xU ∈ V.toSubgroup := ⟨xU, rfl⟩
    have hxRu : gU.onPoints xU ∈ Ru.toSubgroup := hVleRu hxV
    apply MonoidHom.mem_ker.mpr
    have hmem : R.inclusion.onPoints (U.inclusion.onPoints xU) ∈ π.kernel := by
      rw [hπker]
      change R.inclusion.onPoints (U.inclusion.onPoints xU) ∈ Ru.toSubgroup at hxRu
      exact hxRu
    change π.onPoints (R.inclusion.onPoints (U.inclusion.onPoints xU)) = 1
    exact MonoidHom.mem_ker.mp hmem

  have himage : f.imageClosedSubgroup =
      (f.comp T.inclusion).imageClosedSubgroup := by
    apply SetLike.coe_injective
    ext y
    constructor
    · intro hy
      change y ∈ f.image at hy
      rcases hy with ⟨x, rfl⟩
      obtain ⟨t, u, ht, hu, hxu⟩ := hfactor x
      let tT : Variety.Point T.carrierVariety :=
        T.pointEquiv.symm ⟨t, ht⟩
      have htu : f.onPoints u = 1 :=
        MonoidHom.mem_ker.mp (hUleker hu)
      refine ⟨tT, ?_⟩
      change f.onPoints (T.inclusion.onPoints tT) = f.onPoints x
      have htT : T.inclusion.onPoints tT = t := by
        change (T.pointEquiv tT).val = t
        simp [tT]
      rw [htT, hxu, map_mul, htu, mul_one]
    · intro hy
      change y ∈ (f.comp T.inclusion).image at hy
      rcases hy with ⟨t, rfl⟩
      change f.onPoints (T.inclusion.onPoints t) ∈ f.image
      exact ⟨T.inclusion.onPoints t, rfl⟩

  have htorus : IsSubtorus (f.comp T.inclusion).imageClosedSubgroup :=
    morphism_image_isTorus (f.comp T.inclusion) hTmax.1
  have hRS' : f.imageClosedSubgroup = S := by simpa [f] using hRS
  have htorus' : IsSubtorus f.imageClosedSubgroup := by
    rw [himage]
    exact htorus
  exact hRS' ▸ htorus'

private theorem quotient_radical_is_semisimple
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (R : ClosedSubgroup G)
    (hG : Variety.IsConnected G)
    (hR : IsRadicalSubgroup R)
    (π : AlgebraicGroup.Morphism G Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel = R.toSubgroup) :
    /- Mathematical proof plan: connectedness again descends along the
       surjective quotient.  If `S` is a radical of `Q`, its pullback is a
       solvable normal subgroup of `G`; maximality of `R` puts it inside `R`,
       while the kernel equality identifies its image with the identity.
       Therefore every radical of `Q` is trivial. -/
    IsSemisimpleAlgebraicGroup Q := by
  have hQ : _root_.IsConnected (Set.univ : Set (Variety.Point Q)) :=
    connected_of_surjective_morphism π hG hπsurj
  refine ⟨hQ, ?_⟩
  intro S hS
  have hRsolv : Group.IsSolvable R.toSubgroup := by
    letI : Group.IsSolvable (Variety.Point R.carrierVariety) := hR.solvable
    exact Group.isSolvable_of_surjective
      (f := (Equiv.mulEquiv R.pointEquiv).toMonoidHom)
      (Equiv.mulEquiv R.pointEquiv).surjective
  have hkerSolv : Group.IsSolvable π.kernel := by
    rw [hπker]
    exact hRsolv
  let P := π.closedSubgroupPreimage S
  let I := P.identityComponentAmbient
  have hPsolvable : Group.IsSolvable (Variety.Point P.carrierVariety) :=
    π.closedSubgroupPreimage_isSolvable_of_kernel S hS.solvable
      (π.preimageRestriction_kernel_isSolvable_of_kernel S hkerSolv)
  let iP : AlgebraicGroup.Morphism I.carrierVariety P.carrierVariety :=
    I.inclusion.codRestrictClosedSubgroup P (fun x =>
      P.identityComponentAmbient_le (I.pointEquiv x).property)
  have hiP : Function.Injective iP.onPoints := by
    intro x y hxy
    apply I.inclusion_injective
    have hxyAmbient := congrArg P.inclusion.onPoints hxy
    simpa [iP, Morphism.codRestrictClosedSubgroup_inclusion_apply] using hxyAmbient
  have hIsolvable : Group.IsSolvable (Variety.Point I.carrierVariety) := by
    letI : Group.IsSolvable (Variety.Point P.carrierVariety) := hPsolvable
    exact Group.isSolvable_of_isSolvable_injective hiP
  have hInormal : I.toSubgroup.Normal :=
    P.identityComponentAmbient_normal_of_normal
      (π.closedSubgroupPreimage_normal hS.normal)
  have hIconnected : _root_.IsConnected (I : Set (Variety.Point G)) :=
    P.identityComponentAmbient_isConnected
  have hIR : I ≤ R := hR.maximal I hInormal hIconnected hIsolvable
  have hImage :
      (π.comp I.inclusion).imageClosedSubgroup = S :=
    π.closedSubgroupPreimage_identityComponent_image_eq hπsurj S hS.connected
  have hImageBot :
      (π.comp I.inclusion).imageClosedSubgroup.toSubgroup ≤
        (⊥ : Subgroup (Variety.Point Q)) := by
    intro y hy
    change y ∈ (π.comp I.inclusion).image at hy
    rcases hy with ⟨x, hx⟩
    apply Subgroup.mem_bot.mpr
    rw [← hx]
    change π.onPoints (I.inclusion.onPoints x) = 1
    have hxker : I.inclusion.onPoints x ∈ π.kernel := by
      rw [hπker]
      exact hIR (I.pointEquiv x).property
    exact MonoidHom.mem_ker.mp hxker
  apply SetLike.coe_injective
  apply le_antisymm
  · rw [← hImage]
    exact hImageBot
  · intro x hx
    exact Subgroup.mem_bot.mp hx ▸ S.toSubgroup.one_mem

public theorem theorem_1_5_1_e
    {K : Variety k} [AlgebraicGroup K] (hK : Variety.IsConnected K)
    (hSolv : Group.IsSolvable (Variety.Point K)) :
    ∃ U : ClosedSubgroup K, IsUnipotentRadicalSubgroup U ∧
      ∀ T : ClosedSubgroup K, IsMaximalTorus T →
        ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
          (π : AlgebraicGroup.Morphism K Q),
          Function.Surjective π.onPoints ∧
            π.kernel = U.toSubgroup ∧
            (∀ {I : Variety k} (_ : AlgebraicGroup I)
              (φ : AlgebraicGroup.Morphism K I), U.toSubgroup ≤ φ.kernel →
              ∃! ψ : AlgebraicGroup.Morphism Q I, ψ.comp π = φ) ∧
            ∃ e : AlgebraicGroup.Iso Q T.carrierVariety,
              ∀ t : Variety.Point T.carrierVariety,
                e.hom.onPoints (π.onPoints (T.inclusion.onPoints t)) = t := by
  obtain ⟨n, hn, H, ⟨eP⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected hSolv hK
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation K :=
    { n := n, positive := hn, subgroup := H, iso := eP }
  let U : ClosedSubgroup K := P.unipotentRadical
  have hU : IsUnipotentRadicalSubgroup U := by
    dsimp [U]
    exact P.mem_unipotentRadical_iff_characteristicFree
  refine ⟨U, hU, ?_⟩
  intro T hTmax
  letI : AlgebraicGroup P.diagonalImage.carrierVariety :=
    P.diagonalImage.carrierAlgebraicGroup
  have hItorus : IsTorus P.diagonalImage.carrierVariety :=
    P.diagonalImage_isTorus hK
  have hinc (x : Variety.Point K) :
      P.diagonalImage.inclusion.onPoints
          (P.diagonalImageMorphism.onPoints x) =
        P.diagonalMorphism.onPoints x := by
    simpa only [TriangularPresentation.diagonalImageMorphism] using
      (AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
        P.diagonalMorphism P.diagonalImage (fun z => by
          change P.diagonalMorphism.onPoints z ∈ P.diagonalMorphism.image
          exact ⟨z, rfl⟩) x)
  have hdiagSurj : Function.Surjective
      P.diagonalImageMorphism.onPoints := by
    intro y
    have hy := (P.diagonalImage.pointEquiv y).property
    change (P.diagonalImage.pointEquiv y).val ∈
      P.diagonalMorphism.image at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply P.diagonalImage.inclusion_injective
    exact (hinc x).trans hx
  have hTimage : IsMaximalTorus
      ((P.diagonalImageMorphism.comp T.inclusion).imageClosedSubgroup) :=
    theorem_1_4_3_d P.diagonalImageMorphism hdiagSurj T hTmax
  have hStop :
      (P.diagonalImageMorphism.comp T.inclusion).imageClosedSubgroup =
        ClosedSubgroup.top := by
    symm
    apply hTimage.2
    · exact closedSubgroup_top_isTorus
        P.diagonalImage.carrierVariety hItorus
    · rw [ClosedSubgroup.le_iff_le_toSubgroup]
      exact le_top
  have hpiTsurj : ∀ y : Variety.Point P.diagonalImage.carrierVariety,
      ∃ t : Variety.Point T.carrierVariety,
        P.diagonalImageMorphism.onPoints (T.inclusion.onPoints t) = y := by
    intro y
    have hyS : y ∈
        ((P.diagonalImageMorphism.comp T.inclusion).imageClosedSubgroup :
          Set (Variety.Point P.diagonalImage.carrierVariety)) := by
      rw [hStop]
      trivial
    have hSset :
        ((P.diagonalImageMorphism.comp T.inclusion).imageClosedSubgroup :
          Set (Variety.Point P.diagonalImage.carrierVariety)) =
        Set.range (P.diagonalImageMorphism.comp T.inclusion).onPoints := by
      exact (P.diagonalImageMorphism.comp T.inclusion).imageClosedSubgroup_carrier.trans
        (P.diagonalImageMorphism.comp T.inclusion).image_carrier
    rw [hSset] at hyS
    rcases hyS with ⟨t, ht⟩
    exact ⟨t, ht⟩
  have hfactor : ∀ x : Variety.Point K, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u := by
    intro x
    obtain ⟨tT, htT⟩ := hpiTsurj
      (P.diagonalImageMorphism.onPoints x)
    let t : Variety.Point K := T.inclusion.onPoints tT
    let u : Variety.Point K := t⁻¹ * x
    have ht : t ∈ T.toSubgroup := by
      change (T.pointEquiv tT).val ∈ T.toSubgroup
      exact (T.pointEquiv tT).property
    have htx : P.diagonalImageMorphism.onPoints t =
        P.diagonalImageMorphism.onPoints x := by
      simpa [t] using htT
    have hpiu : P.diagonalImageMorphism.onPoints u = 1 := by
      change P.diagonalImageMorphism.onPoints (t⁻¹ * x) = 1
      rw [map_mul, map_inv, htx]
      simp
    have hdiag : P.diagonalMorphism.onPoints u = 1 := by
      rw [← hinc u, hpiu]
      exact P.diagonalImage.inclusion.map_one
    have hu : u ∈ U.toSubgroup := by
      change u ∈ P.unipotentRadical
      exact P.mem_unipotentRadical_iff_diagonal u |>.mpr hdiag
    refine ⟨t, u, ht, hu, ?_⟩
    dsimp [u]
    group
  have hUnormal := hU.normal_of_solvable_connected hSolv hK
  obtain ⟨Q, hQ, π, hπsurj, hπker, hquot⟩ :=
    theorem_1_1_2_b U hUnormal
  letI : AlgebraicGroup Q := hQ
  let fTri : AlgebraicGroup.Morphism T.carrierVariety (tVariety k P.n) :=
    (P.subgroup.inclusion.comp P.iso.hom).comp T.inclusion
  have hsubgroupPull : Function.Surjective
      P.subgroup.inclusion.toVariety.pullbackRingHom := by
    exact P.subgroup.restrictionRingHom_surjective
  have hisoPull : Function.Surjective
      P.iso.hom.toVariety.pullbackRingHom :=
    algebraicGroupIso_hom_pullbackRingHom_surjective P.iso
  have hambientPull : Function.Surjective
      (P.subgroup.inclusion.comp P.iso.hom).toVariety.pullbackRingHom := by
    rw [show (P.subgroup.inclusion.comp P.iso.hom).toVariety.pullbackRingHom =
        P.iso.hom.toVariety.pullbackRingHom.comp
          P.subgroup.inclusion.toVariety.pullbackRingHom from
      Variety.Morphism.pullbackRingHom_comp
        P.subgroup.inclusion.toVariety P.iso.hom.toVariety]
    exact hisoPull.comp hsubgroupPull
  have hfTriPull : Function.Surjective fTri.toVariety.pullbackRingHom := by
    rw [show fTri.toVariety.pullbackRingHom =
        T.inclusion.toVariety.pullbackRingHom.comp
          (P.subgroup.inclusion.comp P.iso.hom).toVariety.pullbackRingHom from by
      dsimp only [fTri]
      exact Variety.Morphism.pullbackRingHom_comp
        (P.subgroup.inclusion.comp P.iso.hom).toVariety T.inclusion.toVariety]
    exact T.restrictionRingHom_surjective.comp hambientPull
  let fTdiag := (tDiagonalMorphism P.n).comp fTri
  have hfTdiagPull : Function.Surjective
      fTdiag.toVariety.pullbackRingHom := by
    exact triangularMorphism_diagonal_pullbackRingHom_surjective
      hTmax.1 P.n fTri hfTriPull
  let I := fTdiag.imageClosedSubgroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  obtain ⟨eTI, heTI⟩ :=
    fTdiag.iso_imageClosedSubgroup_of_pullbackRingHom_surjective hfTdiagPull
  have hdeltaMap (x : Variety.Point K) :
      P.diagonalMorphism.onPoints x ∈ I.toSubgroup := by
    change P.diagonalMorphism.onPoints x ∈ fTdiag.image
    obtain ⟨t, u, ht, hu, htu⟩ := hfactor x
    let tT : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨t, ht⟩
    refine ⟨tT, ?_⟩
    have htT : T.inclusion.onPoints tT = t := by
      change (T.pointEquiv tT).val = t
      simp [tT]
    have hdiagu : P.diagonalMorphism.onPoints u = 1 := by
      change u ∈ P.diagonalMorphism.kernel
      change u ∈ U.toSubgroup at hu
      exact hu
    change fTdiag.onPoints tT = P.diagonalMorphism.onPoints x
    rw [htu, map_mul, hdiagu, mul_one, ← htT]
    rfl
  let delta : AlgebraicGroup.Morphism K I.carrierVariety :=
    P.diagonalMorphism.codRestrictClosedSubgroup I hdeltaMap
  have hdeltaKer : U.toSubgroup ≤ delta.kernel := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply I.inclusion_injective
    have hxkernel : x ∈ P.diagonalMorphism.kernel := by
      change x ∈ U.toSubgroup at hx
      exact hx
    calc
      I.inclusion.onPoints (delta.onPoints x) =
          P.diagonalMorphism.onPoints x :=
        Morphism.codRestrictClosedSubgroup_inclusion_apply
          P.diagonalMorphism I hdeltaMap x
      _ = 1 := MonoidHom.mem_ker.mp hxkernel
      _ = I.inclusion.onPoints 1 := I.inclusion.map_one.symm
  have heTI' : eTI.hom = delta.comp T.inclusion := by
    rw [heTI]
    apply AlgebraicGroup.Morphism.ext
    funext t
    apply I.inclusion_injective
    calc
      I.inclusion.onPoints
          ((fTdiag.codRestrictClosedSubgroup I (fun y => by
            change fTdiag.onPoints y ∈ fTdiag.image
            exact ⟨y, rfl⟩)).onPoints t) =
          fTdiag.onPoints t :=
        Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
      _ = P.diagonalMorphism.onPoints (T.inclusion.onPoints t) := by rfl
      _ = I.inclusion.onPoints (delta.onPoints (T.inclusion.onPoints t)) :=
        (Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _).symm
      _ = I.inclusion.onPoints ((delta.comp T.inclusion).onPoints t) := by rfl
  obtain ⟨e, he⟩ := quotient_iso_torus_of_comparison U T π
    hπsurj hπker hfactor hquot delta hdeltaKer eTI heTI'
  exact ⟨Q, hQ, π, hπsurj, hπker, hquot, e, he⟩

public theorem theorem_1_7_2_g
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    ∃ Ru R : ClosedSubgroup G,
      IsRadicalSubgroup R ∧ IsUnipotentRadicalOf R Ru ∧
      (∃ (Qᵤ : Variety k) (_ : AlgebraicGroup Qᵤ)
        (πᵤ : AlgebraicGroup.Morphism G Qᵤ),
        Function.Surjective πᵤ.onPoints ∧ πᵤ.kernel = Ru.toSubgroup ∧
        (∀ {I : Variety k} (_ : AlgebraicGroup I)
          (φ : AlgebraicGroup.Morphism G I), Ru.toSubgroup ≤ φ.kernel →
          ∃! ψ : AlgebraicGroup.Morphism Qᵤ I, ψ.comp πᵤ = φ) ∧
        IsReductiveAlgebraicGroup Qᵤ) ∧
      (∃ (Qᵣ : Variety k) (_ : AlgebraicGroup Qᵣ)
        (πᵣ : AlgebraicGroup.Morphism G Qᵣ),
        Function.Surjective πᵣ.onPoints ∧ πᵣ.kernel = R.toSubgroup ∧
        (∀ {I : Variety k} (_ : AlgebraicGroup I)
          (φ : AlgebraicGroup.Morphism G I), R.toSubgroup ≤ φ.kernel →
          ∃! ψ : AlgebraicGroup.Morphism Qᵣ I, ψ.comp πᵣ = φ) ∧
        IsSemisimpleAlgebraicGroup Qᵣ) := by
  obtain ⟨R, Ru, hR, hRu⟩ := exists_radical_with_unipotent_radical (G := G)
  have hRunormal := hRu.normal_of_radical hR
  obtain ⟨QU, hQU, πU, hπUsurj, hπUker, hUquot⟩ :=
    theorem_1_1_2_b Ru hRunormal
  obtain ⟨QR, hQR, πR, hπRsurj, hπRker, hRquot⟩ :=
    theorem_1_1_2_b R hR.normal
  letI : AlgebraicGroup QU := hQU
  letI : AlgebraicGroup QR := hQR
  have hred := quotient_unipotent_radical_is_reductive Ru R hG hR hRu
    hRunormal πU hπUsurj hπUker
  have hsemi := quotient_radical_is_semisimple R hG hR πR hπRsurj hπRker
  refine ⟨Ru, R, hR, hRu, ?_, ?_⟩
  · exact ⟨QU, hQU, πU, hπUsurj, hπUker, hUquot, hred⟩
  · exact ⟨QR, hQR, πR, hπRsurj, hπRker, hRquot, hsemi⟩

public def setMul {A : Type*} [Mul A] (S R : Set A) : Set A :=
  {x | ∃ s ∈ S, ∃ r ∈ R, x = s * r}

end Theory.AlgebraicGroup
