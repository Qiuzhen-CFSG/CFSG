module

public import Theory.AlgebraicGroup.Unipotent.ConnectedRadical
public import Theory.AlgebraicGroup.Radical.Image
public import Theory.AlgebraicGroup.Tori.Character.Basis
public import Theory.AlgebraicGroup.PluckerOrbit.Eigenvalue

/-!
The quotient by the connected unipotent radical is reductive. The image of
the solvable radical is the target radical. Triangularization makes its image
commutative, and Jordan decomposition makes every image point semisimple,
because the unipotent factor is killed by the morphism.
The target is constructed as the closed image of the Pluecker conjugation
representation, whose kernel is the prescribed normal subgroup. We retain
point surjectivity and the exact kernel; no universal property is asserted.

Source: GLS3, Theorem 1.7.2(g). The core argument is adapted from the proved
private lemma in `Theory.AlgebraicGroup.QuotientData`, using the narrower
public radical-image theorem in place of its expanded proof.
-/

universe u
set_option linter.style.haveILetI false
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem connectedRadical_quotient_reductive_core
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (Ru R : ClosedSubgroup G)
    (hG : Variety.IsConnected G)
    (hR : IsRadicalSubgroup R)
    (hRu : IsUnipotentRadicalOf R Ru)
    (π : AlgebraicGroup.Morphism G Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel = Ru.toSubgroup) :
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

  have hRS : f.imageClosedSubgroup = S :=
    hR.imageClosedSubgroup_eq_of_surjective_of_kernel_isSolvable π hπsurj hS hkerSolv

  obtain ⟨n, hn, H, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected hR.solvable hKconnected
  let P : TriangularPresentation K := ⟨n, hn, H, e⟩
  let U := P.unipotentRadical
  letI : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
  have hU : IsUnipotentRadicalSubgroup U := P.mem_unipotentRadical_iff_characteristicFree
  have hUunipotent : IsUnipotentAlgebraicGroup U.carrierVariety :=
    hU.isUnipotent_of_solvable_connected hR.solvable hKconnected

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

  have hVleRu : V ≤ Ru := hRu.contains_unipotent_closedSubgroup
    hR.connected hR.solvable hVleR hVunipotent

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

  let I := f.imageClosedSubgroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  obtain ⟨q, hq, hqker, _⟩ := f.closedImageProjection_exists
  have hqU (x : Variety.Point K) (hx : x ∈ U) : q.onPoints x = 1 := by
    apply MonoidHom.mem_ker.mp
    change x ∈ q.kernel
    rw [hqker]
    exact hUleker hx
  have hIconn : Variety.IsConnected I.carrierVariety :=
    connected_of_surjective_morphism q hKconnected hq
  have hIcomm : IsMulCommutative (Variety.Point I.carrierVariety) := by
    apply IsMulCommutative.of_comm
    intro a b
    obtain ⟨x, rfl⟩ := hq a
    obtain ⟨y, rfl⟩ := hq b
    have hxy : x * y * (y * x)⁻¹ ∈ U := by
      change P.diagonalMorphism.onPoints (x * y * (y * x)⁻¹) = 1
      have hc := dVariety_isMulCommutative (k := k) P.n
      rw [isMulCommutative_iff] at hc
      rw [map_mul, map_mul, map_inv, map_mul, hc (P.diagonalMorphism.onPoints x)]
      exact mul_inv_cancel _
    have h := hqU _ hxy
    rw [map_mul, map_mul, map_inv, map_mul, mul_inv_eq_one] at h
    exact h
  have hIsemi : ∀ a : Variety.Point I.carrierVariety,
      IsSemisimpleElement I.carrierVariety a := by
    intro a
    obtain ⟨x, rfl⟩ := hq a
    let d := jordanDecomposition x
    have hu : d.unipotentPart ∈ U := (hU _).mpr d.unipotent
    have hx : q.onPoints x = q.onPoints d.semisimplePart := by
      calc
        q.onPoints x = q.onPoints (d.semisimplePart * d.unipotentPart) :=
          congrArg q.onPoints d.eq_mul
        _ = q.onPoints d.semisimplePart := by rw [map_mul, hqU _ hu, mul_one]
    rw [hx]
    exact morphism_preserves_semisimpleElement q _ d.semisimple
  have htorus : IsSubtorus I :=
    isTorus_of_isConnected_isMulCommutative_all_semisimple hIconn hIcomm hIsemi
  exact hRS ▸ htorus

/-- A surjective morphism whose kernel is the connected unipotent radical
of a connected group has reductive target. -/
public theorem isReductive_of_connectedUnipotentRadical_kernel
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (hG : Variety.IsConnected G) (U : ClosedSubgroup G)
    (hU : IsConnectedUnipotentRadicalOf ClosedSubgroup.top U)
    (π : AlgebraicGroup.Morphism G Q)
    (hπ : Function.Surjective π.onPoints) (hker : π.kernel = U.toSubgroup) :
    IsReductiveAlgebraicGroup Q := by
  obtain ⟨R, hR, hUR⟩ := hU.exists_radical
  exact connectedRadical_quotient_reductive_core U R hG hR hUR π hπ hker

/-- A constructed surjective morphism to a reductive algebraic group with
kernel equal to the specified connected unipotent radical. -/
public theorem exists_reductive_quotient_connectedUnipotentRadical
    {G : Variety k} [AlgebraicGroup G]
    (hG : Variety.IsConnected G) (U : ClosedSubgroup G)
    (hU : IsConnectedUnipotentRadicalOf ClosedSubgroup.top U) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (π : AlgebraicGroup.Morphism G Q),
      Function.Surjective π.onPoints ∧ π.kernel = U.toSubgroup ∧
      IsReductiveAlgebraicGroup Q := by
  obtain ⟨R, hR, hUR⟩ := hU.exists_radical
  let f := U.rightTranslateVanishingPluckerConjugationMorphism
  let T := f.imageClosedSubgroup
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let hmap : ∀ x, f.onPoints x ∈ T.toSubgroup := fun x => ⟨x, rfl⟩
  let π := f.codRestrictClosedSubgroup T hmap
  have hπ : Function.Surjective π.onPoints :=
    f.codRestrictImageClosedSubgroup_surjective hmap
  have hker : π.kernel = U.toSubgroup := by
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_kernel_eq]
    exact U.rightTranslateVanishingPluckerConjugationMorphism_kernel_eq_of_connected
      hG (hUR.normal_of_radical hR)
  exact ⟨T.carrierVariety, inferInstance, π, hπ, hker,
    isReductive_of_connectedUnipotentRadical_kernel hG U hU π hπ hker⟩

end Theory.AlgebraicGroup
