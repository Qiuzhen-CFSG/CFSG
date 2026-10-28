module

public import Theory.AlgebraicGroup.Dimension.Group

universe u

/-! Strict dimension inequalities for closed subvarieties and closed subgroups -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- The coordinate-field dimension of a proper irreducible closed subset is
strictly smaller than that of an irreducible component containing it. -/
public theorem irreducible_closed_fraction_dimension_lt_component
    {V : Variety k} {C D : Set (Variety.Point V)}
    (hCz : IsZariskiClosed V C) (hCi : IsIrreducible C)
    (hD : D ∈ irreducibleComponents (Variety.Point V)) (hCD : C ⊂ D) :
    Algebra.trdeg k
        (FractionRing (coordinateRing (Variety.closedSubvariety hCz))) <
      Variety.componentDimension V D hD := by
  let hDz : IsZariskiClosed V D := Variety.isClosed_iff_isZariskiClosed.mp
    (isClosed_of_mem_irreducibleComponents D hD)
  let R := MvPolynomial V.Coordinates k
  let J : Ideal R := vanishingIdeal D
  let I : Ideal R := vanishingIdeal C
  have hJI : J < I := by
    simpa [J, I] using vanishingIdeal_strict_antitone hDz hCz hCD
  let A := R ⧸ J
  let Q : Ideal A := I.map (Ideal.Quotient.mkₐ k J)
  have hdomJ : IsDomain A := by
    have hprimeJ : J.IsPrime := by
      simpa [J] using isPrime_vanishingIdeal_of_isIrreducible_set hDz hD.1
    exact (Ideal.Quotient.isDomain_iff_prime J).mpr hprimeJ
  let : IsDomain A := hdomJ
  have hdomI : IsDomain (R ⧸ I) := by
    have hprimeI : I.IsPrime := by
      simpa [I] using isPrime_vanishingIdeal_of_isIrreducible_set hCz hCi
    exact (Ideal.Quotient.isDomain_iff_prime I).mpr hprimeI
  have hprimeC : I.IsPrime := by
    simpa [I] using isPrime_vanishingIdeal_of_isIrreducible_set hCz hCi
  have hprimeW : (vanishingIdeal (Set.univ : Set (Variety.Point
      (Variety.closedSubvariety hCz)))).IsPrime := by
    rw [vanishingIdeal_closedSubvariety hCz]
    simpa [I] using hprimeC
  let : IsDomain (coordinateRing (Variety.closedSubvariety hCz)) :=
    (Ideal.Quotient.isDomain_iff_prime
      (vanishingIdeal (Set.univ : Set (Variety.Point
        (Variety.closedSubvariety hCz))))).mpr hprimeW
  let e : (A ⧸ Q) ≃ₐ[k] R ⧸ I := by
    simpa [A, Q] using DoubleQuot.quotQuotEquivQuotOfLEₐ k hJI.le
  let : IsDomain (A ⧸ Q) := e.toRingEquiv.isDomain_iff.mpr hdomI
  have hQ : Q ≠ ⊥ := by
    intro hQ0
    have hle : I ≤ RingHom.ker (Ideal.Quotient.mkₐ k J).toRingHom :=
      (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mkₐ k J)).mp hQ0
    have hle' : I ≤ J := by
      have hker : RingHom.ker (Ideal.Quotient.mkₐ k J).toRingHom = J :=
        Ideal.Quotient.mkₐ_ker k J
      exact hker ▸ hle
    exact (not_le_of_gt hJI) hle'
  have hstrict : Algebra.trdeg k (A ⧸ Q) < Algebra.trdeg k A :=
    trdeg_quotient_lt_of_ne_bot A Q hQ
  calc
    Algebra.trdeg k
        (FractionRing (coordinateRing (Variety.closedSubvariety hCz))) =
        Algebra.trdeg k (R ⧸ I) := by
      rw [trdeg_fractionRing_eq]
      change Algebra.trdeg k (MvPolynomial V.Coordinates k ⧸
        vanishingIdeal (Set.univ : Set (Variety.Point
          (Variety.closedSubvariety hCz)))) = Algebra.trdeg k (R ⧸ I)
      rw [vanishingIdeal_closedSubvariety hCz]
    _ = Algebra.trdeg k (A ⧸ Q) := e.trdeg_eq.symm
    _ < Algebra.trdeg k A := hstrict
    _ = Algebra.trdeg k (FractionRing A) := (trdeg_fractionRing_eq A).symm
    _ = Variety.componentDimension V D hD := by
      simp only [Variety.componentDimension]
      change Algebra.trdeg k (FractionRing A) = Algebra.trdeg k
        (FractionRing (MvPolynomial V.Coordinates k ⧸
          vanishingIdeal (Set.univ : Set (Variety.Point
            (Variety.closedSubvariety hDz)))))
      rw [vanishingIdeal_closedSubvariety hDz]

/-- A proper irreducible closed subset of an irreducible component has
strictly smaller dimension. -/
public theorem proper_irreducible_closed_dimension_lt
    {V : Variety k} {C D : Set (Variety.Point V)}
    (hCz : IsZariskiClosed V C) (hCi : IsIrreducible C)
    (hD : D ∈ irreducibleComponents (Variety.Point V)) (hCD : C ⊂ D) :
    Variety.dimension (Variety.closedSubvariety hCz) <
      Variety.componentDimension V D hD := by
  let W := Variety.closedSubvariety hCz
  let : Nonempty (Variety.Point W) := by
    rcases hCi.1 with ⟨x, hx⟩
    exact ⟨(Variety.closedSubvarietyPointEquiv hCz).symm ⟨x, hx⟩⟩
  have hprimeW : (vanishingIdeal (Set.univ : Set (Variety.Point W))).IsPrime := by
    rw [vanishingIdeal_closedSubvariety hCz]
    exact isPrime_vanishingIdeal_of_isIrreducible_set hCz hCi
  have hWirr : IsIrreducible (Set.univ : Set (Variety.Point W)) :=
    isIrreducible_univ_of_prime_vanishingIdeal W hprimeW
  rw [dimension_eq_fractionRing_of_isIrreducible W hWirr]
  exact irreducible_closed_fraction_dimension_lt_component hCz hCi hD hCD

/-- A proper inclusion between irreducible closed subvarieties strictly raises
dimension.  This is the form needed for chains of connected closed subgroups. -/
public theorem proper_irreducible_closed_subvariety_dimension_lt
    {V : Variety k} {C D : Set (Variety.Point V)}
    (hCz : IsZariskiClosed V C) (hCi : IsIrreducible C)
    (hDz : IsZariskiClosed V D) (hDi : IsIrreducible D) (hCD : C ⊂ D) :
    Variety.dimension (Variety.closedSubvariety hCz) <
      Variety.dimension (Variety.closedSubvariety hDz) := by
  let WC := Variety.closedSubvariety hCz
  let WD := Variety.closedSubvariety hDz
  let : Nonempty (Variety.Point WC) := by
    rcases hCi.1 with ⟨x, hx⟩
    exact ⟨(Variety.closedSubvarietyPointEquiv hCz).symm ⟨x, hx⟩⟩
  let : Nonempty (Variety.Point WD) := by
    rcases hDi.1 with ⟨x, hx⟩
    exact ⟨(Variety.closedSubvarietyPointEquiv hDz).symm ⟨x, hx⟩⟩
  have hprimeWC : (vanishingIdeal
      (Set.univ : Set (Variety.Point WC))).IsPrime := by
    rw [vanishingIdeal_closedSubvariety hCz]
    exact isPrime_vanishingIdeal_of_isIrreducible_set hCz hCi
  have hprimeWD : (vanishingIdeal
      (Set.univ : Set (Variety.Point WD))).IsPrime := by
    rw [vanishingIdeal_closedSubvariety hDz]
    exact isPrime_vanishingIdeal_of_isIrreducible_set hDz hDi
  have hWCi : IsIrreducible (Set.univ : Set (Variety.Point WC)) :=
    isIrreducible_univ_of_prime_vanishingIdeal WC hprimeWC
  have hWDi : IsIrreducible (Set.univ : Set (Variety.Point WD)) :=
    isIrreducible_univ_of_prime_vanishingIdeal WD hprimeWD
  rw [dimension_eq_fractionRing_of_isIrreducible WC hWCi,
    dimension_eq_fractionRing_of_isIrreducible WD hWDi]
  let R := MvPolynomial V.Coordinates k
  let J : Ideal R := vanishingIdeal D
  let I : Ideal R := vanishingIdeal C
  have hJI : J < I := by
    simpa [J, I] using vanishingIdeal_strict_antitone hDz hCz hCD
  let A := R ⧸ J
  let Q : Ideal A := I.map (Ideal.Quotient.mkₐ k J)
  have hdomJ : IsDomain A := by
    have hprimeJ : J.IsPrime := by
      simpa [J] using isPrime_vanishingIdeal_of_isIrreducible_set hDz hDi
    exact (Ideal.Quotient.isDomain_iff_prime J).mpr hprimeJ
  let : IsDomain A := hdomJ
  have hdomI : IsDomain (R ⧸ I) := by
    have hprimeI : I.IsPrime := by
      simpa [I] using isPrime_vanishingIdeal_of_isIrreducible_set hCz hCi
    exact (Ideal.Quotient.isDomain_iff_prime I).mpr hprimeI
  let e : (A ⧸ Q) ≃ₐ[k] R ⧸ I := by
    simpa [A, Q] using DoubleQuot.quotQuotEquivQuotOfLEₐ k hJI.le
  let : IsDomain (A ⧸ Q) := e.toRingEquiv.isDomain_iff.mpr hdomI
  have hQ : Q ≠ ⊥ := by
    intro hQ0
    have hle : I ≤ RingHom.ker (Ideal.Quotient.mkₐ k J).toRingHom :=
      (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mkₐ k J)).mp hQ0
    have hle' : I ≤ J := by
      have hker : RingHom.ker (Ideal.Quotient.mkₐ k J).toRingHom = J :=
        Ideal.Quotient.mkₐ_ker k J
      exact hker ▸ hle
    exact (not_le_of_gt hJI) hle'
  have hstrict : Algebra.trdeg k (A ⧸ Q) < Algebra.trdeg k A :=
    trdeg_quotient_lt_of_ne_bot A Q hQ
  calc
    Algebra.trdeg k (FractionRing (coordinateRing WC)) =
        Algebra.trdeg k (R ⧸ I) := by
      rw [trdeg_fractionRing_eq]
      change Algebra.trdeg k (MvPolynomial V.Coordinates k ⧸
        vanishingIdeal (Set.univ : Set (Variety.Point WC))) =
          Algebra.trdeg k (R ⧸ I)
      rw [vanishingIdeal_closedSubvariety hCz]
    _ = Algebra.trdeg k (A ⧸ Q) := e.trdeg_eq.symm
    _ < Algebra.trdeg k A := hstrict
    _ = Algebra.trdeg k (FractionRing A) := (trdeg_fractionRing_eq A).symm
    _ = Algebra.trdeg k (FractionRing (coordinateRing WD)) := by
      change Algebra.trdeg k (FractionRing A) =
        Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸
          vanishingIdeal (Set.univ : Set (Variety.Point WD))))
      rw [vanishingIdeal_closedSubvariety hDz]

/-- Equal ambient closed sets give equal closed-subvariety dimensions,
independently of the chosen closedness proofs. -/
public theorem closedSubvariety_dimension_congr
    {V : Variety k} {S T : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) (hT : IsZariskiClosed V T) (hST : S = T) :
    Variety.dimension (Variety.closedSubvariety hS) =
      Variety.dimension (Variety.closedSubvariety hT) := by
  subst T
  rfl

/-- The identity component of a closed subgroup maps onto the ambient
identity component exactly when the latter is contained in the subgroup. -/
public theorem ClosedSubgroup.image_identityComponent_eq_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.inclusion.onPoints ''
        Theory.AlgebraicGroup.identityComponent H.carrierVariety =
        Theory.AlgebraicGroup.identityComponent G ↔
      Theory.AlgebraicGroup.identityComponent G ⊆
        (H.toSubgroup : Set (Variety.Point G)) := by
  constructor
  · intro himage x hx
    rw [← himage] at hx
    rcases hx with ⟨y, -, rfl⟩
    exact (H.pointEquiv y).2
  · intro hG₀H
    apply Set.Subset.antisymm
    · exact H.inclusion.image_identityComponent_subset
    · intro x hx
      let eH := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
      let j : {z : Variety.Point G //
          z ∈ Theory.AlgebraicGroup.identityComponent G} →
          Variety.Point H.carrierVariety := fun z =>
        eH.symm ⟨z.1, hG₀H z.2⟩
      let : ConnectedSpace {z : Variety.Point G //
          z ∈ Theory.AlgebraicGroup.identityComponent G} :=
        Subtype.connectedSpace (Theory.AlgebraicGroup.identityComponent_isConnected G)
      have hj : Continuous j :=
        eH.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
      have hRconn : _root_.IsConnected (Set.range j) := isConnected_range hj
      let z₀ : {z : Variety.Point G //
          z ∈ Theory.AlgebraicGroup.identityComponent G} :=
        ⟨1, Theory.AlgebraicGroup.one_mem_identityComponent G⟩
      have hjone : j z₀ = (1 : Variety.Point H.carrierVariety) := by
        apply eH.injective
        apply Subtype.ext
        rfl
      have honeR : (1 : Variety.Point H.carrierVariety) ∈ Set.range j :=
        ⟨z₀, hjone⟩
      have hRsub : Set.range j ⊆
          connectedComponent (1 : Variety.Point H.carrierVariety) :=
        hRconn.subset_connectedComponent honeR
      let z : {z : Variety.Point G //
          z ∈ Theory.AlgebraicGroup.identityComponent G} := ⟨x, hx⟩
      have hjz : j z ∈
          Theory.AlgebraicGroup.identityComponent H.carrierVariety :=
        hRsub ⟨z, rfl⟩
      refine ⟨j z, hjz, ?_⟩
      change (eH (j z)).1 = x
      rw [show j z = eH.symm ⟨x, hG₀H hx⟩ from rfl,
        eH.apply_symm_apply]

/-- Proposition 1.1.6(c), equality criterion: a closed subgroup has the same
dimension as the ambient algebraic group exactly when it contains the ambient
identity component. -/
public theorem closedSubgroup_dimension_eq_iff_contains_identityComponent
    (G : Variety k) [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.dimension H.carrierVariety = Variety.dimension G ↔
      Theory.AlgebraicGroup.identityComponent G ⊆
        (H.toSubgroup : Set (Variety.Point G)) := by
  let W : Variety k := H.carrierVariety
  let T : Set (Variety.Point W) := Theory.AlgebraicGroup.identityComponent W
  let hTz : IsZariskiClosed W T := Theory.AlgebraicGroup.identityComponent_isClosed W
  have hTC : T ∈ irreducibleComponents (Variety.Point W) :=
    Theory.AlgebraicGroup.identityComponent_mem_irreducibleComponents W
  let I : Set (Variety.Point G) :=
    (fun y : Variety.Point W =>
      (Variety.closedSubvarietyPointEquiv H.isZariskiClosed y).1) '' T
  have hinc : H.inclusion.onPoints =
      (fun y : Variety.Point W =>
        (Variety.closedSubvarietyPointEquiv H.isZariskiClosed y).1) := rfl
  have hIC := component_image_isIrreducible_closed H.isZariskiClosed hTC
  have hIi : IsIrreducible I := by simpa [I, T, W] using hIC.1
  let hIz : IsZariskiClosed G I := by
    simpa [I, T, W] using hIC.2
  have hdimImage : Variety.dimension (Variety.closedSubvariety hTz) =
      Variety.dimension (Variety.closedSubvariety hIz) := by
    simpa [I, T, W, hTz, hIz] using
      (closedSubvariety_image_dimension_eq_of_isIrreducible
        H.isZariskiClosed hTz hTC.1)
  have hdimT : Variety.dimension (Variety.closedSubvariety hTz) =
      Variety.dimension W := by
    let W₀ := Theory.AlgebraicGroup.identityComponentClosedSubgroup W
    have hset : T = (W₀.toSubgroup : Set (Variety.Point W)) := by
      ext x
      rfl
    calc
      Variety.dimension (Variety.closedSubvariety hTz) =
          Variety.dimension W₀.carrierVariety :=
        closedSubvariety_dimension_congr hTz W₀.isZariskiClosed hset
      _ = Variety.dimension W :=
        Theory.AlgebraicGroup.dimension_identityComponentClosedSubgroup W
  let G₀ : Set (Variety.Point G) := Theory.AlgebraicGroup.identityComponent G
  let hG₀z : IsZariskiClosed G G₀ := Theory.AlgebraicGroup.identityComponent_isClosed G
  have hdimG₀ : Variety.dimension (Variety.closedSubvariety hG₀z) =
      Variety.dimension G := by
    let G₀' := Theory.AlgebraicGroup.identityComponentClosedSubgroup G
    have hset : G₀ = (G₀'.toSubgroup : Set (Variety.Point G)) := by
      ext x
      rfl
    calc
      Variety.dimension (Variety.closedSubvariety hG₀z) =
          Variety.dimension G₀'.carrierVariety :=
        closedSubvariety_dimension_congr hG₀z G₀'.isZariskiClosed hset
      _ = Variety.dimension G :=
        Theory.AlgebraicGroup.dimension_identityComponentClosedSubgroup G
  constructor
  · intro hdim
    by_contra hnot
    have hIG₀ : I ⊆ G₀ := by
      have hsub := H.inclusion.image_identityComponent_subset
      rw [hinc] at hsub
      simpa [I, T, W, G₀] using hsub
    have hIne : I ≠ G₀ := by
      intro hEq
      apply hnot
      apply (H.image_identityComponent_eq_iff).mp
      rw [hinc]
      simpa [I, T, W, G₀] using hEq
    have hproper : I ⊂ G₀ := ⟨hIG₀, by
      intro hG₀I
      exact hIne (Set.Subset.antisymm hIG₀ hG₀I)⟩
    have hlt := proper_irreducible_closed_dimension_lt hIz hIi
      (Theory.AlgebraicGroup.identityComponent_mem_irreducibleComponents G) hproper
    have hlt' : Variety.dimension (Variety.closedSubvariety hIz) <
        Variety.dimension G := by
      rw [Theory.AlgebraicGroup.dimension_eq_identityComponent G]
      exact hlt
    have hWHlt : Variety.dimension W < Variety.dimension G := by
      rw [← hdimT, hdimImage]
      exact hlt'
    exact (ne_of_lt hWHlt) hdim
  · intro hG₀H
    have hIeq : I = G₀ := by
      have hEq := H.image_identityComponent_eq_iff.mpr hG₀H
      rw [hinc] at hEq
      simpa [I, T, W, G₀] using hEq
    calc
      Variety.dimension W =
          Variety.dimension (Variety.closedSubvariety hTz) := hdimT.symm
      _ = Variety.dimension (Variety.closedSubvariety hIz) := hdimImage
      _ = Variety.dimension (Variety.closedSubvariety hG₀z) := by
        exact closedSubvariety_dimension_congr hIz hG₀z hIeq
      _ = Variety.dimension G := hdimG₀

/-- A connected closed subgroup is irreducible as a closed subset of the
ambient algebraic group. -/
public theorem ClosedSubgroup.isIrreducible_of_isConnected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    IsIrreducible (H : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  have hHconn : Variety.IsConnected H.carrierVariety :=
    connectedSpace_iff_univ.mp inferInstance
  have hHirr : IsIrreducible
      (Set.univ : Set (Variety.Point H.carrierVariety)) :=
    connectedAlgebraicGroup_irreducible H.carrierVariety hHconn
  have himage := hHirr.image H.inclusion.onPoints
    H.inclusion.toVariety.continuous.continuousOn
  have hrange : H.inclusion.onPoints ''
      (Set.univ : Set (Variety.Point H.carrierVariety)) =
        (H : Set (Variety.Point G)) := by
    rw [Set.image_univ]
    change Set.range H.inclusion.onPoints =
      (H.toSubgroup : Set (Variety.Point G))
    exact H.range_inclusion
  rwa [hrange] at himage

/-- Proper inclusion of connected closed subgroups strictly increases their
dimension. -/
public theorem connected_closedSubgroup_dimension_lt_of_le_of_ne
    {G : Variety k} [AlgebraicGroup G] (H K : ClosedSubgroup G)
    (hHK : H ≤ K) (hne : H ≠ K)
    (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (hK : _root_.IsConnected (K : Set (Variety.Point G))) :
    Variety.dimension H.carrierVariety <
      Variety.dimension K.carrierVariety := by
  have hproper : (H : Set (Variety.Point G)) ⊂
      (K : Set (Variety.Point G)) := by
    refine ⟨hHK, ?_⟩
    intro hKH
    apply hne
    apply SetLike.coe_injective
    exact Set.Subset.antisymm hHK hKH
  exact proper_irreducible_closed_subvariety_dimension_lt
    H.isZariskiClosed (H.isIrreducible_of_isConnected hH)
    K.isZariskiClosed (K.isIrreducible_of_isConnected hK) hproper

end Theory.AlgebraicGroup
