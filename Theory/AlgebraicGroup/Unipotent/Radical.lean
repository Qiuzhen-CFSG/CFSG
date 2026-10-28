module

public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.Unipotent.Basic
public import Theory.AlgebraicGroup.Tori.Maximal
public import Theory.AlgebraicGroup.Tori.UnipotentIntersection

universe u

set_option linter.style.haveILetI false

/-! Unipotent radicals of closed subgroups.

The ambient normality result below is obtained by conjugation
characteristicity: conjugating a unipotent radical of a radical subgroup
again produces a unipotent radical of the same subgroup, so uniqueness
identifies the conjugate with the original subgroup.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A unipotent radical of a closed subgroup is its largest closed unipotent
normal subgroup. -/
@[expose]
public def IsUnipotentRadicalOf
    {G : Variety k} [AlgebraicGroup G]
    (B U : ClosedSubgroup G) : Prop :=
  U ≤ B ∧
    IsUnipotentAlgebraicGroup U.carrierVariety ∧
    (∀ b, b ∈ B → ∀ u, u ∈ U → b * u * b⁻¹ ∈ U) ∧
    ∀ V : ClosedSubgroup G,
      V ≤ B → IsUnipotentAlgebraicGroup V.carrierVariety →
      (∀ b, b ∈ B → ∀ v, v ∈ V → b * v * b⁻¹ ∈ V) → V ≤ U

/-- Internal construction of a radical together with connectedness of its
unipotent radical. -/
private lemma exists_unipotent_radical_core
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    (R : ClosedSubgroup G)
    (hRconnected : _root_.IsConnected (R : Set (Variety.Point G)))
    (hRsolvable : Group.IsSolvable (Variety.Point R.carrierVariety)) :
    ∃ U : ClosedSubgroup G,
      IsUnipotentRadicalOf R U ∧
      _root_.IsConnected (U : Set (Variety.Point G)) ∧
      ∀ V : ClosedSubgroup G, V ≤ R →
        IsUnipotentAlgebraicGroup V.carrierVariety → V ≤ U := by
  let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
  letI : ConnectedSpace
      {x : Variety.Point G // x ∈ (R : Set (Variety.Point G))} :=
    Subtype.connectedSpace hRconnected
  letI : ConnectedSpace (Variety.Point R.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  have hRcarrierConnected : Variety.IsConnected R.carrierVariety :=
    connectedSpace_iff_univ.mp inferInstance
  obtain ⟨U0, hU0⟩ :=
    exists_unipotentRadicalSubgroup_of_solvable_connected
      hRsolvable hRcarrierConnected
  letI : AlgebraicGroup U0.carrierVariety := U0.carrierAlgebraicGroup
  have hU0normal : U0.toSubgroup.Normal :=
    hU0.normal_of_solvable_connected hRsolvable hRcarrierConnected
  let f : AlgebraicGroup.Morphism R.carrierVariety G := R.inclusion
  let g : AlgebraicGroup.Morphism U0.carrierVariety G := f.comp U0.inclusion
  let U : ClosedSubgroup G := g.imageClosedSubgroup
  have hcontains (V : ClosedSubgroup G) (hVR : V ≤ R)
      (hVunipotent : IsUnipotentAlgebraicGroup V.carrierVariety) : V ≤ U := by
    intro x hx
    have hxR : x ∈ R.toSubgroup := hVR hx
    have hxVunipotent : IsUnipotentElement V.carrierVariety
        (V.pointEquiv.symm ⟨x, hx⟩) := hVunipotent _
    have hxGunipotent : IsUnipotentElement G x :=
      (closedSubgroup_unipotentElement_iff V hx).mpr hxVunipotent
    let xR : Variety.Point R.carrierVariety :=
      R.pointEquiv.symm ⟨x, hxR⟩
    have hxRunipotent : IsUnipotentElement R.carrierVariety xR :=
      (closedSubgroup_unipotentElement_iff R hxR).mp hxGunipotent
    have hxU0 : xR ∈ U0.toSubgroup := (hU0 xR).mpr hxRunipotent
    let xU0 : Variety.Point U0.carrierVariety :=
      U0.pointEquiv.symm ⟨xR, hxU0⟩
    change x ∈ g.image
    refine ⟨xU0, ?_⟩
    change R.inclusion.onPoints (U0.inclusion.onPoints xU0) = x
    have hxU0val : U0.inclusion.onPoints xU0 = xR := by
      change (U0.pointEquiv xU0).val = xR
      simp [xU0]
    have hxRval : R.inclusion.onPoints xR = x := by
      change (R.pointEquiv xR).val = x
      simp [xR]
    rw [hxU0val, hxRval]
  refine ⟨U, ?_, ?_, hcontains⟩
  dsimp [U, IsUnipotentRadicalOf]
  constructor
  · intro x hx
    change x ∈ R.toSubgroup
    change x ∈ g.image at hx
    rcases hx with ⟨u, rfl⟩
    change R.inclusion.onPoints (U0.inclusion.onPoints u) ∈ R.toSubgroup
    exact (R.pointEquiv (U0.inclusion.onPoints u)).property
  · constructor
    · have hU0unipotent : IsUnipotentAlgebraicGroup U0.carrierVariety :=
        hU0.isUnipotent_of_solvable_connected hRsolvable hRcarrierConnected
      obtain ⟨π, hπsurjective, -, _⟩ := g.closedImageProjection_exists
      exact hU0unipotent.of_surjective π hπsurjective
    · constructor
      · intro b hb u hu
        change b * u * b⁻¹ ∈ g.image
        rcases hu with ⟨u0, rfl⟩
        let bR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨b, hb⟩
        let uR : Variety.Point R.carrierVariety := U0.inclusion.onPoints u0
        have huR : uR ∈ U0.toSubgroup := (U0.pointEquiv u0).property
        have hconjR : bR * uR * bR⁻¹ ∈ U0.toSubgroup :=
          hU0normal.conj_mem uR huR bR
        let v0 : Variety.Point U0.carrierVariety :=
          U0.pointEquiv.symm ⟨bR * uR * bR⁻¹, hconjR⟩
        refine ⟨v0, ?_⟩
        change R.inclusion.onPoints (U0.inclusion.onPoints v0) =
          b * R.inclusion.onPoints (U0.inclusion.onPoints u0) * b⁻¹
        have hv0 : U0.inclusion.onPoints v0 = bR * uR * bR⁻¹ := by
          change (U0.pointEquiv v0).val = _
          simp [v0]
        rw [hv0]
        have hbR : R.inclusion.onPoints bR = b := by
          change (R.pointEquiv bR).val = b
          simp [bR]
        simp only [map_mul, map_inv, hbR]
        rfl
      · intro V hVR hVunipotent _hVnormal
        exact hcontains V hVR hVunipotent
  change _root_.IsConnected (g.imageClosedSubgroup : Set (Variety.Point G))
  exact g.imageClosedSubgroup_isConnected
    (hU0.isConnected_of_solvable_connected hRsolvable hRcarrierConnected)

/-- Every connected solvable closed subgroup has a connected unipotent
radical in the ambient algebraic group. -/
public theorem exists_unipotentRadical_of_connected_solvable
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    (R : ClosedSubgroup G)
    (hconnected : _root_.IsConnected (R : Set (Variety.Point G)))
    (hsolvable : Group.IsSolvable (Variety.Point R.carrierVariety)) :
    ∃ U : ClosedSubgroup G,
      IsUnipotentRadicalOf R U ∧
      _root_.IsConnected (U : Set (Variety.Point G)) := by
  obtain ⟨U, hU, hUconnected, _⟩ :=
    exists_unipotent_radical_core R hconnected hsolvable
  exact ⟨U, hU, hUconnected⟩

/-- A radical subgroup has a unipotent radical. -/
public theorem exists_unipotent_radical
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    (R : ClosedSubgroup G) (hR : IsRadicalSubgroup R) :
    ∃ U : ClosedSubgroup G, IsUnipotentRadicalOf R U := by
  obtain ⟨U, hU, _, _⟩ :=
    exists_unipotent_radical_core R hR.connected hR.solvable
  exact ⟨U, hU⟩

/-- Unipotent radicals of a closed subgroup are unique. -/
public lemma unipotent_radical_unique
    {G : Variety k} [AlgebraicGroup G]
    {R U V : ClosedSubgroup G}
    (hU : IsUnipotentRadicalOf R U)
    (hV : IsUnipotentRadicalOf R V) :
    U = V := by
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (hV.2.2.2 U hU.1 hU.2.1 hU.2.2.1)
    (hU.2.2.2 V hV.1 hV.2.1 hV.2.2.1)

/-- In a connected solvable closed subgroup, its unipotent radical contains
every closed unipotent subgroup, without a normality assumption on that
subgroup. -/
public lemma IsUnipotentRadicalOf.contains_unipotent_closedSubgroup
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    {R U V : ClosedSubgroup G}
    (hU : IsUnipotentRadicalOf R U)
    (hconnected : _root_.IsConnected (R : Set (Variety.Point G)))
    (hsolvable : Group.IsSolvable (Variety.Point R.carrierVariety))
    (hVR : V ≤ R)
    (hVunipotent : IsUnipotentAlgebraicGroup V.carrierVariety) : V ≤ U := by
  obtain ⟨W, hW, _, hcontains⟩ :=
    exists_unipotent_radical_core R hconnected hsolvable
  rw [unipotent_radical_unique hW hU] at hcontains
  exact hcontains V hVR hVunipotent

/-! ### Ambient existence assembly

The construction of a unipotent radical is naturally two-stage: first take
the connected solvable radical of the ambient group, then take its
unipotent radical.  This wrapper exposes that composition without requiring
the caller to provide the radical as an additional datum.
-/

/-- Every algebraic group admits a radical together with its unipotent
radical.  The second subgroup is maximal among closed unipotent subgroups
normalised by the first one. -/
public theorem exists_radical_with_unipotent_radical
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k] :
    ∃ R U : ClosedSubgroup G,
      IsRadicalSubgroup R ∧ IsUnipotentRadicalOf R U := by
  obtain ⟨R, hR⟩ := exists_radical G
  obtain ⟨U, hU, _, _⟩ :=
    exists_unipotent_radical_core R hR.connected hR.solvable
  exact ⟨R, U, hR, hU⟩

private lemma unipotentElement_of_algebraicGroupIso
    {A B : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    (e : AlgebraicGroup.Iso A B) {x : Variety.Point A}
    (hx : IsUnipotentElement A x) :
    IsUnipotentElement B (e.hom.onPoints x) := by
  let Aop : Module.End k (Variety.PolynomialFunction A) :=
    rightTranslationPullback A x - 1
  let Bop : Module.End k (Variety.PolynomialFunction B) :=
    rightTranslationPullback B (e.hom.onPoints x) - 1
  let L : Variety.PolynomialFunction B →ₗ[k] Variety.PolynomialFunction A :=
    e.hom.toVariety.pullbackAlgHom.toLinearMap
  let M : Variety.PolynomialFunction A →ₗ[k] Variety.PolynomialFunction B :=
    e.inv.toVariety.pullbackAlgHom.toLinearMap
  have hML : ∀ f, M (L f) = f := by
    intro f
    apply Variety.PolynomialFunction.ext
    intro y
    change f (e.hom.onPoints (e.inv.onPoints y)) = f y
    rw [e.inv_hom_id]
  have hinter : ∀ f, M (Aop f) = Bop (M f) := by
    intro f
    apply Variety.PolynomialFunction.ext
    intro y
    change f (e.inv.onPoints y * x) - f (e.inv.onPoints y) =
      f (e.inv.onPoints (y * e.hom.onPoints x)) - f (e.inv.onPoints y)
    rw [← e.hom_inv_id x, ← e.inv.onPoints.map_mul, e.inv_hom_id]
  have hiter : ∀ n f, M ((Aop : Variety.PolynomialFunction A →
      Variety.PolynomialFunction A)^[n] f) =
      (Bop : Variety.PolynomialFunction B →
        Variety.PolynomialFunction B)^[n] (M f) := by
    intro n
    induction n with
    | zero => intro f; rfl
    | succ n ih =>
        intro f
        rw [Function.iterate_succ_apply, ih, hinter]
        rw [← Function.iterate_succ_apply]
  intro f
  obtain ⟨n, hn⟩ := hx (L f)
  refine ⟨n, ?_⟩
  have h := hiter n (L f)
  rw [hML f, hn, map_zero] at h
  simpa [Aop, Bop, Module.End.pow_apply] using h.symm

private lemma conjugate_unipotent_radicalOf
    {G : Variety k} [AlgebraicGroup G]
    {R U : ClosedSubgroup G}
    (hRnormal : R.toSubgroup.Normal)
    (hU : IsUnipotentRadicalOf R U)
    (g : Variety.Point G) :
    IsUnipotentRadicalOf R (U.conjugate g) := by
  have hconj_le : U.conjugate g ≤ R := by
    intro x hx
    change x ∈ R.toSubgroup
    have hxU : g⁻¹ * x * g ∈ U.toSubgroup :=
      (U.mem_conjugate_iff g x).mp hx
    have hxR := hU.1 hxU
    have hxR' := hRnormal.conj_mem (g⁻¹ * x * g) hxR g
    simpa [mul_assoc] using hxR'
  have hconj_unipotent :
      IsUnipotentAlgebraicGroup (U.conjugate g).carrierVariety := by
    intro z
    let y : Variety.Point U.carrierVariety :=
      (U.conjugateIso g).inv.onPoints z
    have hy := hU.2.1 y
    have hz := unipotentElement_of_algebraicGroupIso
      (U.conjugateIso g) hy
    rw [show (U.conjugateIso g).hom.onPoints y = z by
      exact (U.conjugateIso g).inv_hom_id z] at hz
    exact hz
  have hconj_normalizes : ∀ b, b ∈ R → ∀ z, z ∈ U.conjugate g →
      b * z * b⁻¹ ∈ U.conjugate g := by
    intro b hb z hz
    change (MulAut.conj g⁻¹) (b * z * b⁻¹) ∈ U.toClosedSubgroup.toSubgroup
    have hzU : g⁻¹ * z * g ∈ U.toSubgroup :=
      (U.mem_conjugate_iff g z).mp hz
    have hbgR : g⁻¹ * b * g ∈ R.toSubgroup := by
      have h := hRnormal.conj_mem b hb g⁻¹
      simpa [mul_assoc] using h
    have h := hU.2.2.1 (g⁻¹ * b * g) hbgR
      (g⁻¹ * z * g) hzU
    have hmem :
        (g⁻¹ * b * g) * (g⁻¹ * z * g) * (g⁻¹ * b * g)⁻¹ ∈
          U.toClosedSubgroup.toSubgroup := h
    simpa [MulAut.conj_apply, mul_assoc] using hmem
  have hconj_maximal : ∀ V : ClosedSubgroup G, V ≤ R →
      IsUnipotentAlgebraicGroup V.carrierVariety →
      (∀ b, b ∈ R → ∀ v, v ∈ V → b * v * b⁻¹ ∈ V) →
      V ≤ U.conjugate g := by
    intro V hVR hVunipotent hVnormal
    have hVconj_le : V.conjugate g⁻¹ ≤ R := by
      intro x hx
      change x ∈ R.toSubgroup
      have hxV : (g⁻¹)⁻¹ * x * g⁻¹ ∈ V.toSubgroup :=
        (V.mem_conjugate_iff g⁻¹ x).mp hx
      have hxR := hVR hxV
      have hxR' := hRnormal.conj_mem ((g⁻¹)⁻¹ * x * g⁻¹) hxR g⁻¹
      simpa [mul_assoc] using hxR'
    have hVconj_unipotent :
        IsUnipotentAlgebraicGroup (V.conjugate g⁻¹).carrierVariety := by
      intro z
      let y : Variety.Point V.carrierVariety :=
        (V.conjugateIso g⁻¹).inv.onPoints z
      have hy := hVunipotent y
      have hz := unipotentElement_of_algebraicGroupIso
        (V.conjugateIso g⁻¹) hy
      rw [show (V.conjugateIso g⁻¹).hom.onPoints y = z by
        exact (V.conjugateIso g⁻¹).inv_hom_id z] at hz
      exact hz
    have hVconj_normalizes : ∀ b, b ∈ R → ∀ z, z ∈ V.conjugate g⁻¹ →
        b * z * b⁻¹ ∈ V.conjugate g⁻¹ := by
      intro b hb z hz
      change (MulAut.conj (g⁻¹)⁻¹) (b * z * b⁻¹) ∈ V.toClosedSubgroup.toSubgroup
      have hzV : (g⁻¹)⁻¹ * z * g⁻¹ ∈ V.toSubgroup :=
        (V.mem_conjugate_iff g⁻¹ z).mp hz
      have hbgR : (g⁻¹)⁻¹ * b * g⁻¹ ∈ R.toSubgroup := by
        have h := hRnormal.conj_mem b hb (g⁻¹)⁻¹
        simpa [mul_assoc] using h
      have h := hVnormal ((g⁻¹)⁻¹ * b * g⁻¹) hbgR
        ((g⁻¹)⁻¹ * z * g⁻¹) hzV
      have hmem :
          ((g⁻¹)⁻¹ * b * g⁻¹) * ((g⁻¹)⁻¹ * z * g⁻¹) *
              ((g⁻¹)⁻¹ * b * g⁻¹)⁻¹ ∈ V.toClosedSubgroup.toSubgroup := h
      simpa [MulAut.conj_apply, mul_assoc] using hmem
    have hle := hU.2.2.2 (V.conjugate g⁻¹)
      hVconj_le hVconj_unipotent hVconj_normalizes
    intro x hx
    change (MulAut.conj g⁻¹) x ∈ U
    have hx' : g⁻¹ * x * g ∈ V.conjugate g⁻¹ := by
      apply (V.mem_conjugate_iff g⁻¹ _).mpr
      simpa [mul_assoc] using
        (show x ∈ V.toClosedSubgroup.toSubgroup from hx)
    apply hle
    change (MulAut.conj g⁻¹) x ∈ (V.conjugate g⁻¹).toClosedSubgroup.toSubgroup
    change x ∈ V.toClosedSubgroup.toSubgroup at hx
    change (MulAut.conj (g⁻¹)⁻¹) ((MulAut.conj g⁻¹) x) ∈
      V.toClosedSubgroup.toSubgroup
    simpa [MulAut.conj_apply, mul_assoc] using hx
  exact ⟨hconj_le, hconj_unipotent, hconj_normalizes, hconj_maximal⟩

/-- The unipotent radical of a radical subgroup is normal in the ambient
algebraic group.  Conjugation preserves the defining radical property, and
uniqueness then gives ambient characteristicity. -/
public theorem IsUnipotentRadicalOf.normal_of_radical
    {G : Variety k} [AlgebraicGroup G]
    {R U : ClosedSubgroup G}
    (hR : IsRadicalSubgroup R)
    (hU : IsUnipotentRadicalOf R U) :
    U.toSubgroup.Normal := by
  constructor
  intro x hx g
  have hconj := conjugate_unipotent_radicalOf hR.normal hU g
  have hx' : g * x * g⁻¹ ∈ U.conjugate g := by
    change (MulAut.conj g⁻¹) (g * x * g⁻¹) ∈ U.toClosedSubgroup.toSubgroup
    simpa [mul_assoc] using hx
  have heq : U.conjugate g = U :=
    unipotent_radical_unique hconj hU
  rw [heq] at hx'
  exact hx'

/-! ### Ambient unipotent radical -/

/-- The largest closed connected unipotent normal subgroup of an algebraic
group.  It is obtained by taking the unipotent radical of the connected
solvable radical, and the maximality clause is ambient. -/
public theorem exists_ambient_unipotent_radical
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k] :
    ∃ U : ClosedSubgroup G,
      U.toSubgroup.Normal ∧
      _root_.IsConnected (U : Set (Variety.Point G)) ∧
      IsUnipotentAlgebraicGroup U.carrierVariety ∧
      ∀ V : ClosedSubgroup G, V.toSubgroup.Normal →
        _root_.IsConnected (V : Set (Variety.Point G)) →
        IsUnipotentAlgebraicGroup V.carrierVariety → V ≤ U := by
  obtain ⟨R, hR⟩ := exists_radical G
  obtain ⟨U, hU, hUconnected, _⟩ :=
    exists_unipotent_radical_core R hR.connected hR.solvable
  have hUnormal : U.toSubgroup.Normal :=
    hU.normal_of_radical hR
  refine ⟨U, hUnormal, hUconnected, hU.2.1, ?_⟩
  intro V hVnormal hVconnected hVunipotent
  have hVR : V ≤ R := by
    apply hR.maximal V hVnormal hVconnected
    exact isSolvable_of_isUnipotentAlgebraicGroup hVunipotent
  apply hU.2.2.2 V hVR hVunipotent
  intro b hb v hv
  have h := hVnormal.conj_mem v hv b
  change b * v * b⁻¹ ∈ V.toClosedSubgroup.toSubgroup
  exact h

private noncomputable def topClosedSubgroupIso_for_radical
    (K : Variety k) [AlgebraicGroup K] [IsAlgClosed k] :
    AlgebraicGroup.Iso K (ClosedSubgroup.top (G := K)).carrierVariety := by
  let T : ClosedSubgroup K := ClosedSubgroup.top
  let toTop : AlgebraicGroup.Morphism K T.carrierVariety :=
    (AlgebraicGroup.Morphism.id K).codRestrictClosedSubgroup T (fun _ => trivial)
  exact {
    hom := toTop
    inv := T.inclusion
    hom_inv_id := by intro x; rfl
    inv_hom_id := by
      intro y
      apply T.inclusion_injective
      dsimp [toTop]
      rfl }

public lemma closedSubgroup_top_isTorus
    (K : Variety k) [AlgebraicGroup K] [IsAlgClosed k] (hK : IsTorus K) :
    IsTorus (ClosedSubgroup.top (G := K)).carrierVariety := by
  obtain ⟨n, ⟨e⟩⟩ := hK
  exact ⟨n, ⟨(topClosedSubgroupIso_for_radical K).comp e⟩⟩

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_5_1_d
    {K : Variety k} [AlgebraicGroup K] (hK : Variety.IsConnected K)
    (hSolv : Group.IsSolvable (Variety.Point K)) :
    ∃ U : ClosedSubgroup K, IsUnipotentRadicalSubgroup U ∧
      ∀ T : ClosedSubgroup K, IsMaximalTorus T →
        (∀ x : Variety.Point K, ∃ t u, t ∈ T.toSubgroup ∧
          u ∈ U.toSubgroup ∧ x = t * u) ∧
        T.toSubgroup ⊓ U.toSubgroup = ⊥ := by
  obtain ⟨n, hn, H, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hSolv hK
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation K :=
    { n := n, positive := hn, subgroup := H, iso := e }
  let U : ClosedSubgroup K := P.unipotentRadical
  have hU : IsUnipotentRadicalSubgroup U := by
    dsimp [U]
    exact P.mem_unipotentRadical_iff_characteristicFree
  refine ⟨U, hU, ?_⟩
  intro T hT
  letI : AlgebraicGroup P.diagonalImage.carrierVariety :=
    P.diagonalImage.carrierAlgebraicGroup
  have hItorus : IsTorus P.diagonalImage.carrierVariety := by
    exact P.diagonalImage_isTorus hK
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
    theorem_1_4_3_d P.diagonalImageMorphism hdiagSurj T hT
  have hStop :
      (P.diagonalImageMorphism.comp T.inclusion).imageClosedSubgroup =
        ClosedSubgroup.top := by
    symm
    apply hTimage.2
    · exact closedSubgroup_top_isTorus
        P.diagonalImage.carrierVariety hItorus
    · rw [ClosedSubgroup.le_iff_le_toSubgroup]
      exact le_top
  have hπTsurj : ∀ y : Variety.Point P.diagonalImage.carrierVariety,
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
    change P.diagonalImageMorphism.onPoints (T.inclusion.onPoints t) = y at ht
    exact ⟨t, ht⟩
  constructor
  · intro x
    obtain ⟨tT, htT⟩ := hπTsurj
      (P.diagonalImageMorphism.onPoints x)
    let t : Variety.Point K := T.inclusion.onPoints tT
    let u : Variety.Point K := t⁻¹ * x
    have ht : t ∈ T.toSubgroup := by
      change (T.pointEquiv tT).val ∈ T.toSubgroup
      exact (T.pointEquiv tT).property
    have htx : P.diagonalImageMorphism.onPoints t =
        P.diagonalImageMorphism.onPoints x := by
      simpa [t] using htT
    have hπu : P.diagonalImageMorphism.onPoints u = 1 := by
      change P.diagonalImageMorphism.onPoints (t⁻¹ * x) = 1
      rw [map_mul, map_inv, htx]
      simp
    have hdiag : P.diagonalMorphism.onPoints u = 1 := by
      rw [← hinc u, hπu]
      exact P.diagonalImage.inclusion.map_one
    have hu : u ∈ U.toSubgroup := by
      change u ∈ P.unipotentRadical
      exact P.mem_unipotentRadical_iff_diagonal u |>.mpr hdiag
    refine ⟨t, u, ht, hu, ?_⟩
    dsimp [u]
    group
  · have hUunipotent : IsUnipotentAlgebraicGroup U.carrierVariety :=
      hU.isUnipotent_of_solvable_connected hSolv hK
    exact subtorus_inf_unipotent_eq_bot T U hT.1 hUunipotent

end

end Theory.AlgebraicGroup
