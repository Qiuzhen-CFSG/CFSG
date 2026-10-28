module

public import Theory.AlgebraicGroup.Unipotent.Basic

universe u

/-! Normalizer dimension growth in unipotent algebraic groups.  The strict
dimension-growth result is the GLS 1.3.2(d) input; the final theorem packages
the Bor1 12.1 nilpotent-normalizer step: in a connected unipotent group, a
closed subgroup whose codimension is at most one has full normalizer.  The
ambient-subgroup wrapper transports the statement through an injective closed
subgroup inclusion, which is the form used by Bor1 13.16. -/

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

/-- GLS3 Proposition 1.3.2(d): a closed subgroup of smaller dimension in a
unipotent algebraic group has a normalizer of strictly larger dimension. -/
public theorem IsUnipotentAlgebraicGroup.normalizer_dimension_gt
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) (H : ClosedSubgroup G)
    (hdim : Variety.dimension H.carrierVariety < Variety.dimension G) :
    Variety.dimension H.carrierVariety <
      Variety.dimension H.normalizer.carrierVariety := by
  have hnil : Group.IsNilpotent (Variety.Point G) :=
    unipotentGroup_isNilpotent hG
  let I : ClosedSubgroup G := AlgebraicGroup.identityComponentClosedSubgroup G
  let S : Subgroup (Variety.Point G) := I.toSubgroup
  have hSconn : _root_.IsConnected (S : Set (Variety.Point G)) := by
    change _root_.IsConnected (AlgebraicGroup.identityComponent G)
    exact AlgebraicGroup.identityComponent_isConnected G
  have hSnotle : ¬ S ≤ H.toSubgroup := by
    intro hle
    have hdimle : Variety.dimension I.carrierVariety ≤
        Variety.dimension H.carrierVariety :=
      connected_closedSubgroup_dimension_le_of_le I H hSconn hle
    rw [AlgebraicGroup.dimension_identityComponentClosedSubgroup G] at hdimle
    exact (not_le_of_gt hdim) hdimle
  have hleL : ∀ n, relativeLowerCentralSeries G S n ≤
      Subgroup.lowerCentralSeries (⊤ : Subgroup (Variety.Point G)) n :=
    relativeLowerCentralSeries_le_lowerCentralSeries S
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  have hterminal : relativeLowerCentralSeries G S n ≤ H.toSubgroup := by
    have hle := hleL n
    rw [hn] at hle
    exact hle.trans bot_le
  classical
  let hex : ∃ m, relativeLowerCentralSeries G S m ≤ H.toSubgroup :=
    ⟨n, hterminal⟩
  let m := Nat.find hex
  have hm : relativeLowerCentralSeries G S m ≤ H.toSubgroup :=
    Nat.find_spec hex
  have hp0 : ¬ relativeLowerCentralSeries G S 0 ≤ H.toSubgroup := by
    simpa [relativeLowerCentralSeries] using hSnotle
  have hmpos : 0 < m := (Nat.find_pos hex).2 hp0
  let j := m - 1
  have hjm : j < m := by
    dsimp [j]
    omega
  have hjone : j + 1 = m := by
    dsimp [j]
    omega
  have hjnotle : ¬ relativeLowerCentralSeries G S j ≤ H.toSubgroup :=
    Nat.find_min hex hjm
  have hnextle : relativeLowerCentralSeries G S (j + 1) ≤ H.toSubgroup := by
    rw [hjone]
    exact hm
  let C : ClosedSubgroup G := subgroupZariskiClosure G
    (relativeLowerCentralSeries G S j)
  have hCconn : _root_.IsConnected (C : Set (Variety.Point G)) :=
    relativeLowerCentralSeries_closure_connected S hSconn j
  have hrawC : relativeLowerCentralSeries G S j ≤ C.toSubgroup := by
    intro x hx
    exact subset_closure hx
  have hCnotle : ¬ C ≤ H := by
    intro hCH
    exact hjnotle (hrawC.trans hCH)
  have hrawNormalizer : relativeLowerCentralSeries G S j ≤
      Subgroup.normalizer (H.toSubgroup : Set (Variety.Point G)) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    have hcomm : ⁅relativeLowerCentralSeries G S j, H.toSubgroup⁆ ≤
        ⁅relativeLowerCentralSeries G S j,
          (⊤ : Subgroup (Variety.Point G))⁆ :=
      Subgroup.commutator_mono le_rfl le_top
    exact hcomm.trans (by
      simpa [relativeLowerCentralSeries] using hnextle)
  have hCnormalizer : C ≤ H.normalizer := by
    intro x hx
    change x ∈ closure
      (relativeLowerCentralSeries G S j : Set (Variety.Point G)) at hx
    exact closure_minimal hrawNormalizer
      (Variety.isClosed_iff_isZariskiClosed.mpr H.normalizer.isZariskiClosed) hx
  have hCnormalizer0 : C ≤ H.normalizer.identityComponentAmbient :=
    connected_closedSubgroup_le_identityComponentAmbient
      C H.normalizer hCconn hCnormalizer
  have hHnormalizer : H ≤ H.normalizer := by
    intro x hx
    exact Subgroup.le_normalizer hx
  have hH0normalizer : H.identityComponentAmbient ≤ H.normalizer := by
    intro x hx
    exact hHnormalizer (H.identityComponentAmbient_le hx)
  have hH0normalizer0 : H.identityComponentAmbient ≤
      H.normalizer.identityComponentAmbient :=
    connected_closedSubgroup_le_identityComponentAmbient
      H.identityComponentAmbient H.normalizer
      H.identityComponentAmbient_isConnected hH0normalizer
  have hne : H.identityComponentAmbient ≠
      H.normalizer.identityComponentAmbient := by
    intro heq
    apply hCnotle
    intro x hx
    apply H.identityComponentAmbient_le
    rw [heq]
    exact hCnormalizer0 hx
  have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne
    H.identityComponentAmbient H.normalizer.identityComponentAmbient
    hH0normalizer0 hne H.identityComponentAmbient_isConnected
    H.normalizer.identityComponentAmbient_isConnected
  rw [ClosedSubgroup.dimension_identityComponentAmbient,
    ClosedSubgroup.dimension_identityComponentAmbient] at hlt
  exact hlt

/-- Bor1 Chapter IV, 12.1 Lemma: in a connected unipotent group, a closed
subgroup of codimension at most one is normalized by the whole group. -/
public theorem IsUnipotentAlgebraicGroup.normalizer_eq_top_of_dimension_le_add_one
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) (hGconn : Variety.IsConnected G)
    (I : ClosedSubgroup G)
    (hdim : Variety.dimension G ≤ Variety.dimension I.carrierVariety + 1) :
    I.normalizer = ClosedSubgroup.top := by
  have hIdimle : Variety.dimension I.carrierVariety ≤ Variety.dimension G := by
    have htopDim : Variety.dimension (ClosedSubgroup.top : ClosedSubgroup G).carrierVariety =
        Variety.dimension G :=
      (closedSubgroup_dimension_eq_iff_contains_identityComponent G
        (ClosedSubgroup.top : ClosedSubgroup G)).2 (by
          intro x _
          trivial)
    rw [← ClosedSubgroup.dimension_identityComponentAmbient I]
    simpa [htopDim] using (connected_closedSubgroup_dimension_le_of_le
      I.identityComponentAmbient ClosedSubgroup.top
      I.identityComponentAmbient_isConnected (fun _ _ ↦ trivial))
  by_cases hIdim : Variety.dimension I.carrierVariety = Variety.dimension G
  · have hG0I : AlgebraicGroup.identityComponent G ⊆
        (I.toSubgroup : Set (Variety.Point G)) :=
      (closedSubgroup_dimension_eq_iff_contains_identityComponent G I).1 hIdim
    have hG0 : AlgebraicGroup.identityComponent G = Set.univ :=
      (identityComponent_eq_univ_iff_isConnected G).2 hGconn
    have hItop : I = ClosedSubgroup.top := by
      apply SetLike.coe_injective
      apply Set.Subset.antisymm (fun _ _ ↦ trivial)
      intro x _
      apply hG0I
      rw [hG0]
      trivial
    rw [hItop]
    apply SetLike.coe_injective
    change Subgroup.normalizer ((⊤ : Subgroup (Variety.Point G)) :
      Set (Variety.Point G)) = (⊤ : Set (Variety.Point G))
    exact congrArg (fun S : Subgroup (Variety.Point G) =>
        (S : Set (Variety.Point G)))
      ((Subgroup.normalizer_eq_top_iff
        (H := (⊤ : Subgroup (Variety.Point G)))).2 Subgroup.normal_top)
  · have hIlt : Variety.dimension I.carrierVariety < Variety.dimension G :=
      lt_of_le_of_ne hIdimle hIdim
    have hnormalizerGt : Variety.dimension I.carrierVariety <
        Variety.dimension I.normalizer.carrierVariety :=
      hG.normalizer_dimension_gt I hIlt
    have hGdimle : Variety.dimension G ≤
        Variety.dimension I.normalizer.carrierVariety :=
      hdim.trans (Cardinal.add_one_le_of_lt hnormalizerGt)
    have hnormalizerDimLe : Variety.dimension I.normalizer.carrierVariety ≤
        Variety.dimension G := by
      have htopDim : Variety.dimension (ClosedSubgroup.top : ClosedSubgroup G).carrierVariety =
          Variety.dimension G :=
        (closedSubgroup_dimension_eq_iff_contains_identityComponent G
          (ClosedSubgroup.top : ClosedSubgroup G)).2 (by
            intro x _
            trivial)
      rw [← ClosedSubgroup.dimension_identityComponentAmbient I.normalizer]
      simpa [htopDim] using (connected_closedSubgroup_dimension_le_of_le
        I.normalizer.identityComponentAmbient ClosedSubgroup.top
        I.normalizer.identityComponentAmbient_isConnected (fun _ _ ↦ trivial))
    have hnormalizerDim : Variety.dimension I.normalizer.carrierVariety =
        Variety.dimension G :=
      le_antisymm hnormalizerDimLe hGdimle
    have hG0normalizer : AlgebraicGroup.identityComponent G ⊆
        (I.normalizer.toSubgroup : Set (Variety.Point G)) :=
      (closedSubgroup_dimension_eq_iff_contains_identityComponent
        G I.normalizer).1 hnormalizerDim
    have hG0 : AlgebraicGroup.identityComponent G = Set.univ :=
      (identityComponent_eq_univ_iff_isConnected G).2 hGconn
    apply SetLike.coe_injective
    apply Set.Subset.antisymm (fun _ _ ↦ trivial)
    intro x _
    apply hG0normalizer
    rw [hG0]
    trivial

/-- Bor1 12.1 in ambient-subgroup form: if `H` is connected and unipotent,
`I` is a closed subgroup of `H`, and the codimension of `I` in `H` is at most
one, then every element of `H` normalizes `I`. -/
public theorem IsUnipotentAlgebraicGroup.le_normalizer_of_le_of_dimension_le_add_one
    {G : Variety k} [AlgebraicGroup G]
    (H I : ClosedSubgroup G)
    (hH : IsUnipotentAlgebraicGroup H.carrierVariety)
    (hHconn : _root_.IsConnected (H : Set (Variety.Point G)))
    (hIH : I ≤ H)
    (hdim : Variety.dimension H.carrierVariety ≤
      Variety.dimension I.carrierVariety + 1) :
    H ≤ I.normalizer := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  have hHvar : Variety.IsConnected H.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
    letI : ConnectedSpace
        {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
      Subtype.connectedSpace hHconn
    letI : ConnectedSpace (Variety.Point H.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  let P : ClosedSubgroup H.carrierVariety :=
    H.inclusion.closedSubgroupPreimage I
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let j : AlgebraicGroup.Morphism P.carrierVariety G :=
    H.inclusion.comp P.inclusion
  have hjimage : j.imageClosedSubgroup = I := by
    apply SetLike.coe_injective
    ext x
    change x ∈ j.image ↔ x ∈ I.toSubgroup
    constructor
    · rintro ⟨z, rfl⟩
      exact (P.pointEquiv z).property
    · intro hx
      have hxH : x ∈ H.toSubgroup := hIH hx
      let y : Variety.Point H.carrierVariety :=
        H.pointEquiv.symm ⟨x, hxH⟩
      have hyval : H.inclusion.onPoints y = x := by
        change (H.pointEquiv y).val = x
        rw [H.pointEquiv.apply_symm_apply]
      have hyP : y ∈ P.toSubgroup := by
        change H.inclusion.onPoints y ∈ I.toSubgroup
        rw [hyval]
        exact hx
      let z : Variety.Point P.carrierVariety :=
        P.pointEquiv.symm ⟨y, hyP⟩
      refine ⟨z, ?_⟩
      change H.inclusion.onPoints (P.inclusion.onPoints z) = x
      have hzval : P.inclusion.onPoints z = y := by
        change (P.pointEquiv z).val = y
        rw [P.pointEquiv.apply_symm_apply]
      rw [hzval, hyval]
  have hjinj : Function.Injective j.onPoints :=
    H.inclusion_injective.comp P.inclusion_injective
  letI : Subsingleton j.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hjinj
    rw [x.property, y.property]
  letI : Subsingleton
      (Variety.Point j.kernelClosedSubgroup.carrierVariety) :=
    j.kernelClosedSubgroup.pointEquiv.subsingleton
  letI : Finite (Variety.Point j.kernelClosedSubgroup.carrierVariety) :=
    Finite.of_subsingleton
  have hkerDim : Variety.dimension j.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points j.kernelClosedSubgroup.carrierVariety).2
      inferInstance
  have hjdim := morphism_dimension_eq_kernel_add_image j
  rw [hkerDim, zero_add, hjimage] at hjdim
  have hPdim : Variety.dimension P.carrierVariety =
      Variety.dimension I.carrierVariety := hjdim
  have hPnormalizer : P.normalizer = ClosedSubgroup.top :=
    hH.normalizer_eq_top_of_dimension_le_add_one hHvar P (by
      rw [hPdim]
      exact hdim)
  have hconjugatesInto : ∀ (a : Variety.Point H.carrierVariety),
      a ∈ P.normalizer.toSubgroup → ∀ z : Variety.Point G,
        z ∈ I.toSubgroup →
          H.inclusion.onPoints a * z * (H.inclusion.onPoints a)⁻¹ ∈
            I.toSubgroup := by
    intro a ha z hz
    have hzImage : z ∈ j.imageClosedSubgroup.toSubgroup := by
      rw [hjimage]
      exact hz
    change z ∈ j.image at hzImage
    obtain ⟨p, hp⟩ := hzImage
    have hpP : P.inclusion.onPoints p ∈ P.toSubgroup :=
      (P.pointEquiv p).property
    have hconjP :=
      (Subgroup.mem_normalizer_iff.mp ha (P.inclusion.onPoints p)).mp hpP
    change H.inclusion.onPoints
      (a * P.inclusion.onPoints p * a⁻¹) ∈ I.toSubgroup at hconjP
    have hp' : H.inclusion.onPoints (P.inclusion.onPoints p) = z := hp
    simpa [map_mul, map_inv, hp'] using hconjP
  intro x hx
  let y : Variety.Point H.carrierVariety :=
    H.pointEquiv.symm ⟨x, hx⟩
  have hy : H.inclusion.onPoints y = x := by
    change (H.pointEquiv y).val = x
    rw [H.pointEquiv.apply_symm_apply]
  have hyNormalizer : y ∈ P.normalizer.toSubgroup := by
    rw [hPnormalizer]
    trivial
  change x ∈ Subgroup.normalizer
    (I.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    simpa [hy] using hconjugatesInto y hyNormalizer z hz
  · intro hz
    have hyInvNormalizer : y⁻¹ ∈ P.normalizer.toSubgroup :=
      P.normalizer.toSubgroup.inv_mem hyNormalizer
    have hback := hconjugatesInto y⁻¹ hyInvNormalizer
      (x * z * x⁻¹) hz
    simpa [hy, mul_assoc] using hback

end Theory.AlgebraicGroup
