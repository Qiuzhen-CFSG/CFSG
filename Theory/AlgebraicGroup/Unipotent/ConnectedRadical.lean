module

public import Theory.AlgebraicGroup.Unipotent.Radical
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Reductive.Defs

/-!
Connected unipotent radicals viewed inside an ambient algebraic group.
The defining maximality is restricted to connected subgroups. Existence is
transported from the intrinsic radical; uniqueness makes it characteristic
under ambient conjugation. Source: GLS3, §§1.5, 1.7 and 3.1.
-/

universe u
set_option linter.style.haveILetI false
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The largest connected closed unipotent subgroup normal in `H`, viewed
inside the original ambient algebraic group. -/
@[expose] public def IsConnectedUnipotentRadicalOf
    {G : Variety k} [AlgebraicGroup G] (H U : ClosedSubgroup G) : Prop :=
  U ≤ H ∧ _root_.IsConnected (U : Set (Variety.Point G)) ∧
    IsUnipotentAlgebraicGroup U.carrierVariety ∧ H ≤ U.normalizer ∧
    ∀ V : ClosedSubgroup G, V ≤ H →
      _root_.IsConnected (V : Set (Variety.Point G)) →
      IsUnipotentAlgebraicGroup V.carrierVariety → H ≤ V.normalizer → V ≤ U

omit [IsAlgClosed k] in
private lemma connectedRadical_carrier_connected
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hU : _root_.IsConnected (U : Set (Variety.Point G))) :
    Variety.IsConnected U.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph U.isZariskiClosed
  letI : ConnectedSpace {x : Variety.Point G // x ∈ (U : Set (Variety.Point G))} :=
    Subtype.connectedSpace hU
  letI : ConnectedSpace (Variety.Point U.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Existence in any closed subgroup, without a connectedness assumption on it. -/
public theorem exists_connectedUnipotentRadicalOf
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ U : ClosedSubgroup G, IsConnectedUnipotentRadicalOf H U := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  obtain ⟨R, hRn, hRc, hRu, hRm⟩ :=
    exists_ambient_unipotent_radical (G := H.carrierVariety)
  letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism R.carrierVariety G := H.inclusion.comp R.inclusion
  let U := f.imageClosedSubgroup
  have hUle : U ≤ H := by
    rintro x ⟨z, rfl⟩
    exact (H.pointEquiv (R.inclusion.onPoints z)).property
  have hmem (y : Variety.Point H.carrierVariety) :
      H.inclusion.onPoints y ∈ U ↔ y ∈ R := by
    constructor
    · rintro ⟨z, hz⟩
      have heq : R.inclusion.onPoints z = y := H.inclusion_injective hz
      rw [← heq]
      exact (R.pointEquiv z).property
    · intro hy
      exact ⟨R.pointEquiv.symm ⟨y, hy⟩, rfl⟩
  have hUn : H ≤ U.normalizer := by
    intro h hh
    let y := H.pointEquiv.symm ⟨h, hh⟩
    have hy : H.inclusion.onPoints y = h := by rfl
    change h ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨r, rfl⟩
      have hconj := hRn.conj_mem (R.inclusion.onPoints r) (R.pointEquiv r).property y
      have hm := (hmem _).mpr hconj
      change H.inclusion.onPoints (y * R.inclusion.onPoints r * y⁻¹) ∈ U.toSubgroup at hm
      change h * H.inclusion.onPoints (R.inclusion.onPoints r) * h⁻¹ ∈ U.toSubgroup
      simpa only [map_mul, map_inv, hy] using hm
    · intro hz
      have hzH : z ∈ H := by
        have hhconj := H.toSubgroup.mul_mem
          (H.toSubgroup.mul_mem (H.toSubgroup.inv_mem hh) (hUle hz)) hh
        change z ∈ H.toSubgroup
        simpa [mul_assoc] using hhconj
      change h * z * h⁻¹ ∈ U at hz
      let zH := H.pointEquiv.symm ⟨z, hzH⟩
      have hzHval : H.inclusion.onPoints zH = z := by rfl
      have hconj : y * zH * y⁻¹ ∈ R := by
        apply (hmem _).mp
        simpa only [map_mul, map_inv, hy, hzHval] using hz
      have hback := hRn.conj_mem _ hconj y⁻¹
      have hzR : zH ∈ R := by
        change zH ∈ R.toSubgroup
        simpa [mul_assoc] using hback
      change z ∈ U
      simpa only [hzHval] using (hmem zH).mpr hzR
  refine ⟨U, hUle, f.imageClosedSubgroup_isConnected
    (connectedRadical_carrier_connected R hRc), ?_, hUn, ?_⟩
  · obtain ⟨π, hπ, _, _⟩ := f.closedImageProjection_exists
    exact hRu.of_surjective π hπ
  · intro V hVH hVc hVu hVn
    let j := V.inclusion.codRestrictClosedSubgroup H (fun x => hVH (V.pointEquiv x).property)
    let W := j.imageClosedSubgroup
    letI : AlgebraicGroup W.carrierVariety := W.carrierAlgebraicGroup
    have hWmem (y : Variety.Point H.carrierVariety) :
        y ∈ W ↔ H.inclusion.onPoints y ∈ V := by
      constructor
      · rintro ⟨v, rfl⟩
        exact (V.pointEquiv v).property
      · intro hy
        refine ⟨V.pointEquiv.symm ⟨H.inclusion.onPoints y, hy⟩, ?_⟩
        apply H.inclusion_injective
        rfl
    have hWn : W.toSubgroup.Normal := by
      constructor
      intro y hy h
      apply (hWmem _).mpr
      have hn := Subgroup.mem_normalizer_iff.mp
        (hVn (H.pointEquiv h).property) (H.inclusion.onPoints y)
      have hh := hn.mp ((hWmem y).mp hy)
      change H.inclusion.onPoints h * H.inclusion.onPoints y *
        (H.inclusion.onPoints h)⁻¹ ∈ V at hh
      simpa only [map_mul, map_inv] using hh
    have hWc := j.imageClosedSubgroup_isConnected
      (connectedRadical_carrier_connected V hVc)
    have hWu : IsUnipotentAlgebraicGroup W.carrierVariety := by
      obtain ⟨π, hπ, _, _⟩ := j.closedImageProjection_exists
      exact hVu.of_surjective π hπ
    have hWR := hRm W hWn hWc hWu
    intro x hx
    let xH := H.pointEquiv.symm ⟨x, hVH hx⟩
    exact (hmem xH).mpr (hWR ((hWmem xH).mpr hx))

omit [IsAlgClosed k] in
/-- The connected unipotent radical is unique. -/
public theorem IsConnectedUnipotentRadicalOf.eq
    {G : Variety k} [AlgebraicGroup G] {H U V : ClosedSubgroup G}
    (hU : IsConnectedUnipotentRadicalOf H U)
    (hV : IsConnectedUnipotentRadicalOf H V) : U = V := by
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (hV.2.2.2.2 U hU.1 hU.2.1 hU.2.2.1 hU.2.2.2.1)
    (hU.2.2.2.2 V hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1)

/-- Ambient elements normalizing a subgroup also normalize its connected
unipotent radical. -/
public theorem IsConnectedUnipotentRadicalOf.normalizer_le
    {G : Variety k} [AlgebraicGroup G] {H U : ClosedSubgroup G}
    (hU : IsConnectedUnipotentRadicalOf H U) : H.normalizer ≤ U.normalizer := by
  have hconj (g : Variety.Point G) (hg : g ∈ H.normalizer) : U.conjugate g ≤ U := by
    apply hU.2.2.2.2
    · intro x hx
      have hxH := hU.1 ((U.mem_conjugate_iff g x).mp hx)
      have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mp hxH
      change x ∈ H.toSubgroup
      simpa [mul_assoc] using h
    · have heq : (U.conjugate g : Set (Variety.Point G)) =
          (AlgebraicGroup.conjugationByMorphism G g).toFun ''
            (U : Set (Variety.Point G)) := by
        ext x
        constructor
        · intro hx
          refine ⟨g⁻¹ * x * g, (U.mem_conjugate_iff g x).mp hx, ?_⟩
          rw [AlgebraicGroup.conjugationByMorphism_apply]
          simp [mul_assoc]
        · rintro ⟨y, hy, rfl⟩
          apply (U.mem_conjugate_iff g _).mpr
          rw [AlgebraicGroup.conjugationByMorphism_apply]
          change y ∈ U.toSubgroup at hy
          simpa [mul_assoc] using hy
      rw [heq]
      exact hU.2.1.image _
        (AlgebraicGroup.conjugationByMorphism G g).continuous.continuousOn
    · exact hU.2.2.1.of_surjective (U.conjugateIso g).hom
        (U.conjugateIso g).toMulEquiv.surjective
    · intro b hb
      change b ∈ Subgroup.normalizer ((U.conjugate g).toSubgroup : Set (Variety.Point G))
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hginv : g⁻¹ ∈ H.normalizer.toSubgroup := H.normalizer.toSubgroup.inv_mem hg
      have hbH := (Subgroup.mem_normalizer_iff.mp hginv b).mp hb
      have hbH' : g⁻¹ * b * g ∈ H := by
        change g⁻¹ * b * g ∈ H.toSubgroup
        simpa using hbH
      have hbN := hU.2.2.2.1 hbH'
      have heq := Subgroup.mem_normalizer_iff.mp hbN (g⁻¹ * x * g)
      change x ∈ U.conjugate g ↔ b * x * b⁻¹ ∈ U.conjugate g
      simpa only [U.mem_conjugate_iff, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left, inv_mul_cancel_left] using heq
  intro g hg
  change g ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    apply hconj g hg
    apply (U.mem_conjugate_iff g _).mpr
    simpa [mul_assoc] using hx
  · intro hx
    have hg' : g⁻¹ ∈ H.normalizer := H.normalizer.toSubgroup.inv_mem hg
    have hback : g⁻¹ * (g * x * g⁻¹) * g ∈ U := by
      apply hconj g⁻¹ hg'
      apply (U.mem_conjugate_iff g⁻¹ _).mpr
      simpa [mul_assoc] using hx
    change x ∈ U
    simpa [mul_assoc] using hback

/-- In a reductive group, a connected normal unipotent subgroup is trivial. -/
public theorem connectedRadical_eq_bot_of_reductive
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) (U : ClosedSubgroup G)
    (hUn : U.toSubgroup.Normal)
    (hUc : _root_.IsConnected (U : Set (Variety.Point G)))
    (hUu : IsUnipotentAlgebraicGroup U.carrierVariety) :
    U.toSubgroup = ⊥ := by
  obtain ⟨R, hR⟩ := Theory.AlgebraicGroup.exists_radical G
  have hUR := hR.maximal U hUn hUc (isSolvable_of_isUnipotentAlgebraicGroup hUu)
  have htriv := subtorus_inf_unipotent_eq_bot R U (hG.2 R hR) hUu
  apply le_antisymm
  · intro x hx
    have h : x ∈ R.toSubgroup ⊓ U.toSubgroup := ⟨hUR hx, hx⟩
    rwa [htriv] at h
  · exact bot_le

/-- The connected ambient radical is the unipotent radical of the connected
solvable radical. This identifies the two constructions without extending
connected maximality to arbitrary disconnected unipotent subgroups. -/
public theorem IsConnectedUnipotentRadicalOf.exists_radical
    {G : Variety k} [AlgebraicGroup G] {U : ClosedSubgroup G}
    (hU : IsConnectedUnipotentRadicalOf ClosedSubgroup.top U) :
    ∃ R : ClosedSubgroup G, IsRadicalSubgroup R ∧ IsUnipotentRadicalOf R U := by
  obtain ⟨R, hR⟩ := Theory.AlgebraicGroup.exists_radical G
  obtain ⟨V, hV, hVc⟩ := exists_unipotentRadical_of_connected_solvable R hR.connected hR.solvable
  have hVn := hV.normal_of_radical hR
  have hVnorm : ClosedSubgroup.top ≤ V.normalizer := by
    intro g _
    change g ∈ Subgroup.normalizer (V.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.normalizer_eq_top_iff.mpr hVn]
    trivial
  have hVU : V ≤ U := hU.2.2.2.2 V (fun _ _ => trivial) hVc hV.2.1 hVnorm
  have hUn : U.toSubgroup.Normal := by
    constructor
    intro x hx g
    exact (Subgroup.mem_normalizer_iff.mp (hU.2.2.2.1 (show g ∈ ClosedSubgroup.top from trivial)) x).mp hx
  have hUR : U ≤ R := hR.maximal U hUn hU.2.1
    (isSolvable_of_isUnipotentAlgebraicGroup hU.2.2.1)
  have hUV : U ≤ V := hV.contains_unipotent_closedSubgroup hR.connected hR.solvable hUR hU.2.2.1
  have hEq : V = U := SetLike.coe_injective (Set.Subset.antisymm hVU hUV)
  exact ⟨R, hR, hEq ▸ hV⟩

end Theory.AlgebraicGroup
