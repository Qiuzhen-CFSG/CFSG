module

public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Solvable
public import Theory.AlgebraicGroup.ClosedSubgroup.Quotient
public import Theory.AlgebraicGroup.Solvable.TorusComplement
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent.TorusFree.BorelCentralizer

/-!
# Connected groups without nontrivial tori are unipotent

Borel, *Linear Algebraic Groups*, §11.5(2), first makes a Borel unipotent
by the solvable torus decomposition. The stronger induction statement is
that a connected group with a unipotent Borel equals that Borel. For a
nontrivial Borel, the connected center has positive dimension. Once §11.4(2)
places it in the ambient center, its genuine affine quotient has smaller
dimension and the image of the Borel is again a unipotent Borel. Equality
in that quotient lifts because its point kernel lies in the original Borel.
For a trivial Borel, §11.4(2) makes the ambient group commutative, and Borel
maximality gives equality directly.

This module proves the quotient transport, dimension decrease, and entire
induction, then discharges §11.4(2) using `borel_centralizer_le_center`.
The terminal theorem supplies the universal unipotence input for the central
maximal torus argument. No descent of torus-freeness through a unipotent kernel
is assumed.

Source: `refs/KGroup/Bor1/Chapter4.tex`, §§11.4–11.5; the solvable
decomposition is §10.6(4) of `refs/KGroup/Bor1/Chapter3.tex`.
-/

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.TorusFree
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

omit [IsAlgClosed k] in
private theorem carrier_connected (B : ClosedSubgroup G)
    (hB : _root_.IsConnected (B : Set (Variety.Point G))) :
    Variety.IsConnected B.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (B : Set (Variety.Point G))} :=
    Subtype.connectedSpace hB
  let : ConnectedSpace (Variety.Point B.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- The solvable torus decomposition makes a connected solvable group
unipotent when all its subtori are trivial. -/
public theorem isUnipotent_of_solvable_of_torusFree
    (hG : Variety.IsConnected G) (hsolv : Group.IsSolvable (Variety.Point G))
    (htorus : ∀ T : ClosedSubgroup G, IsSubtorus T → T.toSubgroup = ⊥) :
    IsUnipotentAlgebraicGroup G := by
  obtain ⟨U, hU, _hUc, T, hT, _hTmax⟩ :=
    exists_maximalTorus_complement_of_solvable_connected hsolv hG
  intro x
  obtain ⟨t, u, ht, hu, htu⟩ := hT.2.1 x
  have htone : t = 1 := by
    apply Subgroup.mem_bot.mp
    rwa [htorus T hT.1] at ht
  rw [htone, one_mul] at htu
  exact htu ▸ (hU u).mp hu

/-- In an ambient group without nontrivial subtori every Borel is unipotent.
The subgroup tori are transported by the literal inclusion into the ambient group. -/
public theorem borel_isUnipotent_of_torusFree
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (htorus : ∀ T : ClosedSubgroup G, IsSubtorus T → T.toSubgroup = ⊥) :
    IsUnipotentAlgebraicGroup B.carrierVariety := by
  apply isUnipotent_of_solvable_of_torusFree (carrier_connected B hB.connected) hB.solvable
  intro T hT
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let j := B.inclusion.comp T.inclusion
  have himage := htorus j.imageClosedSubgroup (morphism_image_isTorus j hT)
  apply le_antisymm _ bot_le
  intro x hx
  let t := T.pointEquiv.symm ⟨x, hx⟩
  have ht : j.onPoints t ∈ j.imageClosedSubgroup.toSubgroup := ⟨t, rfl⟩
  rw [himage] at ht
  apply Subgroup.mem_bot.mpr
  apply B.inclusion_injective
  have heq : T.inclusion.onPoints t = x := by
    exact congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨x, hx⟩)
  have hzero := Subgroup.mem_bot.mp ht
  change B.inclusion.onPoints (T.inclusion.onPoints t) = 1 at hzero
  simpa only [heq, map_one] using hzero

/-- A surjective morphism with solvable point kernel maps every Borel to a
Borel. Connectedness of the kernel is unnecessary: the identity component of
the preimage of a connected solvable overgroup still surjects onto it. -/
public theorem borel_image_of_solvable_kernel
    (q : Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hker : Group.IsSolvable q.kernel)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    IsBorelSubgroup (q.comp B.inclusion).imageClosedSubgroup := by
  let r := q.comp B.inclusion
  refine ⟨r.imageClosedSubgroup_isConnected (carrier_connected B hB.connected),
    r.imageClosedSubgroup_isSolvable hB.solvable, ?_⟩
  intro S hSc hSs hBS
  let P := q.closedSubgroupPreimage S
  let I := P.identityComponentAmbient
  let iP := I.inclusion.codRestrictClosedSubgroup P
    (fun x => P.identityComponentAmbient_le (I.pointEquiv x).property)
  have hiP : Function.Injective iP.onPoints := by
    intro x y hxy
    apply I.inclusion_injective
    have heq := congrArg P.inclusion.onPoints hxy
    simpa only [iP, Morphism.codRestrictClosedSubgroup_inclusion_apply] using heq
  let : Group.IsSolvable (Variety.Point P.carrierVariety) :=
    q.closedSubgroupPreimage_isSolvable_of_kernel S hSs
      (q.preimageRestriction_kernel_isSolvable_of_kernel S hker)
  have hIs : Group.IsSolvable (Variety.Point I.carrierVariety) :=
    Group.isSolvable_of_isSolvable_injective hiP
  have hBP : B ≤ P := by
    intro b hb
    apply hBS
    exact ⟨B.pointEquiv.symm ⟨b, hb⟩,
      congrArg q.onPoints (congrArg Subtype.val (B.pointEquiv.apply_symm_apply ⟨b, hb⟩))⟩
  have hBI : B ≤ I :=
    connected_closedSubgroup_le_identityComponentAmbient B P hB.connected hBP
  have hIB : I = B := hB.maximal I P.identityComponentAmbient_isConnected hIs hBI
  have himage := q.closedSubgroupPreimage_identityComponent_image_eq hq S hSc
  change (q.comp I.inclusion).imageClosedSubgroup = S at himage
  rw [hIB] at himage
  exact himage.symm

private theorem image_dimension_of_injective
    (f : Morphism G Q) (hf : Function.Injective f.onPoints) :
    Variety.dimension f.imageClosedSubgroup.carrierVariety = Variety.dimension G := by
  let : Subsingleton f.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hf
    exact x.property.trans y.property.symm
  let : Subsingleton (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
    f.kernelClosedSubgroup.pointEquiv.subsingleton
  have hker : Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points _).mpr (Finite.of_subsingleton)
  have hdim := morphism_dimension_eq_kernel_add_image f
  rw [hker, zero_add] at hdim
  exact hdim.symm

/-- A surjective algebraic-group morphism with positive-dimensional kernel
strictly decreases dimension. -/
public theorem quotient_dimension_lt_of_positive_kernel
    (q : Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hker : 0 < Variety.dimension q.kernelClosedSubgroup.carrierVariety) :
    Variety.dimension Q < Variety.dimension G := by
  have himage : Variety.dimension q.imageClosedSubgroup.carrierVariety =
      Variety.dimension Q := by
    apply (closedSubgroup_dimension_eq_iff_contains_identityComponent Q _).mpr
    intro x _
    exact hq x
  rw [morphism_dimension_eq_kernel_add_image q, himage]
  simpa only [zero_add] using
    (Cardinal.add_lt_add_iff_of_right_lt_aleph0
      (variety_dimension_lt_aleph0 Q)).mpr hker

/-- The image in the ambient group of the connected center of a nontrivial
unipotent Borel is positive-dimensional and central, given the local §11.4(2)
centralizer containment. This is the kernel used by §11.5(2). -/
public theorem exists_positive_central_subgroup_of_unipotent_borel
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hU : IsUnipotentAlgebraicGroup B.carrierVariety) (hne : B.toSubgroup ≠ ⊥)
    (hcentral : B.centralizer.toSubgroup ≤ Subgroup.center (Variety.Point G)) :
    ∃ H : ClosedSubgroup G, H ≤ B ∧
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
      H.toSubgroup ≤ Subgroup.center (Variety.Point G) ∧
      0 < Variety.dimension H.carrierVariety := by
  let Z := (ClosedSubgroup.top (G := B.carrierVariety)).centralizer
  let Z₀ := Z.identityComponentAmbient
  letI : AlgebraicGroup Z₀.carrierVariety := Z₀.carrierAlgebraicGroup
  let j := B.inclusion.comp Z₀.inclusion
  let H := j.imageClosedSubgroup
  have hpositive : 0 < Variety.dimension Z₀.carrierVariety := by
    rw [show Z₀ = Z.identityComponentAmbient from rfl, Z.dimension_identityComponentAmbient]
    exact unipotent_positiveCenter_dimension hU
      (connected_closedSubgroup_dimension_pos_of_ne_bot B hB.connected hne)
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨z, rfl⟩
    exact (B.pointEquiv (Z₀.inclusion.onPoints z)).property
  · exact j.imageClosedSubgroup_isConnected
      (carrier_connected Z₀ Z.identityComponentAmbient_isConnected)
  · rintro x ⟨z, rfl⟩
    apply hcentral
    change B.inclusion.onPoints (Z₀.inclusion.onPoints z) ∈
      Subgroup.centralizer (B.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    let bB := B.pointEquiv.symm ⟨b, hb⟩
    have hz : Z₀.inclusion.onPoints z ∈ Z :=
      Z.identityComponentAmbient_le (Z₀.pointEquiv z).property
    have heq := Subgroup.mem_centralizer_iff.mp hz bB (by trivial)
    have heq' := congrArg B.inclusion.onPoints heq
    have hbB : B.inclusion.onPoints bB = b :=
      congrArg Subtype.val (B.pointEquiv.apply_symm_apply ⟨b, hb⟩)
    simpa only [map_mul, hbB] using heq'
  · rw [show H = j.imageClosedSubgroup from rfl,
      image_dimension_of_injective j (B.inclusion_injective.comp Z₀.inclusion_injective)]
    exact hpositive

/-- The induction quotient for a nontrivial unipotent Borel, using the
local §11.4(2) centralizer containment. Its algebraic projection has point
kernel contained in the original Borel; the actual Borel image is unipotent,
and the connected target has strictly smaller dimension. -/
public theorem exists_smaller_unipotent_borel_quotient
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hU : IsUnipotentAlgebraicGroup B.carrierVariety) (hne : B.toSubgroup ≠ ⊥)
    (hcentral : B.centralizer.toSubgroup ≤ Subgroup.center (Variety.Point G)) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q) (q : Morphism G Q),
      Function.Surjective q.onPoints ∧ Variety.IsConnected Q ∧
      q.kernel ≤ B.toSubgroup ∧ Variety.dimension Q < Variety.dimension G ∧
      IsBorelSubgroup (q.comp B.inclusion).imageClosedSubgroup ∧
      IsUnipotentAlgebraicGroup (q.comp B.inclusion).imageClosedSubgroup.carrierVariety := by
  obtain ⟨H, hHB, _hHc, hHZ, hHpos⟩ :=
    exists_positive_central_subgroup_of_unipotent_borel B hB hU hne hcentral
  have hHN : H.toSubgroup.Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_center_iff.mp (hHZ hx) g, mul_inv_cancel_right]
    exact hx
  obtain ⟨n, F, hFker⟩ := H.generalLinearMorphism_exactKernel_exists hHN
  letI : AlgebraicGroup F.imageClosedSubgroup.carrierVariety :=
    F.imageClosedSubgroup.carrierAlgebraicGroup
  obtain ⟨q, hq, hqker, _⟩ := F.closedImageProjection_exists
  have hker : q.kernel = H.toSubgroup := hqker.trans hFker
  have hclosedker : q.kernelClosedSubgroup = H := by
    apply SetLike.coe_injective
    exact congrArg (fun L : Subgroup (Variety.Point G) => (L : Set (Variety.Point G))) hker
  have hkerS : Group.IsSolvable q.kernel := by
    apply Group.isSolvable_of_comm
    intro x y
    apply Subtype.ext
    have hx : x.val ∈ H.toSubgroup := hker ▸ x.property
    exact (Subgroup.mem_center_iff.mp (hHZ hx) y.val).symm
  have hQdim : Variety.dimension F.imageClosedSubgroup.carrierVariety <
      Variety.dimension G := by
    apply quotient_dimension_lt_of_positive_kernel q hq
    rwa [hclosedker]
  refine ⟨F.imageClosedSubgroup.carrierVariety, inferInstance, q, hq,
    connected_of_surjective_morphism q hG hq, ?_, hQdim,
    borel_image_of_solvable_kernel q hq hkerS B hB, ?_⟩
  · rw [hker]
    exact hHB
  · let r := q.comp B.inclusion
    letI : AlgebraicGroup r.imageClosedSubgroup.carrierVariety :=
      r.imageClosedSubgroup.carrierAlgebraicGroup
    obtain ⟨p, hp, _⟩ := r.closedImageProjection_exists
    exact hU.of_surjective p hp

/-- Equality with the quotient lifts to a closed subgroup containing the
point kernel. This applies to the literal Borel image in the induction quotient. -/
public theorem closedSubgroup_eq_top_of_image_eq_top
    (q : Morphism G Q) (B : ClosedSubgroup G) (hker : q.kernel ≤ B.toSubgroup)
    (himage : (q.comp B.inclusion).imageClosedSubgroup = ClosedSubgroup.top) :
    B = ClosedSubgroup.top := by
  apply SetLike.ext
  intro x
  constructor
  · intro _
    trivial
  · intro _
    have hx : q.onPoints x ∈ (q.comp B.inclusion).imageClosedSubgroup := by
      rw [himage]
      trivial
    obtain ⟨b, hb⟩ := hx
    have hk : x * (B.inclusion.onPoints b)⁻¹ ∈ q.kernel := by
      change q.onPoints (x * (B.inclusion.onPoints b)⁻¹) = 1
      change q.onPoints (B.inclusion.onPoints b) = q.onPoints x at hb
      simp only [map_mul, map_inv, hb, mul_inv_cancel]
    have hm := B.toSubgroup.mul_mem (hker hk) (B.pointEquiv b).property
    change x * (B.inclusion.onPoints b)⁻¹ * B.inclusion.onPoints b ∈ B at hm
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

omit [IsAlgClosed k] in
/-- The trivial-Borel case: §11.4(2) makes the ambient point group commutative,
and maximal connected solvability forces the Borel to be the whole group. -/
public theorem borel_eq_top_of_bot_of_centralizer_le_center
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hbot : B.toSubgroup = ⊥)
    (hcentral : B.centralizer.toSubgroup ≤ Subgroup.center (Variety.Point G)) :
    B = ClosedSubgroup.top := by
  have hcomm (x y : Variety.Point G) : x * y = y * x := by
    have hx : x ∈ B.centralizer.toSubgroup := by
      change x ∈ Subgroup.centralizer (B.toSubgroup : Set (Variety.Point G))
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [hbot] at hb
      rw [Subgroup.mem_bot.mp hb, one_mul, mul_one]
    exact (Subgroup.mem_center_iff.mp (hcentral hx) y).symm
  let : Group.IsSolvable (Variety.Point G) := Group.isSolvable_of_comm hcomm
  have htop : Group.IsSolvable
      (Variety.Point (ClosedSubgroup.top (G := G)).carrierVariety) :=
    Group.isSolvable_of_isSolvable_injective (ClosedSubgroup.top (G := G)).inclusion_injective
  exact (hB.maximal ClosedSubgroup.top hG htop (fun _ _ => by trivial)).symm

/-- Borel §11.5(2)'s dimension induction, conditional on the earlier
§11.4(2) assertion for connected groups. A unipotent Borel equals its ambient
connected group. The induction hypothesis is applied to the actual quotient,
not to an assumed torus-free target. -/
public theorem unipotent_borel_eq_top_of_borelCentralizers
    (hcentral : ∀ (K : Variety k) [AlgebraicGroup K], Variety.IsConnected K →
      ∀ B : ClosedSubgroup K, IsBorelSubgroup B →
        B.centralizer.toSubgroup ≤ Subgroup.center (Variety.Point K))
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hU : IsUnipotentAlgebraicGroup B.carrierVariety) : B = ClosedSubgroup.top := by
  suffices h : ∀ n : ℕ, ∀ (K : Variety k) [AlgebraicGroup K],
      (Variety.dimension K).toNat = n → Variety.IsConnected K →
      ∀ C : ClosedSubgroup K, IsBorelSubgroup C →
        IsUnipotentAlgebraicGroup C.carrierVariety → C = ClosedSubgroup.top from
    h _ G rfl hG B hB hU
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ hdim hK C hC hCu
    by_cases hbot : C.toSubgroup = ⊥
    · exact borel_eq_top_of_bot_of_centralizer_le_center hK C hC hbot
        (hcentral K hK C hC)
    obtain ⟨Q, hQgroup, q, _hq, hQ, hker, hlt, hCq, hUq⟩ :=
      exists_smaller_unipotent_borel_quotient hK C hC hCu hbot (hcentral K hK C hC)
    letI : AlgebraicGroup Q := hQgroup
    have hltNat : (Variety.dimension Q).toNat < n := by
      rw [← hdim]
      exact Cardinal.toNat_lt_toNat hlt (variety_dimension_lt_aleph0 K)
    have himage := ih _ hltNat Q rfl hQ (q.comp C.inclusion).imageClosedSubgroup hCq hUq
    exact closedSubgroup_eq_top_of_image_eq_top q C hker himage

/-- The torus-free specialization of Borel §11.5(2), with the earlier
§11.4(2) Borel centralizer assertion still explicit. Discharging that sole
remaining premise supplies exactly the universal input of
`CentralMaximalNilpotent.isNilpotent_of_torusFree_unipotence`. -/
public theorem isUnipotent_of_torusFree_of_borelCentralizers
    (hcentral : ∀ (K : Variety k) [AlgebraicGroup K], Variety.IsConnected K →
      ∀ B : ClosedSubgroup K, IsBorelSubgroup B →
        B.centralizer.toSubgroup ≤ Subgroup.center (Variety.Point K))
    (hG : Variety.IsConnected G)
    (htorus : ∀ T : ClosedSubgroup G, IsSubtorus T → T.toSubgroup = ⊥) :
    IsUnipotentAlgebraicGroup G := by
  obtain ⟨B, hB⟩ := exists_borelSubgroup G
  have hU := borel_isUnipotent_of_torusFree B hB htorus
  have htop := unipotent_borel_eq_top_of_borelCentralizers hcentral hG B hB hU
  apply hU.of_surjective B.inclusion
  intro x
  have hx : x ∈ B := by rw [htop]; trivial
  exact ⟨B.pointEquiv.symm ⟨x, hx⟩,
    congrArg Subtype.val (B.pointEquiv.apply_symm_apply ⟨x, hx⟩)⟩

/-- Borel §11.5(2): a unipotent Borel subgroup of a connected affine algebraic
group is the whole group. The Borel centralizer premise in the dimension
induction is supplied by §11.4(2). -/
public theorem unipotent_borel_eq_top
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hU : IsUnipotentAlgebraicGroup B.carrierVariety) : B = ClosedSubgroup.top :=
  unipotent_borel_eq_top_of_borelCentralizers
    (fun _ _ hK C hC => borel_centralizer_le_center hK C hC) hG B hB hU

/-- The torus-free specialization of Borel §11.5(2): a connected affine
algebraic group over an algebraically closed field with no nontrivial subtori
is unipotent. No solvability or nilpotence hypothesis is required.
This discharges the universal input of
`CentralMaximalNilpotent.isNilpotent_of_torusFree_unipotence`. -/
public theorem isUnipotent_of_torusFree
    (hG : Variety.IsConnected G)
    (htorus : ∀ T : ClosedSubgroup G, IsSubtorus T → T.toSubgroup = ⊥) :
    IsUnipotentAlgebraicGroup G :=
  isUnipotent_of_torusFree_of_borelCentralizers
    (fun _ _ hK B hB => borel_centralizer_le_center hK B hB) hG htorus

end Theory.AlgebraicGroup.TorusFree
