module

public import Theory.Representation.InvertedOddSubgroup
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# Rank of an odd support inverted by an involution

For a finite action on an elementary abelian two-group, if an involution
inverts an odd subgroup R, then |[V,R]| = |[V,R,t]|². The latter subgroup
lies both in [V,R] and in [V,t]. No faithfulness assumption is necessary.

Restrict to [V,R] and the normalizer of R. Coprime action makes R fixed-point
free on its support, so `invertedOddSubgroup_card_eq_commutator_sq` applies.
The final map back to V identifies its image with the actual ambient action
commutator. This generalizes the automorphism-group construction in
`Theory.GroupAction.InvertedOddSupportDisplacement` without changing it.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.11, printed p.183, identity (*).
-/

open scoped IsMulCommutative

/-- The support of an inverted odd subgroup has square order, with square root
the displacement on that support. Both ambient containments are retained. -/
public theorem invertedOddSubgroup_support_card_data
    {G W : Type*} [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W]
    (R : Subgroup G) (hodd : Odd (Nat.card R))
    (t : G) (ht : IsInvolution t)
    (hinverts : ∀ r ∈ R, t * r * t⁻¹ = r⁻¹) :
    Nat.card (commutatorAction R W) =
      Nat.card (commutatorSubgroup (Subgroup.zpowers t) W (commutatorAction R W)) ^ 2 ∧
    commutatorSubgroup (Subgroup.zpowers t) W (commutatorAction R W) ≤
      commutatorAction R W ∧
    commutatorSubgroup (Subgroup.zpowers t) W (commutatorAction R W) ≤
      commutatorAction (Subgroup.zpowers t) W := by
  classical
  let U := commutatorAction R W
  let C := FixedPoints.subgroup R W
  have hcop : Nat.Coprime (Nat.card R) (Nat.card W) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := R) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  let N := Subgroup.normalizer (R : Set G)
  have htN : t ∈ N := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨r,hr,rfl⟩
      change t*r*t⁻¹ ∈ R
      rw [hinverts r hr]
      exact R.inv_mem hr
    · intro r hr
      refine ⟨r⁻¹,R.inv_mem hr,?_⟩
      change t*r⁻¹*t⁻¹=r
      simpa only [inv_inv] using hinverts r⁻¹ (R.inv_mem hr)
  let _ : IsInvariant N W U := commutatorAction_isInvariant_of_normalizing_actor N R le_rfl
  let Ri := R.subgroupOf N
  let ti : N := ⟨t,htN⟩
  let _ : IsElementaryAbelian 2 U := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun point =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) (point : W)) }
  have hRiOdd : Odd (Nat.card Ri) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show R ≤ N from Subgroup.le_normalizer)).toEquiv]
    exact hodd
  have hti : IsInvolution ti :=
    ⟨fun heq => ht.1 (congrArg Subtype.val heq),Subtype.ext ht.2⟩
  have hinvertRi : ∀ r : Ri, ti * (r : N) * ti⁻¹ = (r : N)⁻¹ := by
    intro r
    exact Subtype.ext (hinverts r r.property)
  have hRiFixed : FixedPoints.subgroup Ri U = ⊥ := by
    apply bot_unique
    intro point hpoint
    have hfixed : (point : W) ∈ C := by
      intro r
      have hh := hpoint ⟨⟨r,Subgroup.le_normalizer r.property⟩,r.property⟩
      exact congrArg Subtype.val hh
    exact Subtype.ext (hcompl.disjoint.le_bot ⟨hfixed,point.property⟩)
  let B := commutatorAction (Subgroup.zpowers ti) U
  let S := B.map U.subtype
  have hScard : Nat.card S = Nat.card B := Subgroup.card_map_of_injective U.subtype_injective
  have hsquare : Nat.card U = Nat.card S ^ 2 := by
    rw [hScard]
    exact invertedOddSubgroup_card_eq_commutator_sq Ri hRiOdd ti hti hinvertRi hRiFixed
  have hSgen (D : Subgroup W) (hD : ∀ u ∈ U, u⁻¹ * (t • u) ∈ D) : S ≤ D := by
    rintro point ⟨vector,hvector,rfl⟩
    change vector ∈ commutatorAction (Subgroup.zpowers ti) U at hvector
    rw [commutatorAction_eq_closure] at hvector
    apply Subgroup.closure_induction (x := vector)
      (p := fun (v : U) _ => (v : W) ∈ D) ?_ ?_ ?_ ?_ hvector
    · rintro vector ⟨actor,point,rfl⟩
      have hTcard : Nat.card (Subgroup.zpowers ti) = 2 := by
        rw [Nat.card_zpowers,orderOf_eq_prime hti.2 hti.1]
      by_cases hone : actor = 1
      · simp only [hone,one_smul,inv_mul_cancel,OneMemClass.coe_one]
        exact D.one_mem
      obtain ⟨other,hother,hunique⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers ti)).mp hTcard
      have hgenNe : (⟨ti,Subgroup.mem_zpowers ti⟩ : Subgroup.zpowers ti) ≠ 1 :=
        fun heq => hti.1 (congrArg Subtype.val heq)
      have heq : actor = ⟨ti,Subgroup.mem_zpowers ti⟩ :=
        (hunique actor hone).trans (hunique _ hgenNe).symm
      rw [heq]
      exact hD point point.property
    · exact D.one_mem
    · intro x y _ _ hx hy
      exact D.mul_mem hx hy
    · intro x _ hx
      exact D.inv_mem hx
  have hSeq : S = commutatorSubgroup (Subgroup.zpowers t) W U := by
    apply le_antisymm
    · apply hSgen
      intro w hw
      exact Subgroup.subset_closure ⟨⟨t, Subgroup.mem_zpowers t⟩, w, hw, rfl⟩
    · change Subgroup.closure _ ≤ S
      rw [Subgroup.closure_le]
      rintro _ ⟨r, w, hw, rfl⟩
      have hrN : (r : G) ∈ N := (Subgroup.zpowers_le.mpr htN) r.property
      let rn : N := ⟨r, hrN⟩
      have hrn : rn ∈ Subgroup.zpowers ti := by
        obtain ⟨z, hz⟩ := r.property
        exact ⟨z, Subtype.ext hz⟩
      let ri : Subgroup.zpowers ti := ⟨rn, hrn⟩
      let wi : U := ⟨w, hw⟩
      refine ⟨wi⁻¹ * (ri • wi), ?_, rfl⟩
      change wi⁻¹ * (ri • wi) ∈ commutatorAction (Subgroup.zpowers ti) U
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨ri, wi, rfl⟩
  rw [hSeq] at hsquare
  refine ⟨hsquare, ?_, ?_⟩
  · rw [← hSeq]
    exact Subgroup.map_subtype_le _
  · rw [← hSeq]
    apply hSgen
    intro w _
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨t, Subgroup.mem_zpowers t⟩, w, rfl⟩

/-- Equality in the support bound makes the involution trivial on the odd
fixed space and central on the actors fixing the odd support pointwise.
This is the subgroup form of D.2.11(3). -/
public theorem invertedOddSubgroup_full_support
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (R : Subgroup G) (hodd : Odd (Nat.card R))
    (t : G) (ht : IsInvolution t)
    (hinverts : ∀ r ∈ R, t * r * t⁻¹ = r⁻¹)
    (hcard : Nat.card (commutatorAction R V) =
      Nat.card (commutatorAction (Subgroup.zpowers t) V) ^ 2)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    commutatorAction (Subgroup.zpowers t) V =
      commutatorSubgroup (Subgroup.zpowers t) V (commutatorAction R V) ∧
    (∀ v ∈ FixedPoints.subgroup R V, t • v = v) ∧
    ∀ y : G, (∀ r ∈ R, Commute y r) →
      (∀ v ∈ commutatorAction R V, y • v = v) → Commute y t := by
  let U := commutatorAction R V
  let C := FixedPoints.subgroup R V
  let D := commutatorAction (Subgroup.zpowers t) V
  let E := commutatorSubgroup (Subgroup.zpowers t) V U
  obtain ⟨hsquare, hEU, hED⟩ := invertedOddSubgroup_support_card_data (W := V) R hodd t ht hinverts
  have hDE : D = E := by
    apply (Subgroup.eq_of_le_of_card_ge hED ?_).symm
    change Nat.card D ≤ Nat.card E
    change Nat.card U = Nat.card E ^ 2 at hsquare
    change Nat.card U = Nat.card D ^ 2 at hcard
    nlinarith
  have hDU : D ≤ U := hDE ▸ hEU
  have htN : t ∈ Subgroup.normalizer (R : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      change t * r * t⁻¹ ∈ R
      rw [hinverts r hr]
      exact R.inv_mem hr
    · intro r hr
      refine ⟨r⁻¹, R.inv_mem hr, ?_⟩
      change t * r⁻¹ * t⁻¹ = r
      simpa only [inv_inv] using hinverts r⁻¹ (R.inv_mem hr)
  have hcop : Nat.Coprime (Nat.card R) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hcompl : IsCompl C U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := R) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have hCinv := fixedPoints_isInvariant_of_normalizing_actor (V := V)
    (Subgroup.zpowers t) R (Subgroup.zpowers_le.mpr htN)
  have hUinv := commutatorAction_isInvariant_of_normalizing_actor (V := V)
    (Subgroup.zpowers t) R (Subgroup.zpowers_le.mpr htN)
  have htC : ∀ v ∈ C, t • v = v := by
    intro v hv
    have hdelta : v⁻¹ * (t • v) ∈ D := by
      change v⁻¹ * (t • v) ∈ commutatorAction (Subgroup.zpowers t) V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨t, Subgroup.mem_zpowers t⟩, v, rfl⟩
    have hdeltaC : v⁻¹ * (t • v) ∈ C :=
      C.mul_mem (C.inv_mem hv)
        ((hCinv.invariant ⟨t, Subgroup.mem_zpowers t⟩ v).mp hv)
    exact (inv_mul_eq_one.mp (hcompl.disjoint.le_bot ⟨hdeltaC, hDU hdelta⟩)).symm
  refine ⟨hDE, htC, ?_⟩
  intro y hyR hyU
  have hyC : ∀ v ∈ C, y • v ∈ C := by
    intro v hv r
    change (r : G) • (y • v) = y • v
    calc
      (r : G) • (y • v) = y • ((r : G) • v) := by
        simp only [← mul_smul, (hyR r r.property).eq]
      _ = y • v := congrArg (fun w : V => y • w) (hv r)
  have hinj : Function.Injective (MulDistribMulAction.toMulAut G V) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← fixingSubgroup_univ_eq_ker_toMulAut]
    exact hfaith
  change y * t = t * y
  apply hinj
  ext v
  change (y * t) • v = (t * y) • v
  simp only [mul_smul]
  let _ : U.Normal := Subgroup.normal_of_isMulCommutative U
  have hv : v ∈ C ⊔ U := by rw [hcompl.sup_eq_top]; exact Subgroup.mem_top v
  obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hv
  have htu : t • u ∈ U := (hUinv.invariant ⟨t, Subgroup.mem_zpowers t⟩ u).mp hu
  simp only [smul_mul', htC c hc, htC (y • c) (hyC c hc), hyU u hu, hyU (t • u) htu]
