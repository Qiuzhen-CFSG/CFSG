module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Intersections
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.LinearAlgebra.DisplacementFiltration
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The centralizer hyperplane and its displacement

The commutator form of 12.8.8(2), evaluated on the literal quotient U/Z(U),
identifies W/Z(U) with the orthogonal complement of the image of V₂.
That image has order two, since V₂ has order four and intersects Z(U) in
V₁. Double orthogonality gives Z(W)=V₂Z(U). A displacement whose restriction
to this hyperplane lands in the marked line has rank at most two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.8.8(2–3) and 12.8.10, printed pp.851–854, PDF pp.868–871.
The preceding commutator-form and intersection inputs remain with the
Preliminary owner; the full 12.8.10 assembly remains with Centers.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The actual central quotient projection, with no coordinate replacement. -/
def uhatProjection (F : InvariantFlag T V n) : F.U →* F.Uhat :=
  QuotientGroup.mk' (center F.U)

/-- The binary subspace given by the image of an ambient subgroup in U/Z(U). -/
def hatSubspace (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (A : Subgroup G) : Submodule (ZMod 2) (Additive F.Uhat) :=
  AddSubgroup.toZModSubmodule 2
    (((A.subgroupOf F.U).map F.uhatProjection).toAddSubgroup)

/-- The source commutator form, including its evaluation on actual quotient classes.
These are precisely the symplectic-form data of 12.8.8(2), not centralizer or
rank conclusions. Invariance is unnecessary for the present calculation. -/
structure UhatCommutatorForm (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (hc : ⁅F.U, F.U⁆ ≤ F.Vi 1) where
  valueEquiv : F.Vi 1 ≃* Multiplicative (ZMod 2)
  form : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)
  nondegenerate : form.Nondegenerate
  alternating : form.IsAlt
  evaluation (a b : F.U) :
    form (Additive.ofMul (F.uhatProjection a)) (Additive.ofMul (F.uhatProjection b)) =
      (valueEquiv ⟨⁅(a : G), (b : G)⁆,
        hc (commutator_mem_commutator a.property b.property)⟩).toAdd

private theorem centerIn_membership (A : Subgroup G) (x : G) :
    x ∈ centerIn A ↔ x ∈ A ∧ ∀ a ∈ A, a * x = x * a := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.property, fun a ha => congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr (fun a => Subtype.ext (hc a a.property)), rfl⟩

private theorem projection_center (F : InvariantFlag T V n) (a : F.U) :
    F.uhatProjection a = 1 ↔ (a : G) ∈ F.ZU := by
  rw [show F.uhatProjection a = 1 ↔ a ∈ center F.U from QuotientGroup.eq_one_iff a]
  constructor
  · exact fun ha => mem_map_of_mem F.U.subtype ha
  · rintro ⟨z, hz, he⟩
    have : z = a := Subtype.ext he
    exact this ▸ hz

private theorem center_subgroupOf (F : InvariantFlag T V n) :
    F.ZU.subgroupOf F.U = center F.U := by
  ext a
  exact (F.projection_center a).symm.trans (QuotientGroup.eq_one_iff a)

/-- Pulling back a hatted subspace adjoins exactly Z(U). -/
theorem mem_hatSubspace_projection (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (A : Subgroup G) (hA : A ≤ F.U) (a : F.U) :
    Additive.ofMul (F.uhatProjection a) ∈ F.hatSubspace A ↔ (a : G) ∈ A ⊔ F.ZU := by
  change a ∈ ((A.subgroupOf F.U).map F.uhatProjection).comap F.uhatProjection ↔ _
  rw [Subgroup.comap_map_eq, show F.uhatProjection.ker = center F.U from QuotientGroup.ker_mk' _,
    ← F.center_subgroupOf, ← subgroupOf_sup hA (F.ZU_le_W.trans inf_le_left)]
  rfl

private theorem form_zero_iff (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc) (a b : F.U) :
    B.form (Additive.ofMul (F.uhatProjection a)) (Additive.ofMul (F.uhatProjection b)) = 0 ↔
      (a : G) * (b : G) = (b : G) * (a : G) := by
  rw [B.evaluation]
  change B.valueEquiv _ = 1 ↔ _
  rw [map_eq_one_iff B.valueEquiv B.valueEquiv.injective, Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm

/-- The actual centralizer W maps to the orthogonal hyperplane. -/
theorem hat_plane_centralizer (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc) :
    F.hatSubspace F.W = B.form.orthogonal (F.hatSubspace (F.Vi 2)) := by
  ext q
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) q.toMul
  have hq : q = Additive.ofMul (F.uhatProjection u) := congrArg Additive.ofMul hu.symm
  rw [hq, F.mem_hatSubspace_projection F.W inf_le_left,
    sup_eq_left.mpr F.ZU_le_W, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro huW q hq
    obtain ⟨a, ha, he⟩ := hq
    change F.uhatProjection a = q.toMul at he
    rw [show q = Additive.ofMul (F.uhatProjection a) from congrArg Additive.ofMul he.symm]
    exact (F.form_zero_iff B a u).mpr (huW.2 a ha)
  · intro h
    refine ⟨u.property, fun a ha => ?_⟩
    let aU : F.U := ⟨a, le_conjugateSpanBy V F.H (F.le_seed 2 ha)⟩
    exact (F.form_zero_iff B aU u).mp
      (h (Additive.ofMul (F.uhatProjection aU)) (show _ ∈ F.hatSubspace (F.Vi 2) from
        ⟨aU, ha, rfl⟩))

/-- The extraspecial centralizer calculation used in the first line of 12.8.10.
The double orthogonal is computed from the preceding commutator form. -/
theorem plane_centralizer_center (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1} (B : F.UhatCommutatorForm hc) :
    centerIn F.W = F.Vi 2 ⊔ F.ZU := by
  have hP : F.Vi 2 ≤ F.W := (F.le_seed 2).trans F.seed_le_W
  apply le_antisymm
  · intro z hz
    obtain ⟨hzW, hzc⟩ := (centerIn_membership F.W z).mp hz
    let u : F.U := ⟨z, hzW.1⟩
    have ho : Additive.ofMul (F.uhatProjection u) ∈ B.form.orthogonal (F.hatSubspace F.W) := by
      intro q hq
      obtain ⟨a, ha, he⟩ := hq
      change F.uhatProjection a = q.toMul at he
      rw [show q = Additive.ofMul (F.uhatProjection a) from congrArg Additive.ofMul he.symm]
      exact (F.form_zero_iff B a u).mpr (hzc a ha)
    rw [F.hat_plane_centralizer B,
      B.form.orthogonal_orthogonal B.nondegenerate B.alternating.isRefl] at ho
    exact (F.mem_hatSubspace_projection (F.Vi 2)
      ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) u).mp ho
  · apply sup_le
    · intro z hz
      exact (centerIn_membership F.W z).mpr ⟨hP hz, fun a ha => (ha.2 z hz).symm⟩
    · intro z hz
      obtain ⟨hzU, hzc⟩ := (centerIn_membership F.U z).mp hz
      exact (centerIn_membership F.W z).mpr ⟨F.ZU_le_W hz, fun a ha => hzc a ha.1⟩

/-- The hatted plane has dimension one, by the orders of V₂ and V₁. -/
theorem finrank_hat_plane (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hcenter : V ⊓ F.ZU = F.Vi 1) :
    Module.finrank (ZMod 2) (F.hatSubspace (F.Vi 2)) = 1 := by
  let hP : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  let f : F.Vi 2 →* F.Uhat := F.uhatProjection.comp (inclusion hP)
  have hk : f.ker = (F.Vi 1).subgroupOf (F.Vi 2) := by
    ext a
    change F.uhatProjection (inclusion hP a) = 1 ↔ (a : G) ∈ F.Vi 1
    rw [F.projection_center, ← hcenter]
    exact ⟨fun ha => ⟨F.le_seed 2 a.property, ha⟩, fun ha => ha.2⟩
  have hkc : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.monotone (show 1 ≤ 2 by omega))).toEquiv,
      F.card 1 (by omega), pow_one]
  have hr : f.range = ((F.Vi 2).subgroupOf F.U).map F.uhatProjection := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨inclusion hP b, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hc := f.ker.card_mul_index
  rw [index_ker, hkc, F.card 2 hn] at hc
  have hcard : Nat.card (F.hatSubspace (F.Vi 2)) = 2 := by
    change Nat.card ((F.Vi 2).subgroupOf F.U |>.map F.uhatProjection) = 2
    rw [← hr]
    omega
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.hatSubspace (F.Vi 2))
  rw [hcard, Nat.card_zmod] at hd
  have he : 2 ^ Module.finrank (ZMod 2) (F.hatSubspace (F.Vi 2)) = 2 ^ 1 := by
    simpa using hd.symm
  exact (Nat.pow_right_injective (by omega)) he

/-- W is an actual hyperplane of U/Z(U). -/
theorem finrank_quotient_hat_centralizer (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hcenter : V ⊓ F.ZU = F.Vi 1) {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc) :
    Module.finrank (ZMod 2) (Additive F.Uhat ⧸ F.hatSubspace F.W) = 1 := by
  have hd := B.form.finrank_add_finrank_orthogonal B.alternating.isRefl
    (F.hatSubspace (F.Vi 2))
  rw [B.form.orthogonal_top_eq_bot B.nondegenerate, inf_bot_eq,
    finrank_bot, add_zero, F.finrank_hat_plane hn hcenter, ← F.hat_plane_centralizer B] at hd
  have hq := (F.hatSubspace F.W).finrank_quotient_add_finrank
  omega

/-- In group terms the same hyperplane calculation gives [U:W]=2. -/
theorem plane_centralizer_index_two (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 F.Uhat] (hn : 2 ≤ n)
    (hcenter : V ⊓ F.ZU = F.Vi 1) {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc) : (F.W.subgroupOf F.U).index = 2 := by
  let S := (F.W.subgroupOf F.U).map F.uhatProjection
  have hqc : Nat.card (Additive F.Uhat ⧸ F.hatSubspace F.W) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      F.finrank_quotient_hat_centralizer hn hcenter B, Nat.card_zmod, pow_one]
  have hd := (F.hatSubspace F.W).card_eq_card_quotient_mul_card
  change Nat.card F.Uhat = Nat.card S * Nat.card (Additive F.Uhat ⧸ F.hatSubspace F.W) at hd
  rw [hqc] at hd
  have hs := S.card_mul_index
  have hp : 0 < Nat.card S := Nat.card_pos
  have hi : S.index = 2 := by nlinarith
  have hk : F.uhatProjection.ker ≤ F.W.subgroupOf F.U := by
    intro u hu
    exact F.ZU_le_W ((F.projection_center u).mp hu)
  rw [← (F.W.subgroupOf F.U).index_map_eq
    (QuotientGroup.mk'_surjective (center F.U)) hk]
  exact hi

/-- The linear displacement of the already defined, literal action on U/Z(U). -/
def uhatDisplacement (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (h : F.H) : Additive F.Uhat →ₗ[ZMod 2] Additive F.Uhat :=
  (F.uhatAction h).toMonoidHom.toAdditive.toZModLinearMap 2 - LinearMap.id

/-- Evaluation uses the original ambient actor and the original quotient map. -/
theorem uhatDisplacement_projection (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (h : F.H) (a : F.U) :
    F.uhatDisplacement h (Additive.ofMul (F.uhatProjection a)) =
      Additive.ofMul (F.uhatProjection (F.uAction h a / a)) := by
  change Additive.ofMul (F.uhatAction h (F.uhatProjection a) / F.uhatProjection a) = _
  rw [map_div F.uhatProjection]
  exact congrArg (fun q : F.Uhat => Additive.ofMul (q / F.uhatProjection a))
    (F.uhatAction_apply_mk h a)

/-- The displacement image is a subgroup since U/Z(U) is elementary abelian. -/
def uhatDisplacementHom (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (h : F.H) : F.Uhat →* F.Uhat where
  toFun q := F.uhatAction h q / q
  map_one' := by simp
  map_mul' q r := by simp only [map_mul, div_eq_mul_inv, mul_inv_rev]; ac_rfl

/-- The moved subgroup [Uhat,h] for the actual quotient action. -/
def uhatMoved (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (h : F.H) : Subgroup F.Uhat := (F.uhatDisplacementHom h).range

/-- The range is exactly the subgroup generated by the actual displacements. -/
theorem uhatMoved_eq_closure (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (h : F.H) :
    F.uhatMoved h = closure (Set.range (fun q => F.uhatAction h q / q)) := by
  apply le_antisymm
  · rintro q ⟨a, rfl⟩
    exact subset_closure ⟨a, rfl⟩
  · apply (closure_le _).mpr
    rintro q ⟨a, rfl⟩
    exact ⟨a, rfl⟩

/-- The multiplicative moved subgroup and the linear displacement have the
same elements; this connects the numerical rank bound to [Uhat,h]. -/
theorem mem_uhatMoved_iff (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (h : F.H) (q : F.Uhat) :
    q ∈ F.uhatMoved h ↔ Additive.ofMul q ∈ (F.uhatDisplacement h).range := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Additive.ofMul a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a.toMul, congrArg Additive.toMul ha⟩

/-- The conjugate center embeds into precisely H, the actor of uhatAction. -/
def conjugateCenterActor (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hgP : g ∈ F.P L) : conjugate F.ZU g →* F.H :=
  inclusion ((F.conjugate_ZU_le_X g).trans (F.X_le_H g (F.P_le_G₂ hn L hL hgP)))

/-- The actual displacement of the centralizer hyperplane lands in the marked
line. The commutator containment is supplied by the proved intersection theorem. -/
theorem conjugate_center_displacement_hyperplane (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (x : conjugate F.ZU g) :
    (F.hatSubspace F.W).map
      (F.uhatDisplacement (F.conjugateCenterActor hn L hL g hgP x)) ≤
        F.hatSubspace (F.Vi 2) := by
  have hb : ⁅conjugate F.ZU g, F.W⁆ ≤ F.Vi 2 ⊔ F.ZU := by
    rw [commutator_comm, sup_comm]
    exact F.center_commutator_le_plane hn L hL hcenter hc
      (F.plane_centralizer_center B) g hgP hgH
  rintro q ⟨v, hv, rfl⟩
  obtain ⟨a, ha, he⟩ := hv
  change F.uhatProjection a = v.toMul at he
  rw [show v = Additive.ofMul (F.uhatProjection a) from congrArg Additive.ofMul he.symm,
    F.uhatDisplacement_projection,
    F.mem_hatSubspace_projection (F.Vi 2) ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))]
  change (x : G) * (a : G) * (x : G)⁻¹ / (a : G) ∈ F.Vi 2 ⊔ F.ZU
  have hba : ⁅(x : G), (a : G)⁆ ∈ F.Vi 2 ⊔ F.ZU :=
    hb (commutator_mem_commutator x.property ha)
  simpa only [commutatorElement_def, div_eq_mul_inv] using hba

/-- The rank-two bound in 12.8.10(4), on the literal displacement map. -/
theorem conjugate_center_displacement_rank_le_two (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (x : conjugate F.ZU g) :
    Module.finrank (ZMod 2)
      (F.uhatDisplacement (F.conjugateCenterActor hn L hL g hgP x)).range ≤ 2 := by
  have hb := (F.uhatDisplacement (F.conjugateCenterActor hn L hL g hgP x)).finrank_range_le_quotient_add_map
    (F.hatSubspace F.W)
  have hm := Submodule.finrank_mono
    (F.conjugate_center_displacement_hyperplane hn L hL hcenter B g hgP hgH x)
  rw [F.finrank_quotient_hat_centralizer hn hcenter B] at hb
  rw [F.finrank_hat_plane hn hcenter] at hm
  omega

/-- The same estimate for the generator rank of the actual moved subgroup. -/
theorem conjugate_center_moved_rank_le_two (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (x : conjugate F.ZU g) :
    Group.rank (F.uhatMoved (F.conjugateCenterActor hn L hL g hgP x)) ≤ 2 := by
  let h := F.conjugateCenterActor hn L hL g hgP x
  let e : F.uhatMoved h ≃ (F.uhatDisplacement h).range := {
    toFun q := ⟨Additive.ofMul q, (F.mem_uhatMoved_iff h q).mp q.property⟩
    invFun q := ⟨q.val.toMul, (F.mem_uhatMoved_iff h q.val.toMul).mpr q.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc : Nat.card (F.uhatMoved h) ≤ 2 ^ 2 := by
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by omega)
      (F.conjugate_center_displacement_rank_le_two hn L hL hcenter B g hgP hgH x)
  let : IsElementaryAbelian 2 (F.uhatMoved h) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun q =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 F.Uhat) q.val)) }
  exact IsElementaryAbelian.rank_le_of_card_le (F.uhatMoved h) hc

/-- Application to the existing 12.8.10 intersection and kernel assembly:
the extra centralizer-center premise is now discharged. Only the explicit
preceding 12.8.3–9 premises remain, with their original relative subgroups,
quotients, and actions. The moved-rank clause is supplied separately by
`conjugate_center_moved_rank_le_two`. -/
theorem center_and_kernel_calculations_of_commutator_form
    (F : InvariantFlag T V n) [Finite G] [IsMulCommutative V]
    [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hUT : F.U ≤ T) (hI : F.Gi 2 ≤ normalizer (F.I₂ L : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hgen : F.I₂ L = F.U ⊔ conjugate F.U g)
    (e : (F.I₂ L ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))
    (hfix : ∀ a ∈ F.U, a ∉ F.W → ∀ z ∈ (F.I₂ L).pCoreIn 2,
      ⁅z, a⁆ ∈ F.E g → z ∈ F.W)
    (hhat : F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g)
    (htilde : F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = F.E g)
    (hcore : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H)
    (B : F.UhatCommutatorForm hcomm) :
    F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ∧
    F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L) ∧
    (F.Vi 1 < F.ZU ⊓ conjugate F.U g → sylowOmega T ⊓ centerIn (F.I₂ L) ≠ ⊥) ∧
    ⁅F.W, conjugate F.ZU g⁆ ≤ F.ZU ⊔ F.Vi 2 ∧
    (conjugate F.ZU g ≤ F.U →
      F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
      ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
        ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
    (conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype =
        conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype ∧
      conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype =
        conjugate F.ZU g ⊓ QH F.H ∧
      conjugate F.ZU g ⊓ QH F.H = conjugate F.ZU g ⊓ F.U ∧
      conjugate F.ZU g ⊓ F.U =
        (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g ∧
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g =
        centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ∧
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ≤ F.U) := by
  exact F.center_and_kernel_calculations_of_centralizer_center hn L hL hcenter hcomm
    hUT hI g hgP hgH hgen e hfix hhat htilde hcore (F.plane_centralizer_center B)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
