module

public import Theory.SpecificGroups.Suzuki.SchurEightUpper.LocalSetup
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# The actual mixed commutator pairing for Sz(8)

The marked roots are elements of the original matrix subgroup over `GF(8)`.
In its universal central cover, `D = [P,P]` is the full preimage of the root
center. Since `D` is abelian, changing the central coordinate of the first
lift does not affect its commutator with a center lift. Centrality of
`J = [P,D]` then makes this mixed commutator additive in both coordinates.

Conjugating by lifts of the literal split torus gives weights one and five.
Hall–Witt gives Jacobi, using the root commutator `x*y^4 + y*x^4` and the
fact that inversion preserves a root's first coordinate. Finally, every
commutator generating the actual `J` has this coordinate description.
Together these facts construct `PairingData` without extra hypotheses.

Sources: Huppert–Blackburn III, XI.3.1–3.3, in the upper-triangular matrix
convention of `BenderSuzuki.MatrixGroups.Suzuki`, and the Hall–Witt identity.
The multiplier statement is GLS3 §6.1 and Aschbacher–Smith I.1.3(5),
printed p.407/PDF p.418 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative

namespace BenderSuzuki.MatrixGroups.SchurCover.EightLocal
local instance : Fact (0 < (1 : ℕ)) := ⟨by decide⟩

namespace MixedPairing

/-- The marked root in the actual matrix subgroup, with its two field coordinates. -/
abbrev root (x z : Field) : SuzukiMatrixGroup 1 := (Family.rootPoint 1 x z).val

/-- The marked root belongs to the standard root subgroup. -/
lemma root_mem (x z : Field) : root x z ∈ SuzukiRootSubgroup 1 :=
  (Family.rootPoint 1 x z).property

/-- The zero coordinates mark the identity. -/
lemma root_zero : root 0 0 = 1 := congrArg Subtype.val (Family.rootPoint_zero 1)

/-- Huppert XI.3.1 in the actual Sz(8) subgroup: the cross-term is `x * y^4`. -/
lemma root_mul (x z y w : Field) : root x z * root y w = root (x+y) (z+w+x*y^4) := by
  have h := congrArg Subtype.val (Family.rootPoint_mul 1 (by decide) x z y w)
  simpa only [root, Subgroup.coe_mul, suzukiTits_apply, Nat.reduceAdd, Nat.reducePow] using h

/-- Every element of the standard root subgroup has marked coordinates. -/
lemma root_exists {g : SuzukiMatrixGroup 1} (hg : g ∈ SuzukiRootSubgroup 1) :
    ∃ x z, g = root x z := by
  obtain ⟨x,z,h⟩ := Family.rootPoint_surjective 1 ⟨g,hg⟩
  exact ⟨x,z,congrArg Subtype.val h⟩

private lemma derived_base_iff (g : SuzukiMatrixGroup 1) :
    g ∈ ⁅SuzukiRootSubgroup 1, SuzukiRootSubgroup 1⁆ ↔ ∃ z, g = root 0 z := by
  rw [← map_subtype_commutator]
  constructor
  · rintro ⟨u,hu,rfl⟩
    rw [← Family.rootCoordinate_ker 1 (by decide)] at hu
    obtain ⟨x,z,rfl⟩ := Family.rootPoint_surjective 1 u
    have hx : x = 0 := congrArg Multiplicative.toAdd hu
    exact ⟨z,hx ▸ rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨Family.rootPoint 1 0 z, ?_, rfl⟩
    rw [← Family.rootCoordinate_ker 1 (by decide)]
    rfl

/-- Transfer and the root-derived image identify every center lift with an element of `D`. -/
lemma derived_iff (g : CoverGroup 1) :
    g ∈ DerivedPreimage ↔ ∃ z, projection g = root 0 z := by
  have he : DerivedPreimage =
      (⁅SuzukiRootSubgroup 1,SuzukiRootSubgroup 1⁆).comap projection := by
    rw [← derived_map, comap_map_eq_self kernel_le_derived]
  rw [he, mem_comap, derived_base_iff]

/-- Inversion preserves the first coordinate in characteristic two. -/
lemma root_inv (x z : Field) : (root x z)⁻¹ = root x (z+x*x^4) := by
  apply Subtype.ext
  simpa only [root, Family.rootPoint, Subgroup.coe_inv, suzukiTits_apply, Nat.reduceAdd, Nat.reducePow] using
    External.suzukiRootGL_inv 1 (suzukiTits 1) (suzukiTits_sq 1)
      (suzukiTits_apply 1) x z

/-- The marked root commutator has central coordinate `x * y^4 + y * x^4`. -/
lemma root_commutator (x z y w : Field) :
    ⁅root x z, root y w⁆ = root 0 (x*y^4+y*x^4) := by
  rw [commutatorElement_def, root_inv, root_inv, root_mul, root_mul, root_mul]
  congr 1 <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod]

private lemma conj_center (g z : CoverGroup 1) (hz : z ∈ center (CoverGroup 1)) :
    g*z*g⁻¹ = z := by
  rw [mem_center_iff.mp hz g, mul_inv_cancel_right]

private lemma comm_mem {a b : CoverGroup 1} (ha : a ∈ RootPreimage) (hb : b ∈ DerivedPreimage) :
    ⁅a,b⁆ ∈ ThirdCommutator := commutator_mem_commutator ha hb

private lemma comm_central {a b : CoverGroup 1} (ha : a ∈ RootPreimage) (hb : b ∈ DerivedPreimage) :
    ⁅a,b⁆ ∈ center (CoverGroup 1) := third_le_center (comm_mem ha hb)

private lemma preimage_mem {a : CoverGroup 1} {x z : Field} (ha : projection a = root x z) :
    a ∈ RootPreimage := by
  change projection a ∈ SuzukiRootSubgroup 1
  rw [ha]
  exact root_mem x z

private lemma comm_eq_same_first {a a' b : CoverGroup 1} {x z z' : Field}
    (ha : projection a = root x z) (ha' : projection a' = root x z')
    (hb : b ∈ DerivedPreimage) : ⁅a,b⁆ = ⁅a',b⁆ := by
  have hd : a*a'⁻¹ ∈ DerivedPreimage := by
    apply (derived_iff _).mpr
    refine ⟨z+z', ?_⟩
    rw [map_mul, map_inv, ha, ha', root_inv, root_mul]
    congr 1
    · exact CharTwo.add_self_eq_zero x
    · simp [add_assoc, CharTwo.add_self_eq_zero]
  have hc : ⁅a*a'⁻¹,b⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact congrArg Subtype.val (mul_comm (⟨a*a'⁻¹,hd⟩ : DerivedPreimage) ⟨b,hb⟩)
  calc
    ⁅a,b⁆ = ⁅(a*a'⁻¹)*a',b⁆ := by simp
    _ = (a*a'⁻¹)*⁅a',b⁆*(a*a'⁻¹)⁻¹*⁅a*a'⁻¹,b⁆ :=
      commutatorElement_mul_left_eq_conj_mul _ _ _
    _ = ⁅a',b⁆ := by
      rw [conj_center _ _ (comm_central (preimage_mem ha') hb), hc]
      exact mul_one _

private def lift (x z : Field) : CoverGroup 1 :=
  ((PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)).surjective (root x z)).choose

private lemma lift_image (x z : Field) : projection (lift x z) = root x z :=
  ((PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)).surjective (root x z)).choose_spec

private lemma lift_mem (x z : Field) : lift x z ∈ RootPreimage := preimage_mem (lift_image x z)

private lemma center_lift_mem (z : Field) : lift 0 z ∈ DerivedPreimage :=
  (derived_iff _).mpr ⟨z,lift_image 0 z⟩

private def value (x z : Field) : Additive ThirdCommutator :=
  Additive.ofMul ⟨⁅lift x 0,lift 0 z⁆, comm_mem (lift_mem x 0) (center_lift_mem z)⟩

private lemma value_formula (x y z : Field) (a b : CoverGroup 1)
    (ha : projection a = root x y) (hb : projection b = root 0 z) :
    ((value x z).toMul : CoverGroup 1) = ⁅a,b⁆ := by
  change ⁅lift x 0,lift 0 z⁆ = ⁅a,b⁆
  rw [comm_eq_same_first (lift_image x 0) ha (center_lift_mem z)]
  exact CentralExtension.commutator_eq_of_image_eq projection
    (PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)).ker_le_center
    rfl ((lift_image 0 z).trans hb.symm)

private lemma value_zero_right (x : Field) : value x 0 = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [value_formula x 0 0 (lift x 0) 1 (lift_image x 0) (by rw [map_one, root_zero])]
  simp

private lemma value_zero_left (z : Field) : value 0 z = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [value_formula 0 0 z 1 (lift 0 z) (by rw [map_one, root_zero]) (lift_image 0 z)]
  simp

private lemma value_add_right (x z w : Field) : value x (z+w) = value x z + value x w := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((value x (z+w)).toMul : CoverGroup 1) = ⁅lift x 0,lift 0 z⁆ * ⁅lift x 0,lift 0 w⁆
  rw [value_formula x 0 (z+w) (lift x 0) (lift 0 z*lift 0 w) (lift_image x 0)
    (by simp only [map_mul, lift_image, root_mul, zero_mul, add_zero]),
    commutatorElement_mul_right_eq_mul_conj]
  rw [mul_assoc, mul_assoc, ← mul_assoc (lift 0 z),
    conj_center _ _ (comm_central (lift_mem x 0) (center_lift_mem w))]

private lemma value_add_left (x y z : Field) : value (x+y) z = value x z + value y z := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((value (x+y) z).toMul : CoverGroup 1) = ⁅lift x 0,lift 0 z⁆ * ⁅lift y 0,lift 0 z⁆
  rw [value_formula (x+y) (x*y^4) z (lift x 0*lift y 0) (lift 0 z)
    (by simp only [map_mul, lift_image, root_mul, zero_add]) (lift_image 0 z),
    commutatorElement_mul_left_eq_conj_mul,
    conj_center _ _ (comm_central (lift_mem y 0) (center_lift_mem z))]
  exact (mem_center_iff.mp (comm_central (lift_mem y 0) (center_lift_mem z)) _).symm

/-- The additive mixed commutator pairing with values in the literal third commutator. -/
def pairing : Field →+ (Field →+ Additive ThirdCommutator) where
  toFun x := { toFun := value x, map_zero' := value_zero_right x, map_add' := value_add_right x }
  map_zero' := AddMonoidHom.ext value_zero_left
  map_add' x y := AddMonoidHom.ext (value_add_left x y)

/-- The pairing is the literal commutator for arbitrary lifts.
The second coordinate of the first root is unrestricted because `D` is abelian. -/
lemma pairing_formula (x y z : Field) (a b : CoverGroup 1)
    (ha : projection a = root x y) (hb : projection b = root 0 z) :
    ((pairing x z).toMul : CoverGroup 1) = ⁅a,b⁆ := value_formula x y z a b ha hb

/-- The literal split torus acts with weights one and five on the two root coordinates. -/
lemma torus_conj (t : Fieldˣ) (x z : Field) :
    Family.torusPoint 1 (by decide) t * root x z * (Family.torusPoint 1 (by decide) t)⁻¹ =
      root ((t : Field)*x) ((t : Field)^5*z) := by
  have h := Family.torusPoint_conj 1 (by decide) t x z
  have ht : (t : Field) * suzukiTits 1 t = (t : Field)^5 := by
    rw [suzukiTits_apply]
    exact (pow_succ' (t : Field) 4).symm
  simpa only [root, ht] using h

/-- Lifting the split torus proves invariance, since it fixes the central subgroup `J` pointwise. -/
lemma invariant : EightPairing.TorusInvariant pairing := by
  intro t x z
  have hs : Function.Surjective projection :=
    (PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)).surjective
  let g : CoverGroup 1 := (hs (Family.torusPoint 1 (by decide) t)).choose
  have hg : projection g = Family.torusPoint 1 (by decide) t :=
    (hs (Family.torusPoint 1 (by decide) t)).choose_spec
  have ha : projection (g*lift x 0*g⁻¹) = root ((t : Field)*x) 0 := by
    simp only [map_mul, map_inv, hg, lift_image, torus_conj, mul_zero]
  have hb : projection (g*lift 0 z*g⁻¹) = root 0 ((t : Field)^5*z) := by
    simp only [map_mul, map_inv, hg, lift_image, torus_conj, mul_zero]
  have hl := pairing_formula ((t : Field)*x) 0 ((t : Field)^5*z)
    (g*lift x 0*g⁻¹) (g*lift 0 z*g⁻¹) ha hb
  have hr := pairing_formula x 0 z (lift x 0) (lift 0 z) (lift_image x 0) (lift_image 0 z)
  have hc : ⁅g*lift x 0*g⁻¹,g*lift 0 z*g⁻¹⁆ = ⁅lift x 0,lift 0 z⁆ :=
    (conjugate_commutatorElement (lift x 0) (lift 0 z) g).symm.trans
      (conj_center g _ (comm_central (lift_mem x 0) (center_lift_mem z)))
  apply Additive.toMul.injective
  exact Subtype.ext (hl.trans (hc.trans hr.symm))

private lemma central_hall_witt {G : Type*} [Group G] (a b c : G)
    (h1 : ⁅a,⁅b⁻¹,c⁆⁆ ∈ center G)
    (h2 : ⁅b,⁅c⁻¹,a⁆⁆ ∈ center G)
    (h3 : ⁅c,⁅a⁻¹,b⁆⁆ ∈ center G) :
    ⁅a,⁅b⁻¹,c⁆⁆ * ⁅b,⁅c⁻¹,a⁆⁆ * ⁅c,⁅a⁻¹,b⁆⁆ = 1 := by
  have hc (g z : G) (hz : z ∈ center G) : g*z*g⁻¹ = z := by
    rw [mem_center_iff.mp hz g, mul_inv_cancel_right]
  have h : (b*⁅a,⁅b⁻¹,c⁆⁆*b⁻¹)*(c*⁅b,⁅c⁻¹,a⁆⁆*c⁻¹)*(a*⁅c,⁅a⁻¹,b⁆⁆*a⁻¹) = 1 := by
    simpa only [mul_assoc] using conj_commutatorElement_right_commutatorElement_mul a b c
  rwa [hc _ _ h1, hc _ _ h2, hc _ _ h3] at h

/-- Hall–Witt gives the additive Jacobi identity with the actual root commutator polynomial. -/
lemma jacobi : EightPairing.Jacobi pairing := by
  intro x y z
  let a := lift x 0
  let b := lift y 0
  let c := lift z 0
  have himage (u v : Field) : projection ⁅(lift u 0)⁻¹,lift v 0⁆ =
      root 0 (u*v^4+v*u^4) := by
    rw [map_commutatorElement, map_inv, lift_image, lift_image, root_inv, root_commutator]
  have h1 := pairing_formula x 0 (y*z^4+z*y^4) a ⁅b⁻¹,c⁆ (lift_image x 0) (himage y z)
  have h2 := pairing_formula y 0 (z*x^4+x*z^4) b ⁅c⁻¹,a⁆ (lift_image y 0) (himage z x)
  have h3 := pairing_formula z 0 (x*y^4+y*x^4) c ⁅a⁻¹,b⁆ (lift_image z 0) (himage x y)
  have hc (u v w : Field) : ⁅lift u 0,⁅(lift v 0)⁻¹,lift w 0⁆⁆ ∈ center (CoverGroup 1) :=
    comm_central (lift_mem u 0) ((derived_iff _).mpr ⟨_,himage v w⟩)
  have hh := central_hall_witt a b c (hc x y z) (hc y z x) (hc z x y)
  have hp := congrArg₂ (fun u v : CoverGroup 1 => u*v)
    (congrArg₂ (fun u v : CoverGroup 1 => u*v) h1 h2) h3
  apply Additive.toMul.injective
  exact Subtype.ext (hp.trans hh)

/-- Every generator of the actual subgroup `[P,D]` is a value of the pairing. -/
lemma generates : AddSubgroup.closure {v | ∃ x z, pairing x z = v} = ⊤ := by
  let S : AddSubgroup (Additive ThirdCommutator) :=
    AddSubgroup.closure {v | ∃ x z, pairing x z = v}
  let T : Subgroup ThirdCommutator := Subgroup.toAddSubgroup.symm S
  have hle : ThirdCommutator ≤ T.map ThirdCommutator.subtype := by
    apply commutator_le.mpr
    intro a ha d hd
    obtain ⟨x,y,hxy⟩ := root_exists ha
    obtain ⟨z,hz⟩ := (derived_iff d).mp hd
    refine ⟨(pairing x z).toMul, ?_, pairing_formula x y z a d hxy hz⟩
    change pairing x z ∈ S
    exact AddSubgroup.subset_closure ⟨x,z,rfl⟩
  apply top_unique
  intro v _
  have hv : ∃ w : ThirdCommutator, w ∈ T ∧ (w : CoverGroup 1) = (v.toMul : CoverGroup 1) :=
    hle v.toMul.property
  have he : hv.choose = v.toMul := Subtype.ext hv.choose_spec.2
  change v.toMul ∈ T
  exact he ▸ hv.choose_spec.1

end MixedPairing

/-- The unconditional mixed commutator data for the actual universal cover of Sz(8). -/
@[expose] def mixedPairingData : PairingData where
  pairing := MixedPairing.pairing
  invariant := MixedPairing.invariant
  jacobi := MixedPairing.jacobi
  generates := MixedPairing.generates

/-- The pairing premise of the exceptional Suzuki upper-bound assembly is inhabited. -/
theorem nonempty_pairingData : Nonempty PairingData := ⟨mixedPairingData⟩

/-- The constructed data has the marked commutator formula for every choice of lifts. -/
theorem mixedPairingData_commutator (x y z : Field) (a b : CoverGroup 1)
    (ha : projection a = MixedPairing.root x y) (hb : projection b = MixedPairing.root 0 z) :
    ((mixedPairingData.pairing x z).toMul : CoverGroup 1) = ⁅a, b⁆ :=
  MixedPairing.pairing_formula x y z a b ha hb

end BenderSuzuki.MatrixGroups.SchurCover.EightLocal

end
