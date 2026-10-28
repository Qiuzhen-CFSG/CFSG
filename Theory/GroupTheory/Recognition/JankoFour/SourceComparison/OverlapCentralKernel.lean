module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCharacteristic
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneCentral
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerLift
import all Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CentralTwist

/-!
# The central kernel of the original overlap automorphism action

A homomorphism from the native outer hexad group to an abelian group kills
its natural four-dimensional radical: two explicit symplectic commutators
supply every vector as a sum of displacements. Consequently its binary
characters are trivial or sign. For the actual overlap I, [O2(I),A]=Q
and the odd order of A make every binary character factor through the
literal I/(Q A), so I likewise has only one nontrivial binary character.

An automorphism fixing Q pointwise displaces every element into C_H(Q)=Z(H).
This displacement is a homomorphism into the original center of order two.
The restriction of the constructed plane twist is nonidentity, since the
hexad image of order 11520 cannot lie in the inner M22 of order 443520.
It therefore accounts for the entire pointwise core-fixing kernel.
Extraspecial commutator duality then identifies the kernel on Q/Z(Q):
it consists of inner automorphisms through Q and that same central twist.
All corrections retain the marked involution and original embeddings.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
The internal CentralTwist import identifies its original even subgroup
with the inverse image of Inn(M22), without changing that module's API.
The action of an arbitrary overlap automorphism on Q/Z(Q), alignment of
the local maps, and the full edge-reversal equation remain necessary.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu MathieuCode
open scoped Pointwise

namespace OverlapCohomology
open Matrix
open Representation.OneCohomology.SymplecticFour
open Sporadic.Mathieu.M22ChapterH.Hexad.Action

private theorem native_hom_kills_radical {C : Type*} [CommGroup C]
    (f : Outer →* C) (n : pCore 2 Outer) : f n.val = 1 := by
  let v : V := (nativeCoordinates n).toAdd
  have hv : ∃ w : V, v = (BinaryField.generatorMatrix 0 *ᵥ w - w) +
      (BinaryField.generatorMatrix 1 *ᵥ w - w) := by
    have cert : ∀ v : V, ∃ w : V, v = (BinaryField.generatorMatrix 0 *ᵥ w - w) +
        (BinaryField.generatorMatrix 1 *ᵥ w - w) := by decide +kernel
    exact cert v
  obtain ⟨w,hw⟩ := hv
  let vec (u : V) : Outer := (nativeCoordinates.symm (Multiplicative.ofAdd u)).val
  have hmul (u v : V) : vec (u + v) = vec u * vec v := by
    exact congrArg Subtype.val (nativeCoordinates.symm.map_mul _ _)
  have hsub (u v : V) : vec (u - v) = vec u * (vec v)⁻¹ := by
    exact congrArg Subtype.val (nativeCoordinates.symm.map_div _ _)
  have hgen (j : Fin 3) : f (vec (BinaryField.generatorMatrix j *ᵥ w - w)) = 1 := by
    obtain ⟨g,hg⟩ := nativeActor_surjective (BinaryField.generator j).val
    rw [hsub]
    have ha : vec (BinaryField.generatorMatrix j *ᵥ w) = g * vec w * g⁻¹ := by
      have he := nativeCoordinates_conjugation_symm g w
      change vec (natural (nativeActor g) w) = _ at he
      rw [hg] at he
      change vec ((BinaryField.generator j).val.val *ᵥ w) = _ at he
      rwa [BinaryField.generator_val] at he
    rw [ha,map_mul,map_mul,map_mul,map_inv,map_inv]
    rw [mul_comm (f g) (f (vec w))]
    group
  have hn : vec v = n.val := by
    change (nativeCoordinates.symm (Multiplicative.ofAdd (nativeCoordinates n).toAdd)).val = _
    rw [ofAdd_toAdd,MulEquiv.symm_apply_apply]
  rw [←hn,hw,hmul,map_mul,hgen,hgen,one_mul]

private theorem perm_sign_cases (f : Equiv.Perm (Fin 6) →* ℤˣ) :
    f = 1 ∨ f = Equiv.Perm.sign := by
  by_cases hf : f = 1
  · exact Or.inl hf
  · right
    apply Equiv.Perm.eq_sign_of_surjective_hom
    have hn : ∃ x, f x ≠ 1 := by
      by_contra hn
      exact hf (MonoidHom.ext fun x => by simpa using not_exists.mp hn x)
    obtain ⟨x,hx⟩ := hn
    intro y
    rcases Int.units_eq_one_or y with rfl | rfl
    · exact ⟨1,map_one _⟩
    · exact ⟨x,(Int.units_eq_one_or (f x)).resolve_left hx⟩

/-- A sign character on the genuine native outer hexad group. -/
noncomputable def nativeSign : Outer →* ℤˣ :=
  Equiv.Perm.sign.comp
    (HexadSymplecticComparison.PolarModel.sixToSymplectic.symm.toMonoidHom.comp nativeActor)

/-- Its abelian characters of order two are precisely the trivial character and sign. -/
theorem native_sign_hom_cases (f : Outer →* ℤˣ) : f = 1 ∨ f = nativeSign := by
  have hk : nativeActor.ker ≤ f.ker := by
    rw [nativeActor_ker]
    intro x hx
    exact native_hom_kills_radical f ⟨x,hx⟩
  let q : Sp →* ℤˣ := nativeActor.liftOfSurjective nativeActor_surjective ⟨f,hk⟩
  have hq (x : Outer) : q (nativeActor x) = f x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  let r := q.comp HexadSymplecticComparison.PolarModel.sixToSymplectic.toMonoidHom
  rcases perm_sign_cases r with hr | hr
  · left
    apply MonoidHom.ext
    intro x
    have he := DFunLike.congr_fun hr
      (HexadSymplecticComparison.PolarModel.sixToSymplectic.symm (nativeActor x))
    change q (HexadSymplecticComparison.PolarModel.sixToSymplectic
      (HexadSymplecticComparison.PolarModel.sixToSymplectic.symm (nativeActor x))) = 1 at he
    rwa [MulEquiv.apply_symm_apply,hq] at he
  · right
    apply MonoidHom.ext
    intro x
    have he := DFunLike.congr_fun hr
      (HexadSymplecticComparison.PolarModel.sixToSymplectic.symm (nativeActor x))
    change q (HexadSymplecticComparison.PolarModel.sixToSymplectic
      (HexadSymplecticComparison.PolarModel.sixToSymplectic.symm (nativeActor x))) = _ at he
    rwa [MulEquiv.apply_symm_apply,hq] at he
end OverlapCohomology

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

private theorem overlap_sign_kills_cubicLift (f : PlaneOverlap a →* ℤˣ) :
    (twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a) ≤ f.ker := by
  let I := PlaneOverlap a
  have hQ : (core z).subgroupOf I ≤ f.ker := by
    rw [←overlap_core_eq_commutator a]
    exact (commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker f)
  have hA : (cubicSylowImage a.e a.X).subgroupOf I ≤ f.ker := by
    intro x hx
    have h3 : x^3=1 := by
      have he : (⟨x.val,hx⟩ : cubicSylowImage a.e a.X)^Nat.card (cubicSylowImage a.e a.X)=1 := pow_card_eq_one'
      rw [cubicSylowImage_card h a.e a.X] at he
      exact Subtype.ext (congrArg (fun t : cubicSylowImage a.e a.X => t.val) he)
    change f x = 1
    rcases Int.units_eq_one_or (f x) with he | he
    · exact he
    · have hh : (f x)^3=1 := by rw [←map_pow,h3,map_one]
      norm_num [he] at hh
  have hl : cubicSylowImage a.e a.X ≤ I := by
    apply le_trans ?_ (overlap_cubicLift_le a)
    rw [←cubicLift_eq_twoThreeCore h a.e,←core_sup_cubicSylow a.e h a.X]
    exact le_sup_right
  have hs : (twoThreeCore (centralizer z)).subgroupOf I =
      (core z).subgroupOf I ⊔ (cubicSylowImage a.e a.X).subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (overlap_cubicLift_le a),Subgroup.map_sup,
      map_subgroupOf_eq_of_le ((core_le_twoThreeCore h).trans (overlap_cubicLift_le a)),
      map_subgroupOf_eq_of_le hl,core_sup_cubicSylow a.e h a.X,cubicLift_eq_twoThreeCore h a.e]
  rw [hs]
  exact sup_le hQ hA

/-- Sign of the same original cubic quotient, using its constructed native coordinates. -/
noncomputable def overlapSign : PlaneOverlap a →* ℤˣ :=
  OverlapCohomology.nativeSign.comp ((OverlapCohomology.originalEquiv h a.P).toMonoidHom.comp
    (QuotientGroup.mk' ((twoThreeCore (centralizer z)).subgroupOf (PlaneOverlap a))))

/-- The original overlap has just one nontrivial binary character. -/
theorem overlap_sign_hom_cases (f : PlaneOverlap a →* ℤˣ) : f = 1 ∨ f = overlapSign a := by
  let q := QuotientGroup.lift _ f (overlap_sign_kills_cubicLift a f)
  let r := q.comp (OverlapCohomology.originalEquiv h a.P).symm.toMonoidHom
  rcases OverlapCohomology.native_sign_hom_cases r with hr | hr
  · left
    apply MonoidHom.ext
    intro x
    have he := DFunLike.congr_fun hr (OverlapCohomology.originalEquiv h a.P (QuotientGroup.mk' _ x))
    change q ((OverlapCohomology.originalEquiv h a.P).symm
      (OverlapCohomology.originalEquiv h a.P (QuotientGroup.mk' _ x))) = 1 at he
    rwa [MulEquiv.symm_apply_apply] at he
  · right
    apply MonoidHom.ext
    intro x
    have he := DFunLike.congr_fun hr (OverlapCohomology.originalEquiv h a.P (QuotientGroup.mk' _ x))
    change q ((OverlapCohomology.originalEquiv h a.P).symm
      (OverlapCohomology.originalEquiv h a.P (QuotientGroup.mk' _ x))) = _ at he
    rwa [MulEquiv.symm_apply_apply] at he

/-- Restrict the actual plane central twist to the literal overlap. -/
noncomputable def overlapPlaneTwist : MulAut (PlaneOverlap a) :=
  (PlaneOverlap a).equivMapOfInjective (planeTwist h a.e).toMonoidHom
    (planeTwist h a.e).injective |>.trans
      (MulEquiv.subgroupCongr (planeTwist_point_overlap h a))

theorem overlapPlaneTwist_coe (x : PlaneOverlap a) :
    (overlapPlaneTwist a x).val = planeTwist h a.e x.val := rfl

theorem overlapPlaneTwist_fixes_core (x : PlaneOverlap a) (hx : x.val ∈ core z) :
    overlapPlaneTwist a x = x :=
  Subtype.ext (planeTwist_fixes_core h a.e ⟨x.val,hx⟩)

theorem overlapPlaneTwist_sq : overlapPlaneTwist a ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f : MulAut (centralizer z) => f x.val) (planeTwist_sq h a.e)

/-- The plane twist is nontrivial even on I, whose image has order 11520
and hence cannot lie inside the inner M22 group of order 443520. -/
theorem overlapPlaneTwist_ne_one : overlapPlaneTwist a ≠ 1 := by
  intro he
  have hm : planeMarker (z := z) ≠ 1 := by
    intro hz
    have ho := h.involution
    have hz1 : z=1 := congrArg Subtype.val hz
    rw [hz1,orderOf_one] at ho
    contradiction
  have hev (x : PlaneOverlap a) : x.val ∈ planeEven a.e := by
    by_contra hx
    have hf := congrArg (fun f : MulAut (PlaneOverlap a) => (f x).val) he
    change planeTwist h a.e x.val = x.val at hf
    rw [planeTwist_apply,if_neg hx] at hf
    exact hm (mul_left_cancel (hf.trans (mul_one x.val).symm))
  have hle : designStabilizer a.P.hexad ≤ MulAut.innerSubgroup M22 := by
    intro y hy
    obtain ⟨x,hx⟩ := overlapProjection_surjective a.P.cubic _ _ a.P.overlap ⟨y,hy⟩
    have hh := hev x
    change CubicLift.projection a.e x.val ∈ MulAut.innerSubgroup M22 at hh
    have hx' : CubicLift.projection a.P.cubic x.val = y := congrArg Subtype.val hx
    rw [a.cubic_eq] at hx'
    rwa [hx'] at hh
  have hc : Nat.card (MulAut.innerSubgroup M22) = 443520 :=
    (Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).toEquiv).symm.trans m22_order
  have hd := card_dvd_of_le hle
  rw [native_design_hex_card a.P.hexad_mem,hc] at hd
  norm_num at hd

/-- An overlap automorphism fixing Q pointwise has displacement in the
original marked center of H, before any quotient is taken. -/
theorem overlap_core_fixer_displacement (f : MulAut (PlaneOverlap a))
    (hf : ∀ x : PlaneOverlap a, x.val ∈ core z → f x = x) (x : PlaneOverlap a) :
    (f x).val * x.val⁻¹ ∈ center (centralizer z) := by
  have hQI : core z ≤ PlaneOverlap a :=
    (core_le_twoThreeCore h).trans (overlap_cubicLift_le a)
  have ha : (MulAut.conjNormal (f x).val : MulAut (core z)) = MulAut.conjNormal x.val := by
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    let y : PlaneOverlap a := ⟨q.val,hQI q.property⟩
    have hy : f y = y := hf y q.property
    have hc := hf (x*y*x⁻¹)
      ((inferInstance : (core z).Normal).conj_mem q.val q.property x.val)
    rw [map_mul,map_mul,map_inv,hy] at hc
    change (f x).val*q.val*(f x).val⁻¹ = x.val*q.val*x.val⁻¹
    exact congrArg Subtype.val hc
  rw [←planeCoreAction_ker h]
  change MulAut.conjNormal ((f x).val*x.val⁻¹) = 1
  rw [map_mul,map_inv,ha,mul_inv_cancel]

/-- The central displacement is a homomorphism on the original overlap. -/
noncomputable def overlapCentralDisplacement (f : MulAut (PlaneOverlap a))
    (hf : ∀ x : PlaneOverlap a, x.val ∈ core z → f x = x) :
    PlaneOverlap a →* center (centralizer z) where
  toFun x := ⟨(f x).val*x.val⁻¹,overlap_core_fixer_displacement a f hf x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (f (x*y)).val*(x*y).val⁻¹ =
      ((f x).val*x.val⁻¹)*((f y).val*y.val⁻¹)
    have hc := mem_center_iff.mp (overlap_core_fixer_displacement a f hf y) x.val⁻¹
    simp only [map_mul,coe_mul,mul_inv_rev]
    calc
      _ = (f x).val * (((f y).val * y.val⁻¹) * x.val⁻¹) := by group
      _ = (f x).val * (x.val⁻¹ * ((f y).val * y.val⁻¹)) := by rw [←hc]
      _ = _ := by group

/-- Central displacement detects the original automorphism without losing z. -/
theorem overlapCentralDisplacement_injective
    (f g : MulAut (PlaneOverlap a))
    (hf : ∀ x : PlaneOverlap a, x.val ∈ core z → f x = x)
    (hg : ∀ x : PlaneOverlap a, x.val ∈ core z → g x = x)
    (he : overlapCentralDisplacement a f hf = overlapCentralDisplacement a g hg) : f = g := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact mul_right_cancel (congrArg Subtype.val (DFunLike.congr_fun he x))

/-- The pointwise core-fixing kernel consists precisely of identity and
restriction of the constructed plane central twist. -/
theorem overlap_core_fixer_cases (f : MulAut (PlaneOverlap a))
    (hf : ∀ x : PlaneOverlap a, x.val ∈ core z → f x = x) :
    f = 1 ∨ f = overlapPlaneTwist a := by
  let E : center (centralizer z) ≃* ℤˣ :=
    mulEquivOfPrimeCardEq (centralizer_center_card h) (by rw [Nat.card_eq_fintype_card,Fintype.card_units_int])
  let df := overlapCentralDisplacement a f hf
  let dt := overlapCentralDisplacement a (overlapPlaneTwist a) (overlapPlaneTwist_fixes_core a)
  have ht : E.toMonoidHom.comp dt ≠ 1 := by
    intro he
    apply overlapPlaneTwist_ne_one a
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have hh := DFunLike.congr_fun he x
    change E (dt x) = 1 at hh
    have hh' : dt x = 1 := E.map_eq_one_iff.mp hh
    exact mul_inv_eq_one.mp (congrArg Subtype.val hh')
  have hts : E.toMonoidHom.comp dt = overlapSign a :=
    (overlap_sign_hom_cases a _).resolve_left ht
  rcases overlap_sign_hom_cases a (E.toMonoidHom.comp df) with hh | hh
  · left
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have hx := DFunLike.congr_fun hh x
    change E (df x) = 1 at hx
    exact mul_inv_eq_one.mp (congrArg Subtype.val (E.map_eq_one_iff.mp hx))
  · right
    apply overlapCentralDisplacement_injective a f (overlapPlaneTwist a) hf
      (overlapPlaneTwist_fixes_core a)
    apply MonoidHom.ext
    intro x
    apply E.injective
    exact DFunLike.congr_fun (hh.trans hts.symm) x

/-- The restriction to the original extraspecial group, using its proved
characteristic placement in I. -/
noncomputable def overlapCoreAut : MulAut (PlaneOverlap a) →* MulAut (core z) :=
  (MulAut.congr (subgroupOfEquivOfLe
    ((core_le_twoThreeCore h).trans (overlap_cubicLift_le a)))).toMonoidHom.comp
    (MulAut.characteristic ((core z).subgroupOf (PlaneOverlap a)))

theorem overlapCoreAut_coe (f : MulAut (PlaneOverlap a)) (q : core z) :
    (overlapCoreAut a f q).val =
      (f ⟨q.val,(core_le_twoThreeCore h).trans (overlap_cubicLift_le a) q.property⟩).val := rfl

/-- Innerness on Q/Z(Q) lifts to an actual inner correction through Q;
the only residual overlap automorphism is the plane central twist. -/
theorem overlap_core_central_displacement_cases (f : MulAut (PlaneOverlap a))
    (hf : ∀ x : PlaneOverlap a, x.val ∈ core z →
      (f x).val * x.val⁻¹ ∈ center (centralizer z)) :
    ∃ q : core z,
      f = MulAut.conj (⟨q.val,(core_le_twoThreeCore h).trans
        (overlap_cubicLift_le a) q.property⟩ : PlaneOverlap a) ∨
      f = MulAut.conj (⟨q.val,(core_le_twoThreeCore h).trans
        (overlap_cubicLift_le a) q.property⟩ : PlaneOverlap a) * overlapPlaneTwist a := by
  let := h.extraspecial
  have hc (q : core z) : overlapCoreAut a f q * q⁻¹ ∈ center (core z) := by
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    have hz := hf ⟨q.val,(core_le_twoThreeCore h).trans (overlap_cubicLift_le a) q.property⟩ q.property
    change (overlapCoreAut a f q).val*q.val⁻¹ ∈ center (centralizer z) at hz
    exact mem_center_iff.mp hz r.val
  obtain ⟨q,hq⟩ := IsExtraspecial.exists_conj_of_central_displacement (p := 2)
    (overlapCoreAut a f) hc
  let r : PlaneOverlap a := ⟨q.val,(core_le_twoThreeCore h).trans
    (overlap_cubicLift_le a) q.property⟩
  have ha (x : PlaneOverlap a) (hx : x.val ∈ core z) : f x = r*x*r⁻¹ := by
    apply Subtype.ext
    exact (congrArg Subtype.val (MulEquiv.congr_fun hq ⟨x.val,hx⟩)).symm
  let b : MulAut (PlaneOverlap a) := (MulAut.conj r)⁻¹ * f
  have hb : ∀ x : PlaneOverlap a, x.val ∈ core z → b x = x := by
    intro x hx
    change (MulAut.conj r)⁻¹ (f x) = x
    rw [←map_inv,MulAut.conj_apply,ha x hx]
    group
  have he : f = MulAut.conj r * b := by dsimp [b]; group
  refine ⟨q,?_⟩
  rcases overlap_core_fixer_cases a b hb with hb | hb
  · left
    rw [he,hb,mul_one]
  · right
    rw [he,hb]

/-- Exact classification of the restriction kernel on the literal Q/Z(Q).
Both alternatives retain the actual correcting element of Q and marked twist. -/
theorem overlap_core_quotient_kernel (f : MulAut (PlaneOverlap a))
    (hf : quotientAut (center (core z)) (overlapCoreAut a f) = 1) :
    ∃ q : core z,
      f = MulAut.conj (⟨q.val,(core_le_twoThreeCore h).trans
        (overlap_cubicLift_le a) q.property⟩ : PlaneOverlap a) ∨
      f = MulAut.conj (⟨q.val,(core_le_twoThreeCore h).trans
        (overlap_cubicLift_le a) q.property⟩ : PlaneOverlap a) * overlapPlaneTwist a := by
  apply overlap_core_central_displacement_cases a f
  intro x hx
  let q : core z := ⟨x.val,hx⟩
  have he := DFunLike.congr_fun hf (QuotientGroup.mk' (center (core z)) q)
  rw [quotientAut_apply_mk] at he
  have hc : overlapCoreAut a f q * q⁻¹ ∈ center (core z) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center (core z)) (overlapCoreAut a f q * q⁻¹) = 1
    rw [map_mul,map_inv,he]
    exact mul_inv_cancel _
  rw [←core_center_eq_centralizer_center h]
  exact mem_map_of_mem (core z).subtype hc

/-- Pointwise fixation of Q is exactly the two-element central-twist kernel. -/
theorem overlap_core_fixer_iff (f : MulAut (PlaneOverlap a)) :
    (∀ x : PlaneOverlap a, x.val ∈ core z → f x = x) ↔
      f = 1 ∨ f = overlapPlaneTwist a := by
  constructor
  · exact overlap_core_fixer_cases a f
  · rintro (rfl | rfl)
    · exact fun _ _ => rfl
    · exact overlapPlaneTwist_fixes_core a

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
