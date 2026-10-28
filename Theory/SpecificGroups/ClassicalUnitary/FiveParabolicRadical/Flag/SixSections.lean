module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Automorphisms
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.NormSimilitudes
public import Theory.GroupTheory.FrattiniFlagSimpleSections
public import Theory.SpecificGroups.SymmetricFourSolvable
import all Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Automorphisms

/-!
# No alternating-six section in the actual unitary-five Sylow automorphisms

Fourth-power values form an invariant set of size at most four. Its kernel
acts on the two original Frattini root axes by norm similitudes. Each axis
has no A₆ section, and the common action kernel is the genuine Burnside
two-kernel. Arbitrary section kernels are retained through both reductions.
Source: Aschbacher--Smith 4.4.10--11 and 12.1.9, printed pp.621 and 793,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.Flag.SixSections
open Automorphisms PlaneCore
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
  (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)

private def firstAction : MulAut (Coordinates J) →* MulAut (Multiplicative F) where
  toFun a := {
    toFun x := Multiplicative.ofAdd ((rootAction J c hc hJ a (Multiplicative.ofAdd (x.toAdd,0))).toAdd.1)
    invFun x := Multiplicative.ofAdd ((firstPerm (rootAction J c hc hJ a)
      (fun x => rootAction_first J c hc hJ a (Multiplicative.ofAdd (x,0)) rfl)).symm x.toAdd)
    left_inv x := congrArg Multiplicative.ofAdd ((firstPerm (rootAction J c hc hJ a)
      (fun x => rootAction_first J c hc hJ a (Multiplicative.ofAdd (x,0)) rfl)).symm_apply_apply x.toAdd)
    right_inv x := congrArg Multiplicative.ofAdd ((firstPerm (rootAction J c hc hJ a)
      (fun x => rootAction_first J c hc hJ a (Multiplicative.ofAdd (x,0)) rfl)).apply_symm_apply x.toAdd)
    map_mul' x y := by
      apply Multiplicative.toAdd.injective
      have he := (rootAction J c hc hJ a).map_mul
        (Multiplicative.ofAdd (x.toAdd,0)) (Multiplicative.ofAdd (y.toAdd,0))
      simpa only [toAdd_mul,←ofAdd_add,Prod.mk_add_mk,add_zero,toAdd_ofAdd,Prod.fst_add]
        using congrArg (fun z : Multiplicative (F×F) => z.toAdd.1) he }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    change (rootAction J c hc hJ 1 (Multiplicative.ofAdd (x.toAdd,0))).toAdd.1 = x.toAdd
    rw [map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    have he : rootAction J c hc hJ b (Multiplicative.ofAdd (x.toAdd,0)) =
        Multiplicative.ofAdd ((rootAction J c hc hJ b (Multiplicative.ofAdd (x.toAdd,0))).toAdd.1,0) :=
      Multiplicative.toAdd.injective (Prod.ext rfl (rootAction_first J c hc hJ b _ rfl))
    change Multiplicative.ofAdd ((rootAction J c hc hJ (a*b) (Multiplicative.ofAdd (x.toAdd,0))).toAdd.1) = _
    rw [map_mul]
    change Multiplicative.ofAdd ((rootAction J c hc hJ a
      (rootAction J c hc hJ b (Multiplicative.ofAdd (x.toAdd,0)))).toAdd.1) = _
    rw [he]
    rfl

private def secondAction : MulAut (Coordinates J) →* MulAut (Multiplicative F) where
  toFun a := {
    toFun x := Multiplicative.ofAdd ((rootAction J c hc hJ a (Multiplicative.ofAdd (0,x.toAdd))).toAdd.2)
    invFun x := Multiplicative.ofAdd ((secondPerm (rootAction J c hc hJ a)
      (fun x => rootAction_second J c hc hJ a (Multiplicative.ofAdd (0,x)) rfl)).symm x.toAdd)
    left_inv x := congrArg Multiplicative.ofAdd ((secondPerm (rootAction J c hc hJ a)
      (fun x => rootAction_second J c hc hJ a (Multiplicative.ofAdd (0,x)) rfl)).symm_apply_apply x.toAdd)
    right_inv x := congrArg Multiplicative.ofAdd ((secondPerm (rootAction J c hc hJ a)
      (fun x => rootAction_second J c hc hJ a (Multiplicative.ofAdd (0,x)) rfl)).apply_symm_apply x.toAdd)
    map_mul' x y := by
      apply Multiplicative.toAdd.injective
      have he := (rootAction J c hc hJ a).map_mul
        (Multiplicative.ofAdd (0,x.toAdd)) (Multiplicative.ofAdd (0,y.toAdd))
      simpa only [toAdd_mul,←ofAdd_add,Prod.mk_add_mk,add_zero,toAdd_ofAdd,Prod.snd_add]
        using congrArg (fun z : Multiplicative (F×F) => z.toAdd.2) he }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    change (rootAction J c hc hJ 1 (Multiplicative.ofAdd (0,x.toAdd))).toAdd.2 = x.toAdd
    rw [map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    have he : rootAction J c hc hJ b (Multiplicative.ofAdd (0,x.toAdd)) =
        Multiplicative.ofAdd (0,(rootAction J c hc hJ b (Multiplicative.ofAdd (0,x.toAdd))).toAdd.2) :=
      Multiplicative.toAdd.injective (Prod.ext (rootAction_second J c hc hJ b _ rfl) rfl)
    change Multiplicative.ofAdd ((rootAction J c hc hJ (a*b) (Multiplicative.ofAdd (0,x.toAdd))).toAdd.2) = _
    rw [map_mul]
    change Multiplicative.ofAdd ((rootAction J c hc hJ a
      (rootAction J c hc hJ b (Multiplicative.ofAdd (0,x.toAdd)))).toAdd.2) = _
    rw [he]
    rfl

private theorem rootAction_pair (a : MulAut (Coordinates J)) (x y : F) :
    rootAction J c hc hJ a (Multiplicative.ofAdd (x,y)) =
      Multiplicative.ofAdd ((firstAction J c hc hJ a (Multiplicative.ofAdd x)).toAdd,
        (secondAction J c hc hJ a (Multiplicative.ofAdd y)).toAdd) := by
  have h1 : rootAction J c hc hJ a (Multiplicative.ofAdd (x,0)) =
      Multiplicative.ofAdd ((firstAction J c hc hJ a (Multiplicative.ofAdd x)).toAdd,0) :=
    Multiplicative.toAdd.injective (Prod.ext rfl (rootAction_first J c hc hJ a _ rfl))
  have h2 : rootAction J c hc hJ a (Multiplicative.ofAdd (0,y)) =
      Multiplicative.ofAdd (0,(secondAction J c hc hJ a (Multiplicative.ofAdd y)).toAdd) :=
    Multiplicative.toAdd.injective (Prod.ext (rootAction_second J c hc hJ a _ rfl) rfl)
  have hsplit : Multiplicative.ofAdd (x,y) =
      (Multiplicative.ofAdd (x,0) : Multiplicative (F×F)) * Multiplicative.ofAdd (0,y) := by
    apply Multiplicative.toAdd.injective
    simp
  rw [hsplit,map_mul,h1,h2]
  apply Multiplicative.toAdd.injective
  simp

private def fourthAction : MulAut (Coordinates J) →* Equiv.Perm (fourthValues J) where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (by
    intro x
    constructor
    · rintro ⟨u,hu⟩
      refine ⟨a.symm u,?_⟩
      change (a.symm u)^4 = x
      rw [←map_pow]
      exact (congrArg a.symm hu).trans (a.symm_apply_apply x)
    · rintro ⟨u,rfl⟩
      exact ⟨a u,(map_pow a u 4).symm⟩)
  map_one' := by apply Equiv.ext; intro x; rfl
  map_mul' a b := by apply Equiv.ext; intro x; rfl

private theorem fourth_kernel_norm (hconj : ∀ x, J.conj x = x^4)
    (a : (fourthAction J).ker) (x y : F) :
    ((firstAction J c hc hJ a.val (Multiplicative.ofAdd x)).toAdd *
      (secondAction J c hc hJ a.val (Multiplicative.ofAdd y)).toAdd)^5 = (x*y)^5 := by
  obtain ⟨u,hu⟩ := rootCoordinates_surjective J c hc (Multiplicative.ofAdd (x,y))
  have he : a.val (u^4) = u^4 := congrArg Subtype.val
    (Equiv.congr_fun a.property (⟨u^4,⟨u,rfl⟩⟩ : fourthValues J))
  have hz := congrArg (fun v : Coordinates J => v.left.z 0 0) he
  rw [map_pow,fourth_z,fourth_z] at hz
  have hnorm : ((rootAction J c hc hJ a.val (rootCoordinates J u)).toAdd.1 *
      (rootAction J c hc hJ a.val (rootCoordinates J u)).toAdd.2)^5 =
      ((rootCoordinates J u).toAdd.1 * (rootCoordinates J u).toAdd.2)^5 := by
    rw [rootAction_apply]
    change ((a.val u).right.toAdd * (a.val u).left.x 1)^5 =
      (u.right.toAdd * u.left.x 1)^5
    change ((a.val u).right.toAdd * (a.val u).left.x 1) * J.conj
      ((a.val u).right.toAdd * (a.val u).left.x 1) =
      (u.right.toAdd * u.left.x 1) * J.conj (u.right.toAdd * u.left.x 1) at hz
    simpa only [hconj,←pow_succ'] using hz
  rw [hu,rootAction_pair] at hnorm
  exact hnorm

omit [CharP F 2] [Finite F] in
private theorem norm_similitudes_of_product
    (a b : MulAut (Multiplicative F))
    (h : ∀ x y : F, ((a (Multiplicative.ofAdd x)).toAdd *
      (b (Multiplicative.ofAdd y)).toAdd)^5 = (x*y)^5) :
    ∀ x : F, (a (Multiplicative.ofAdd x)).toAdd^5 =
      (a (Multiplicative.ofAdd 1)).toAdd^5 * x^5 := by
  have hne : (b (Multiplicative.ofAdd 1)).toAdd ≠ 0 := by
    intro he
    have heq := b.injective ((congrArg Multiplicative.ofAdd he).trans (map_one b).symm)
    exact (one_ne_zero : (1 : F) ≠ 0) (congrArg Multiplicative.toAdd heq)
  intro x
  apply mul_right_cancel₀ (pow_ne_zero 5 hne)
  have hx := h x 1
  have h1 := h 1 1
  rw [mul_pow,mul_one] at hx
  rw [mul_pow,one_mul,one_pow] at h1
  calc
    _ = x^5 := hx
    _ = _ := by rw [mul_assoc,mul_comm (x^5),←mul_assoc,h1,one_mul]

include c hc hJ in
/-- The full Sylow-coordinate automorphism group has no alternating-six
section, with the genuine Frattini two-kernel and arbitrary section kernels. -/
theorem no_six_section_coordinates
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x^4)
    (U : Subgroup (MulAut (Coordinates J)))
    (q : U →* alternatingGroup (Fin 6)) (hq : Function.Surjective q) : False := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Finite (Parameters J) := Finite.of_injective (fun u : Parameters J => (u.x,u.z))
    (fun _ _ h => Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let : Finite (Coordinates J) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hns := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
  have hs : Group.IsSolvable (Equiv.Perm (fourthValues J)) := by
    let : Fintype (fourthValues J) := Fintype.ofFinite _
    let e : fourthValues J ↪ Fin 4 := Classical.choice
      (Function.Embedding.nonempty_of_card_le (by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_fin] using fourthValues_card J hcard hconj))
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    exact Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let := hs
  let t := fourthAction J
  let : Group.IsSolvable (MulAut (Coordinates J) ⧸ t.ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange t).toMonoidHom)
      (QuotientGroup.quotientKerEquivRange t).injective
  obtain ⟨B,f,hf⟩ := simple_section_normal_of_solvable_quotient hns t.ker U q hq
  let r := (firstAction J c hc hJ).comp t.ker.subtype
  let s := (secondAction J c hc hJ).comp t.ker.subtype
  have hp : IsPGroup 2 (Coordinates J) :=
    (unipotent_isPGroup J c hc hJ).of_equiv (coordinatesEquivUnipotent J c hc hJ).symm
  have hk : IsPGroup 2 (r.ker ⊓ s.ker : Subgroup t.ker) := by
    let j : (r.ker ⊓ s.ker : Subgroup t.ker) →*
        (quotientAut (frattini (Coordinates J))).ker :=
      (t.ker.subtype.comp (r.ker ⊓ s.ker : Subgroup t.ker).subtype).codRestrict _ (by
        intro a
        apply (MulAut.congr (frattiniEquiv J c hc hJ)).injective
        change rootAction J c hc hJ a.val.val =
          (MulAut.congr (frattiniEquiv J c hc hJ)) 1
        rw [map_one]
        apply MulEquiv.ext
        intro v
        have he := rootAction_pair J c hc hJ a.val.val v.toAdd.1 v.toAdd.2
        have ha1 : firstAction J c hc hJ a.val.val = 1 := a.property.1
        have ha2 : secondAction J c hc hJ a.val.val = 1 := a.property.2
        simpa only [ha1,ha2,MulAut.one_apply,toAdd_ofAdd,Prod.mk.eta,ofAdd_toAdd] using he)
    exact (isPGroup_quotientAut_frattini_kernel hp).of_injective j
      (fun a b he => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) he)))
  let : Group.IsNilpotent (r.rangeRestrict.ker ⊓ s.rangeRestrict.ker : Subgroup t.ker) := by
    rw [MonoidHom.ker_rangeRestrict,MonoidHom.ker_rangeRestrict]
    exact hk.isNilpotent
  rcases simple_section_two_actions hns r.rangeRestrict s.rangeRestrict B f hf with ⟨C,g,hg⟩ | ⟨C,g,hg⟩
  · have hn (a : r.range) (x : F) :
        (a.val (Multiplicative.ofAdd x)).toAdd^5 =
          (a.val (Multiplicative.ofAdd 1)).toAdd^5*x^5 := by
      obtain ⟨b,hb⟩ := a.property
      rw [←hb]
      exact norm_similitudes_of_product (r b) (s b)
        (fourth_kernel_norm J c hc hJ hconj b) x
    exact no_six_section_of_norm_similitudes hcard r.range.subtype
      r.range.subtype_injective hn C g hg
  · have hn (a : s.range) (x : F) :
        (a.val (Multiplicative.ofAdd x)).toAdd^5 =
          (a.val (Multiplicative.ofAdd 1)).toAdd^5*x^5 := by
      obtain ⟨b,hb⟩ := a.property
      rw [←hb]
      apply norm_similitudes_of_product (s b) (r b) ?_ x
      intro x y
      calc
        _ = ((r b (Multiplicative.ofAdd y)).toAdd * (s b (Multiplicative.ofAdd x)).toAdd)^5 :=
          congrArg (fun z : F => z^5) (mul_comm _ _)
        _ = (y*x)^5 := fourth_kernel_norm J c hc hJ hconj b y x
        _ = (x*y)^5 := congrArg (fun z : F => z^5) (mul_comm _ _)
    exact no_six_section_of_norm_similitudes hcard s.range.subtype
      s.range.subtype_injective hn C g hg

include hJ in
/-- Every actual Sylow of the marked projective unitary group has no A₆
section in its full automorphism group. -/
theorem no_six_section_sylow_of_equiv
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x^4)
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G)
    (U : Subgroup (MulAut P)) (q : U →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨d,hd⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let e₁ : P ≃* R := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  let e₂ := R.equiv (unipotentSylowFour J hcard hconj d hd hJ)
  let e₃ := unipotentSylowFourEquivCoordinates J hcard hconj d hd hJ
  let a := MulAut.congr (e₁.trans (e₂.trans e₃))
  let b := U.equivMapOfInjective a.toMonoidHom a.injective
  exact no_six_section_coordinates J d hd hJ hcard hconj (U.map a.toMonoidHom)
    (q.comp b.symm.toMonoidHom) (hq.comp b.symm.surjective)

end Theory.SpecificGroups.UnitaryFive.Flag.SixSections
