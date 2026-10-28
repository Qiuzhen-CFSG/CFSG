module
public import Theory.GroupTheory.BinaryFrattiniExtension
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
public import GorensteinWalter.PGL2DihedralSylow
public import Theory.SpecificGroups.OddClassicalSylowFrattini
public import Theory.GroupTheory.SylowFrattiniBounds

/-!
# Four Frattini generators for odd-prime G₂ Sylow subgroups

The constructed orthogonal subgroup of odd index is the image of
(SL₂(p) × SL₂(p)) ⋊ C₂. Projection onto the first factor has an SL₂ kernel.
The first factor extended by the twist maps to PGL₂(p), with scalar kernel
of order two. That scalar is a square and is central, so lies in the
Frattini subgroup of every Sylow two-subgroup. Dihedral PGL₂ Sylows and
cyclic or quaternion SL₂ Sylows therefore give two generators for each
factor. The extension inequality gives four for the original cover and
its orthogonal image. Odd index transfers the bound to G₂(p).

At p = 3 the same orthogonal subgroup has order 576 and index 7371; its
kernel calculation remains unchanged. Field transport retains the actual
octonion carrier. The Hall consumer uses this bound to exclude its marked
PSL₅(2) outer section through the full component cover.

Source: Aschbacher--Smith 4.4.10--11, printed p.621. The prime-three index
calculation reuses Chapter11's `OddNormalizer.G2Frattini` proof. Coordinate
models and field transport retain the licensed ATLAS realization; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace Atlas.G2.OddFrattiniSixteen

private theorem cyclic_frattini_le_two {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) [IsCyclic P] : Nat.card (P ⧸ frattini P) ≤ 2 := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsCyclic (P ⧸ frattini P) := isCyclic_of_surjective
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have h := IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ frattini P)
  rw [IsCyclic.exponent_eq_card] at h
  exact Nat.le_of_dvd (by decide) h

private theorem cyclic_index_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (A : Subgroup P) [IsCyclic A] (hi : A.index ≤ 2) :
    Nat.card (P ⧸ frattini P) ≤ 4 :=
  (hP.card_frattini_quotient_le_subgroup_index_mul A).trans
    ((Nat.mul_le_mul hi (cyclic_frattini_le_two (hP.to_subgroup A))).trans (by decide))

private theorem quaternion_subgroup_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {n : ℕ} (hn : 0 < n)
    (e : P →* QuaternionGroup n) (he : Function.Injective e) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  let : NeZero n := ⟨hn.ne'⟩
  let A := zpowers (QuaternionGroup.a (1 : ZMod (2*n)))
  have hi : A.index = 2 := by
    have h := A.index_mul_card
    rw [Nat.card_zpowers,QuaternionGroup.orderOf_a_one] at h
    have hc : Nat.card (QuaternionGroup n) = 4*n := by
      rw [Nat.card_eq_fintype_card,QuaternionGroup.card]
    rw [hc] at h
    nlinarith
  let B := A.comap e
  let : IsCyclic B := isCyclic_of_injective (e.subgroupComap A)
    (fun x y h => Subtype.ext (he (congrArg Subtype.val h)))
  apply cyclic_index_frattini_le_four hP B
  let : A.Normal := normal_of_index_eq_two hi
  rw [index_comap]
  exact Nat.le_of_dvd (by decide) (hi ▸ A.relIndex_dvd_index_of_normal e.range)

private theorem sl2_subgroup_frattini_le_four {F P : Type*} [Field F] [Finite F]
    [Group P] [Finite P] (hF : (2 : F) ≠ 0) (hP : IsPGroup 2 P)
    (j : P →* SL(2,F)) (hj : Function.Injective j) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  have hr : IsPGroup 2 j.range := hP.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨S,hS⟩ := hr.exists_le_sylow
  let i : P →* S := j.codRestrict _ (fun x => hS ⟨x,rfl⟩)
  have hi : Function.Injective i := fun x y h => hj (congrArg Subtype.val h)
  rcases Matrix.SpecialLinearGroup.sylow_two_cyclic_or_quaternion hF S with hc | ⟨n,hn,⟨e⟩⟩
  · let := hc
    let : IsCyclic P := isCyclic_of_injective i hi
    exact (cyclic_frattini_le_two hP).trans (by decide)
  exact quaternion_subgroup_frattini_le_four hP hn (e.toMonoidHom.comp i) (e.injective.comp hi)

private theorem dihedral_subgroup_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {n : ℕ} (hn : 0 < n)
    (f : P →* DihedralGroup n) (hf : Function.Injective f) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  let : NeZero n := ⟨hn.ne'⟩
  let A := zpowers (DihedralGroup.r (1 : ZMod n))
  have hi : A.index = 2 := by
    have h := A.index_mul_card
    rw [Nat.card_zpowers,DihedralGroup.orderOf_r_one,DihedralGroup.nat_card] at h
    nlinarith
  let B := A.comap f
  let : IsCyclic B := isCyclic_of_injective (f.subgroupComap A)
    (fun x y h => Subtype.ext (hf (congrArg Subtype.val h)))
  apply cyclic_index_frattini_le_four hP B
  let : A.Normal := normal_of_index_eq_two hi
  rw [index_comap]
  exact Nat.le_of_dvd (by decide) (hi ▸ A.relIndex_dvd_index_of_normal f.range)

end Atlas.G2.OddFrattiniSixteen


open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative TensorProduct
namespace Atlas.G2.OddFrattiniSixteen
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
variable {F : Type*} [Field F]

private def twistMatrix (d : F) (hd : d ≠ 0) : GL (Fin 2) F where
  val := !![0,d;1,0]
  inv := !![0,1;d⁻¹,0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd]

private theorem twistMatrix_conj (d : F) (hd : d ≠ 0) (A : SL(2,F)) :
    SpecialLinearGroup.toGL (rankOneTwist d hd A) =
      twistMatrix d hd * SpecialLinearGroup.toGL A * (twistMatrix d hd)⁻¹ := by
  apply Units.ext
  change twist d A.val = !![0,d;1,0] * A.val * !![0,1;d⁻¹,0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist,Matrix.mul_apply,Fin.sum_univ_two,Matrix.vecMul,dotProduct,hd,mul_comm,mul_left_comm]

private theorem twistMatrix_square (d : F) (hd : d ≠ 0) :
    twistMatrix d hd ^ 2 = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 d hd) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistMatrix,pow_two,Matrix.mul_apply,Fin.sum_univ_two,GeneralLinearGroup.coe_scalar]

private def twistProjective (d : F) (hd : d ≠ 0) : C2 →* PGL(Fin 2,F) :=
  involutionHom (ProjGenLinGroup.mk (twistMatrix d hd)) (by
    rw [←map_pow,twistMatrix_square,ProjGenLinGroup.mk_scalar])

private def singleAction (d : F) (hd : d ≠ 0) : C2 →* MulAut SL(2,F) :=
  involutionHom (rankOneTwist d hd) (by
    ext A : 1
    apply Subtype.ext
    exact twist_twist d hd A.val)

private abbrev Single (d : F) (hd : d ≠ 0) := SL(2,F) ⋊[singleAction d hd] C2

private instance finiteSingle [Finite F] (d : F) (hd : d ≠ 0) : Finite (Single d hd) :=
  Finite.of_equiv (SL(2,F) × C2) SemidirectProduct.equivProd.symm

private theorem projective_compatibility (d : F) (hd : d ≠ 0) (c : C2) :
    SpecialLinearGroup.toPGL.comp ((singleAction d hd c).toMonoidHom) =
      (MulAut.conj (twistProjective d hd c)).toMonoidHom.comp SpecialLinearGroup.toPGL := by
  have hc : c = 1 ∨ c = .ofAdd 1 := by
    exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c.toAdd
  rcases hc with rfl | rfl
  · ext A; simp
  · ext A
    change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (singleAction d hd (.ofAdd 1) A)) =
      twistProjective d hd (.ofAdd 1) * ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) *
        (twistProjective d hd (.ofAdd 1))⁻¹
    simp only [singleAction,twistProjective,involutionHom_generator,twistMatrix_conj,
      map_mul,map_inv]

private def singleProjection (d : F) (hd : d ≠ 0) : Single d hd →* PGL(Fin 2,F) :=
  SemidirectProduct.lift SpecialLinearGroup.toPGL (twistProjective d hd)
    (projective_compatibility d hd)

private theorem singleProjection_kernel (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare (-d))
    (x : Single d hd) : singleProjection d hd x = 1 ↔
      x = 1 ∨ x = SemidirectProduct.inl (-1) := by
  have hneg : Matrix.scalar (Fin 2) (-1 : F) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · intro hx
    have hc : x.right = 1 ∨ x.right = .ofAdd 1 := by
      exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) x.right.toAdd
    have hx0 : x.right = 1 := by
      rcases hc with hc | hc
      · exact hc
      · exfalso
        have he : ProjGenLinGroup.mk (SpecialLinearGroup.toGL x.left * twistMatrix d hd) = 1 := by
          simpa only [singleProjection,SemidirectProduct.lift,MonoidHom.coe_mk,OneHom.coe_mk,
            hc,twistProjective,involutionHom_generator,map_mul,Matrix.SpecialLinearGroup.toPGL,MonoidHom.comp_apply] using hx
        have hcen : SpecialLinearGroup.toGL x.left * twistMatrix d hd ∈ center (GL (Fin 2) F) :=
          ProjGenLinGroup.mk_eq_one.mp he
        rw [GeneralLinearGroup.center_eq_range_scalar] at hcen
        obtain ⟨u,hu⟩ := hcen
        have hedet := congrArg (fun g : GL (Fin 2) F => (GeneralLinearGroup.det g : F)) hu
        have hdet : (-d) = (u : F) ^ 2 := by
          simpa [GeneralLinearGroup.val_det_apply,GeneralLinearGroup.coe_scalar,
            Matrix.det_mul,x.left.property,twistMatrix,Matrix.det_fin_two,
            Matrix.det_diagonal,Fin.prod_univ_succ,pow_two] using hedet.symm
        exact hns ⟨u,by simpa only [pow_two] using hdet⟩
    have he : SpecialLinearGroup.toPGL x.left = 1 := by
      simpa only [singleProjection,SemidirectProduct.lift,MonoidHom.coe_mk,OneHom.coe_mk,
        hx0,map_one,mul_one] using hx
    have hz : x.left ∈ center SL(2,F) := by
      rw [←SpecialLinearGroup.toPGL_ker]
      exact he
    obtain ⟨r,hr,heq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    have hr' : r = 1 ∨ r = -1 := by
      have h : r ^ 2 = 1 := by simpa using hr
      exact sq_eq_one_iff.mp h
    rcases hr' with rfl | rfl
    · exact Or.inl (SemidirectProduct.ext (Subtype.ext (by simpa using heq.symm)) hx0)
    · exact Or.inr (SemidirectProduct.ext (Subtype.ext (heq.symm.trans hneg)) hx0)
  · rintro (rfl | rfl)
    · exact map_one _
    · rw [singleProjection,SemidirectProduct.lift_inl]
      rw [←MonoidHom.mem_ker,SpecialLinearGroup.toPGL_ker]
      exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1,by simp,hneg⟩

private def firstProjection (d : F) (hd : d ≠ 0) :
    (SL(2,F) × SL(2,F)) ⋊[action d hd] C2 →* Single d hd :=
  SemidirectProduct.map (MonoidHom.fst _ _) (MonoidHom.id _) (by
    intro c
    have hc : c = 1 ∨ c = .ofAdd 1 := by
      exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c.toAdd
    rcases hc with rfl | rfl
    · ext A; simp
    · apply MonoidHom.ext
      intro A
      simp only [MonoidHom.comp_apply,MonoidHom.id_apply,action,singleAction,involutionHom_generator]
      rfl)

end Atlas.G2.OddFrattiniSixteen

namespace Atlas.G2.OddFrattiniSixteen
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
variable {p : ℕ} [Fact p.Prime]

private theorem single_scalar_central (d : ZMod p) (hd : d ≠ 0) :
    SemidirectProduct.inl (-1) ∈ center (Single d hd) := by
  apply mem_center_iff.mpr
  rintro ⟨A,c⟩
  have hc : c = 1 ∨ c = .ofAdd 1 := by
    exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c.toAdd
  have hscalar : singleAction d hd c (-1) = -1 := by
    rcases hc with rfl | rfl
    · simp
    · simp only [singleAction,involutionHom_generator]
      apply Subtype.ext
      change twist d (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [twist]
  apply SemidirectProduct.ext
  · change A * singleAction d hd c (-1) = -1 * singleAction d hd 1 A
    rw [hscalar,map_one]
    simp
  · simp

private theorem pgl2_subgroup_frattini_le_four (ho : Odd p)
    {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R)
    (j : R →* PGL(2,ZMod p)) (hj : Function.Injective j) :
    Nat.card (R ⧸ frattini R) ≤ 4 := by
  let : Finite PGL(2,ZMod p) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hr : IsPGroup 2 j.range := hR.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨S,hS⟩ := hr.exists_le_sylow
  let i : R →* S := j.codRestrict _ (fun x => hS ⟨x,rfl⟩)
  have hi : Function.Injective i := fun x y h => hj (congrArg Subtype.val h)
  obtain ⟨n,_,⟨e⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model (ZMod p)
    ⟨p,1,Fact.out,ho,by decide,by simp⟩ S
  exact dihedral_subgroup_frattini_le_four hR (by positivity)
    (e.toMonoidHom.comp i) (e.injective.comp hi)

private theorem single_sylow_frattini_le_four (ho : Odd p) (d : ZMod p) (hd : d ≠ 0)
    (hns : ¬ IsSquare (-d)) (P : Sylow 2 (Single d hd)) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  let : Finite PGL(2,ZMod p) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let f := (singleProjection d hd).subgroupMap (P : Subgroup (Single d hd))
  have hf := (singleProjection d hd).subgroupMap_surjective (P : Subgroup (Single d hd))
  have hk : f.ker ≤ frattini P := by
    intro x hx
    have hxx : singleProjection d hd x = 1 := congrArg Subtype.val hx
    rcases (singleProjection_kernel d hd hns x).mp hxx with h | h
    · have he : x = 1 := Subtype.ext h
      rw [he]
      exact one_mem _
    · let z : Single d hd := SemidirectProduct.inl (-1)
      let a : Single d hd := SemidirectProduct.inl (quarterTurn p)
      have ha : a ^ 2 = z := by rw [←map_pow,quarterTurn_sq]
      have hz : z ^ 2 = 1 := by rw [←map_pow]; simp
      obtain ⟨y,hy⟩ := BinaryFrattiniExtension.central_square_in_sylow P (single_scalar_central d hd) ha hz
      have he : y ^ 2 = x := Subtype.ext (hy.trans h.symm)
      let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
      exact he ▸ pth_power_mem_frattini_of_isPGroup (p := 2) y
  apply (BinaryFrattiniExtension.card_le_of_frattini_kernel P.isPGroup' f hf hk).trans
  exact pgl2_subgroup_frattini_le_four ho (P.isPGroup'.of_surjective f hf)
    ((P : Subgroup (Single d hd)).map (singleProjection d hd)).subtype Subtype.val_injective

end Atlas.G2.OddFrattiniSixteen

namespace Atlas.G2.OddFrattiniSixteen
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
variable {p : ℕ} [Fact p.Prime]
private abbrev Double (d : ZMod p) (hd : d ≠ 0) :=
  (SL(2,ZMod p) × SL(2,ZMod p)) ⋊[action d hd] C2

private instance finiteDouble (d : ZMod p) (hd : d ≠ 0) : Finite (Double d hd) :=
  Finite.of_equiv ((SL(2,ZMod p) × SL(2,ZMod p)) × C2) SemidirectProduct.equivProd.symm

private theorem firstKernel_right (d : ZMod p) (hd : d ≠ 0)
    (x : (firstProjection d hd).ker) : x.val.right = 1 :=
  congrArg SemidirectProduct.right x.property

private theorem firstKernel_left (d : ZMod p) (hd : d ≠ 0)
    (x : (firstProjection d hd).ker) : x.val.left.1 = 1 :=
  congrArg SemidirectProduct.left x.property

private def firstKernelSecond (d : ZMod p) (hd : d ≠ 0) :
    (firstProjection d hd).ker →* SL(2,ZMod p) where
  toFun x := x.val.left.2
  map_one' := rfl
  map_mul' x y := by
    change x.val.left.2 * (action d hd x.val.right y.val.left).2 = _
    rw [firstKernel_right d hd x,map_one]
    rfl

private theorem firstKernelSecond_injective (d : ZMod p) (hd : d ≠ 0) :
    Function.Injective (firstKernelSecond d hd) := by
  intro x y h
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact Prod.ext ((firstKernel_left d hd x).trans (firstKernel_left d hd y).symm) h
  · exact (firstKernel_right d hd x).trans (firstKernel_right d hd y).symm

private theorem double_sylow_frattini_le_sixteen (ho : Odd p) (d : ZMod p) (hd : d ≠ 0)
    (hns : ¬ IsSquare (-d)) (P : Sylow 2 (Double d hd)) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  have hfirst : Function.Surjective (firstProjection d hd) := by
    intro y
    exact ⟨⟨(y.left,1),y.right⟩,rfl⟩
  let Q := P.mapSurjective hfirst
  let f : P →* Q := (firstProjection d hd).subgroupMap (P : Subgroup (Double d hd))
  have hf : Function.Surjective f := (firstProjection d hd).subgroupMap_surjective _
  let k : f.ker →* (firstProjection d hd).ker :=
    (((P : Subgroup (Double d hd)).subtype).comp f.ker.subtype).codRestrict _
      (fun x => congrArg Subtype.val x.property)
  have hk : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (firstProjection d hd).ker => z.val) h))
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hne : p ≠ 2 := by rintro rfl; norm_num at ho
    have hp2 := (Fact.out : p.Prime).two_le
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  have hker : Nat.card (f.ker ⧸ frattini f.ker) ≤ 4 :=
    sl2_subgroup_frattini_le_four h2 (P.isPGroup'.to_subgroup _)
      ((firstKernelSecond d hd).comp k) ((firstKernelSecond_injective d hd).comp hk)
  exact (BinaryFrattiniExtension.card_le P.isPGroup' f hf).trans
    ((Nat.mul_le_mul hker (single_sylow_frattini_le_four ho d hd hns Q)).trans (by decide))

end Atlas.G2.OddFrattiniSixteen

namespace Atlas.G2.OddFrattiniSixteen
open Subgroup Matrix
open scoped MatrixGroups
open Atlas.G2 Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap

/-- Internal odd-index transport, shared with the sharper diagonal calculation
in `OddFrattiniEight`. The actual orthogonal kernel and prime-three endpoint
are proved once here. -/
private theorem prime_frattini_card_le_of_double_bound {p : ℕ} [Fact p.Prime]
    (hp : 2 < p) (b : ℕ)
    (hbound : ∀ (d : ZMod p) (hd : d ≠ 0), ¬ IsSquare (-d) →
      ∀ P : Sylow 2 (Double d hd), Nat.card (P ⧸ frattini P) ≤ b)
    (P : Sylow 2 (Model (ZMod p))) : Nat.card (P ⧸ frattini P) ≤ b := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  let d := -a
  have hd : d ≠ 0 := neg_ne_zero.mpr ha0
  let H := (OrthogonalMap.inclusion d hd).range
  have hindex : ¬ 2 ∣ H.index := by
    rw [← even_iff_two_dvd]
    apply Nat.not_even_iff_odd.mpr
    by_cases hp3 : 3 < p
    · exact odd_index_of_diagonal_kernel
        (F := ZMod p) (by simp [Nat.card_eq_fintype_card]) hp3
        (action d hd) (OrthogonalMap.inclusion d hd)
        (inclusion_kernel d hd (by simpa [d] using ha))
    · have he : p = 3 := by omega
      subst p
      let j := OrthogonalMap.inclusion d hd
      let z : (RankOne 3 × RankOne 3) ⋊[action d hd] C2 := SemidirectProduct.inl (-1,-1)
      have hz : z ≠ 1 := by
        intro h
        have h' := congrArg (fun x : (RankOne 3 × RankOne 3) ⋊[action d hd] C2 => x.left.1.val 0 0) h
        change (-1 : ZMod 3) = 1 at h'
        have hz : (2 : ZMod 3) = 0 := by linear_combination -h'
        have hh := (ZMod.natCast_eq_zero_iff 2 3).mp hz
        norm_num at hh
      have hk : Nat.card j.ker = 2 := by
        apply (Nat.card_eq_two_iff' (1 : j.ker)).mpr
        have hj := inclusion_kernel d hd (by simpa [d] using ha)
        refine ⟨⟨z,(hj z).mpr (Or.inr rfl)⟩,fun h => hz (congrArg Subtype.val h),?_⟩
        intro x hx
        rcases (hj x).mp x.property with h | h
        · exact (hx (Subtype.ext h)).elim
        · exact Subtype.ext h
      have hdom : Nat.card ((RankOne 3 × RankOne 3) ⋊[action d hd] C2) = 1152 := by
        rw [SemidirectProduct.card,Nat.card_prod,Atlas.card_sl_two]
        norm_num [C2,Nat.card_eq_fintype_card]
      have hr : Nat.card H = 576 := by
        have h := j.ker.card_mul_index
        rw [index_ker,hk,hdom] at h
        change 2 * Nat.card H = 1152 at h
        omega
      have hidx := H.card_mul_index
      rw [hr,Atlas.G2.card_Model] at hidx
      norm_num [Nat.card_eq_fintype_card] at hidx
      have hh : H.index = 7371 := by omega
      rw [hh]
      decide
  let Q : Sylow 2 H := Classical.choice inferInstance
  have hm : ¬ 2 ∣ ((Q : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two Q.not_dvd_index hindex
  let S : Sylow 2 (Model (ZMod p)) := (Q.isPGroup'.map H.subtype).toSylow hm
  have he : Q ≃* S := Q.equivMapOfInjective H.subtype H.subtype_injective
  have hQ : Nat.card (Q ⧸ frattini Q) ≤ b := by
    apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
      (OrthogonalMap.inclusion d hd).rangeRestrict
      (OrthogonalMap.inclusion d hd).rangeRestrict_surjective ?_ Q
    intro R
    exact hbound d hd (by simpa [d] using ha) R
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (Sylow.equiv P S),
    ← Theory.GroupTheory.SylowFrattiniBounds.card_congr he]
  exact hQ

/-- The bound for the literal split-octonion model over the odd prime field. -/
theorem prime_frattini_card_le_sixteen {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (P : Sylow 2 (Model (ZMod p))) : Nat.card (P ⧸ frattini P) ≤ 16 :=
  prime_frattini_card_le_of_double_bound hp 16
    (fun d hd hns R => double_sylow_frattini_le_sixteen
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) d hd hns R) P

/-- Every odd-prime G₂ Sylow two-subgroup has at most four Frattini generators. -/
theorem frattini_card_le_sixteen {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hF : Nat.card F = p)
    (P : Sylow 2 (Model F)) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  have hp : 2 < p := by
    have hprime := (Fact.out : p.Prime).two_le
    have hne : p ≠ 2 := by rintro rfl; norm_num at ho
    omega
  let := Fintype.ofFinite F
  let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F Fact.out
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := fieldEquiv e.symm
  let Q := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have he : P ≃* Q := P.equivMapOfInjective f.toMonoidHom f.injective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr he]
  exact prime_frattini_card_le_sixteen hp Q

end Atlas.G2.OddFrattiniSixteen
