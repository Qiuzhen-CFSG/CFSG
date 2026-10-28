module
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates
public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.ElementaryPerfectSplit

/-!
# The marked augmentation cover of an elementary hexad radical

In a perfect central extension of the native M₂₂ hexad stabilizer, a lift
of the specified A₆ complement splits off the full radical. If that radical
is elementary abelian, perfectness makes its coinvariants zero. Its literal
map to the native natural four-space is therefore a perfect central module
cover, so the five-dimensional even six-letter core surjects onto it.

The surjection preserves the lifted complement's conjugation action and
commutes with the original natural projection. No central kernel is removed
or assumed trivial.

Source: Aschbacher--Smith B.3.3, I.1.5--6 and I.2.2(6), printed pp.84,
408 and 412; the universal marked module cover is imported below.
-/

public section
open Subgroup Representation Representation.OneCohomology
open Sporadic.Mathieu
open scoped IsMulCommutative Pointwise

namespace Sporadic.Mathieu.M22CentralCover

/-- The full elementary radical is a marked quotient of the even six-letter core. -/
theorem hexad_augmentation_surjection
    {D : Type*} [Group D] [Finite D] [Group.IsPerfect D]
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (q : D →* MulAction.stabilizer M22 B) (hq : Function.Surjective q)
    (hc : q.ker ≤ center D)
    (s : alternatingGroup (Fin 6) →* D) (hs : q.comp s = m22HexadSection hB)
    [IsElementaryAbelian 2 (((m22SetAction B).ker).comap q)] :
    let R := ((m22SetAction B).ker).comap q
    let φ : alternatingGroup (Fin 6) →* MulAut R := MulAut.conjNormal.comp s
    let p : R →* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
      (m22HexadNaturalCoordinates hB).toMonoidHom.comp (q.subgroupComap (m22SetAction B).ker)
    ∃ b : Multiplicative (BinaryPermutation.core (Fin 6)) →* R,
      Function.Surjective b ∧
      (∀ a v, b (Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 6) a.val v.toAdd)) = φ a (b v)) ∧
      ∀ v, (p (b v)).toAdd = BinaryPermutation.coreToNatural (Fin 6) v.toAdd := by
  intro R φ p
  let k : R ⋊[φ] alternatingGroup (Fin 6) →* D :=
    SemidirectProduct.lift R.subtype s (fun _ => rfl)
  have hsinj : Function.Injective s := by
    intro a b hab
    apply m22HexadSection_injective hB
    exact (DFunLike.congr_fun hs a).symm.trans
      ((congrArg q hab).trans (DFunLike.congr_fun hs b))
  have hd : Disjoint R s.range := by
    apply disjoint_def.mpr
    rintro x hx ⟨a,rfl⟩
    have ha : m22HexadSection hB a = 1 :=
      (disjoint_def.mp (m22HexadSection_isComplement hB).disjoint)
        ((DFunLike.congr_fun hs a) ▸ hx) ⟨a,rfl⟩
    rw [show a = 1 from (m22HexadSection_injective hB) (ha.trans (map_one _).symm),map_one]
  have hksur : Function.Surjective k := by
    intro x
    obtain ⟨⟨n,a'⟩,he⟩ := (m22HexadSection_isComplement hB).2 (q x)
    obtain ⟨a,ha⟩ := a'.property
    have hr : x * (s a)⁻¹ ∈ R := by
      change q (x * (s a)⁻¹) ∈ (m22SetAction B).ker
      rw [map_mul,map_inv,show q (s a) = m22HexadSection hB a from DFunLike.congr_fun hs a,ha,←he]
      change n.val * a'.val * a'.val⁻¹ ∈ (m22SetAction B).ker
      rw [mul_inv_cancel_right]
      exact n.property
    exact ⟨⟨⟨x * (s a)⁻¹,hr⟩,a⟩,inv_mul_cancel_right x (s a)⟩
  have hkinj : Function.Injective k := by
    intro x y he
    have hh : (x.left,(⟨s x.right,x.right,rfl⟩ : s.range)) =
        (y.left,(⟨s y.right,y.right,rfl⟩ : s.range)) :=
      (Subgroup.mul_injective_of_disjoint hd) he
    apply SemidirectProduct.ext (congrArg Prod.fst hh)
    exact hsinj (congrArg (fun z : R × s.range => (z.2 : D)) hh)
  let E := MulEquiv.ofBijective k ⟨hkinj,hksur⟩
  let : Group.IsPerfect (R ⋊[φ] alternatingGroup (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  let σ := elementaryRepresentation (p := 2) φ
  have hp (a : alternatingGroup (Fin 6)) (r : R) :
      (p (φ a r)).toAdd = BinaryPermutation.naturalRepresentation (Fin 6) a.val (p r).toAdd := by
    let t := q.subgroupComap (m22SetAction B).ker
    have he : t (φ a r) = MulAut.conjNormal (m22HexadSection hB a) (t r) := by
      apply Subtype.ext
      change q (s a * r * (s a)⁻¹) = _
      rw [map_mul,map_mul,map_inv,show q (s a) = m22HexadSection hB a from DFunLike.congr_fun hs a]
      rfl
    change (m22HexadNaturalCoordinates hB (t (φ a r))).toAdd = _
    rw [he]
    exact m22HexadNaturalCoordinates_section hB a (t r)
  let P : σ.IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) :=
    (p.toAdditiveLeft.toZModLinearMap 2).intertwiningMap_of_isIntertwiningMap _ _
      (fun a r => hp a r.toMul)
  have hP : IsCover P := by
    refine ⟨?_,?_,elementary_coinvariants_eq_top_of_perfect φ⟩
    · intro v
      obtain ⟨r,hr⟩ := ((m22HexadNaturalCoordinates hB).surjective.comp
        (q.subgroupComap_surjective_of_surjective _ hq)) (Multiplicative.ofAdd v)
      exact ⟨Additive.ofMul r,congrArg Multiplicative.toAdd hr⟩
    · intro r hr a
      have hrq : q r.toMul = 1 := by
        have hp0 : p r.toMul = 1 := congrArg Multiplicative.ofAdd hr
        have hh : q.subgroupComap (m22SetAction B).ker r.toMul = 1 :=
          (m22HexadNaturalCoordinates hB).injective (hp0.trans (map_one _).symm)
        exact congrArg Subtype.val hh
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change s a * (r.toMul : D) * (s a)⁻¹ = (r.toMul : D)
      rw [mem_center_iff.mp (hc hrq) (s a),mul_inv_cancel_right]
  obtain ⟨b,hb,he,hp⟩ := BinaryPermutation.SixCover.core_quotient_of_alternating_cover σ P hP
  exact ⟨b.toAddMonoidHom.toMultiplicativeLeft,hb,he,hp⟩

end Sporadic.Mathieu.M22CentralCover
