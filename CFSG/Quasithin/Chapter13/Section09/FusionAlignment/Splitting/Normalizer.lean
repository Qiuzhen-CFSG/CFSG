module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Complement
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.NaturalModule
/-!
# The original normalizer as a marked affine five-point group

The actual complement to B maps bijectively to the literal five-point
permutation quotient. Combining that complement with the equivariant binary
module identification gives N_G(B) ≃ 2⁴ ⋊ S₅. The equivalence retains both
B and the marked involution t, so centralizer computations transport back to
the original configuration. No extension-classification assumption is used.
Source: Aschbacher–Smith 13.9.9–10, printed p.973.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The original N_G(B) is the actual marked binary affine five-point group. -/
theorem exists_binary_five_normalizer {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃e:BinaryFiveAffine.W≃*normalizer (m.B:Set G),
      (e BinaryFiveAffine.t:G)=m.t ∧
      BinaryFiveAffine.vectorGroup.map e.toMonoidHom = m.B.subgroupOf (normalizer (m.B:Set G)) := by
  obtain ⟨eB,a,ha,hker,ht,hact⟩ := m.exists_binary_five_module hG
  obtain ⟨L,hL⟩ := m.exists_normalizer_complement
  let K := normalizer (m.B:Set G)
  let V := m.B.subgroupOf K
  let eV : BinaryFiveAffine.V≃*V := eB.trans (subgroupOfEquivOfLe m.B.le_normalizer).symm
  let aL := a.comp L.subtype
  have haL : Function.Bijective aL := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff aL).mp
      apply eq_bot_iff.mpr
      intro x hx
      have hxV : (x:K)∈V := by
        change (x:K)∈m.B.subgroupOf K
        rw [←hker]
        exact hx
      exact Subtype.ext (disjoint_def.mp hL.disjoint hxV x.property)
    · intro σ
      obtain ⟨k,hk⟩ := ha σ
      obtain ⟨⟨v,l⟩,he⟩ := hL.2 k
      have hv : a v=1 := by
        change (v:K)∈a.ker
        rw [hker]
        exact v.property
      refine ⟨l,?_⟩
      change a (l:K)=σ
      rw [←hk,←he,map_mul,hv,one_mul]
  let eL : L≃*BinaryFiveAffine.S := MulEquiv.ofBijective aL haL
  let fV := V.subtype.comp eV.toMonoidHom
  let fS := L.subtype.comp eL.symm.toMonoidHom
  have hfa (σ:BinaryFiveAffine.S) : a (fS σ)=σ := eL.apply_symm_apply σ
  have hfv (x:BinaryFiveAffine.V) : a (fV x)=1 := by
    change fV x∈a.ker
    rw [hker]
    exact (eV x).property
  have hcompat (σ:BinaryFiveAffine.S) (x:BinaryFiveAffine.V) :
      fV (BinaryFiveAffine.action σ x)=fS σ*fV x*(fS σ)⁻¹ := by
    apply Subtype.ext
    change (eB (BinaryFiveAffine.action σ x):G)=
      (fS σ:G)*(eB x:G)*(fS σ:G)⁻¹
    simpa only [hfa] using hact (fS σ) x
  let f : BinaryFiveAffine.W→*K := SemidirectProduct.lift fV fS (fun σ=>
    MonoidHom.ext (hcompat σ))
  have hfa' (x:BinaryFiveAffine.W) : a (f x)=x.right := by
    change a (fV x.left*fS x.right)=x.right
    rw [map_mul,hfv,hfa,one_mul]
  have hbij : Function.Bijective f := by
    constructor
    · intro x y he
      have hr : x.right=y.right := (hfa' x).symm.trans ((congrArg a he).trans (hfa' y))
      have hv : fV x.left=fV y.left := by
        change fV x.left*fS x.right=fV y.left*fS y.right at he
        rw [hr] at he
        exact mul_right_cancel he
      exact SemidirectProduct.ext
        (eV.injective (Subtype.ext hv)) hr
    · intro k
      obtain ⟨⟨v,l⟩,he⟩ := hL.2 k
      refine ⟨⟨eV.symm v,eL l⟩,?_⟩
      change (eV (eV.symm v):K)*(eL.symm (eL l):K)=k
      rw [eV.apply_symm_apply,eL.symm_apply_apply]
      exact he
  let e : BinaryFiveAffine.W≃*K := MulEquiv.ofBijective f hbij
  have heV (x:BinaryFiveAffine.V) : e (SemidirectProduct.inl x)=fV x := by
    change fV x*fS 1=fV x
    rw [map_one,mul_one]
  refine ⟨e,?_,?_⟩
  · change (e (SemidirectProduct.inl BinaryFiveAffine.pair01):G)=m.t
    rw [heV]
    exact ht
  · ext x
    constructor
    · rintro ⟨w,⟨v,rfl⟩,rfl⟩
      change e (SemidirectProduct.inl v)∈V
      rw [heV]
      exact (eV v).property
    · intro hx
      refine ⟨SemidirectProduct.inl (eV.symm ⟨x,hx⟩),⟨_,rfl⟩,?_⟩
      change e (SemidirectProduct.inl (eV.symm ⟨x,hx⟩))=x
      rw [heV]
      exact congrArg Subtype.val (eV.apply_symm_apply ⟨x,hx⟩)

end CFSG.Quasithin.Chapter13.Section09.Marking
