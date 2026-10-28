module
public import Theory.Representation.BinaryTensorThree.PlaneFixed
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The literal fixed space through a tensor action with kernel

The full preimage of the paired plane radicals defines R in the original
acting group. Equivariance identifies the actual ambient intersection C_V(R)
with the marked four-space. Sylow conjugacy aligns the full action and the
vector coordinates together; it places R in the original Sylow subgroup.
An elementary nine lifts through the two-group kernel and acts faithfully on
this exact fixed subgroup, supplying the faithful-action input used in
source 8.3.8(b) without an extra action hypothesis. The ambient quasithin application is in QuietTensorPlaneFixed.

Source: Aschbacher--Smith, 8.3.8(a)--(c), printed p.725.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace BinaryTensorThree.PlaneFixed
variable {G : Type*} [_root_.Group G] [Finite G]
  (V H : Subgroup G) [IsElementaryAbelian 2 V]
  (hHV : H ≤ normalizer (V : Set G))
  (q : H →* Actor) (hq : Function.Surjective q)
  (e : Additive V ≃ₗ[ZMod 2] Space)
  (he : ∀ (a : H) (v : Additive V),
    e (Additive.ofMul (V.normalizerMonoidHom ⟨a,hHV a.property⟩ v.toMul)) =
      action (PointParabolic.tensorHom (q a)) (e v))

/-- Full preimage of the two marked plane radicals, including the action kernel. -/
@[expose] def originalRadical : Subgroup G := (radicalPair.range.comap q).map H.subtype

/-- The fixed subgroup is the literal ambient intersection C_V(R). -/
@[expose] def originalFixed : Subgroup G := V ⊓ centralizer (originalRadical H q : Set G)

include hq he in
omit [Finite G] in
theorem mem_originalFixed (v : V) :
    (v : G) ∈ originalFixed V H q ↔ e (Additive.ofMul v) ∈ square := by
  rw [←radical_fixed_iff]
  constructor
  · intro hv a
    obtain ⟨g,hg⟩ := hq (radicalPair a)
    have hgR : (g : G) ∈ originalRadical H q := ⟨g,by change q g ∈ radicalPair.range; rw [hg]; exact ⟨a,rfl⟩,rfl⟩
    have hcomm := hv.2 g hgR
    have hconj : V.normalizerMonoidHom ⟨g,hHV g.property⟩ v = v := by
      apply Subtype.ext
      change (g : G)*(v : G)*(g : G)⁻¹ = v
      rw [hcomm,mul_inv_cancel_right]
    rw [←hg,←he]
    change e (Additive.ofMul (V.normalizerMonoidHom ⟨g,hHV g.property⟩ v)) = _
    rw [hconj]
  · intro hv
    refine ⟨v.property,?_⟩
    rintro r ⟨g,hg,rfl⟩
    obtain ⟨a,ha⟩ := hg
    have hh := he g (Additive.ofMul v)
    rw [←ha,hv a] at hh
    have hh' := congrArg (fun x : Additive V => (x.toMul : G)) (e.injective hh)
    exact mul_inv_eq_iff_eq_mul.mp hh'

include hq he in
omit [Finite G] in
theorem originalFixed_normalized_by_line (B : Subgroup G) (hBH : B ≤ H)
    (hB : (B.subgroupOf H).map q ≤ Matrix.PSL3Two.WreathPair.line) :
    B ≤ normalizer (originalFixed V H q : Set G) := by
  apply le_normalizer_iff.mpr
  intro b hb v hv
  let a : H := ⟨b,hBH hb⟩
  have hval : b*v*b⁻¹ ∈ V := (mem_normalizer_iff.mp (hHV a.property) v).mp hv.1
  apply (mem_originalFixed V H hHV q hq e he ⟨_,hval⟩).mpr
  have hv' := (mem_originalFixed V H hHV q hq e he ⟨v,hv.1⟩).mp hv
  have hh := line_preserves_square (q a) (hB (mem_map_of_mem q hb)) _ hv'
  rw [←he] at hh
  exact hh

include hq he in
omit [Finite G] in
theorem originalFixed_contains_point {z : G} (hz : z ∈ V)
    (hpoint : e (Additive.ofMul ⟨z,hz⟩) = point) : z ∈ originalFixed V H q := by
  apply (mem_originalFixed V H hHV q hq e he ⟨z,hz⟩).mpr
  rw [hpoint]
  exact point_mem_square

include hq he in
/-- Lift the actual cubic plane through the two-group kernel. Its restriction
to C_V(R) is faithful, so no fixed-space or faithful-action premise is added. -/
theorem exists_originalFixed_faithful_nine (hk : IsPGroup 2 q.ker) :
    ∃ A : Subgroup G, IsElementaryAbelian 3 A ∧ Nat.card A = 9 ∧ A ≤ H ∧
      ∃ hAU : A ≤ normalizer (originalFixed V H q : Set G),
        Function.Injective ((originalFixed V H q).normalizerMonoidHom.comp (inclusion hAU)) := by
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨A,hA,hm,hcard⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    q hq hcop cubicPair.range
  let : IsElementaryAbelian 3 A := hA
  let B := A.map H.subtype
  have hBH : B ≤ H := map_subtype_le A
  have hBA : B.subgroupOf H = A := by
    exact comap_map_eq_self_of_injective H.subtype_injective A
  have hBline : (B.subgroupOf H).map q ≤ Matrix.PSL3Two.WreathPair.line := by
    rw [hBA,hm]
    rintro x ⟨a,rfl⟩
    exact cubic_mem_line a
  have hBN := originalFixed_normalized_by_line V H hHV q hq e he B hBH hBline
  refine ⟨B,IsElementaryAbelian.map_subtype,?_,hBH,hBN,?_⟩
  · rw [card_map_of_injective H.subtype_injective,hcard,card_cubic_range]
  · apply (injective_iff_map_eq_one _).mpr
    intro b hb
    let a : A := ⟨⟨b,hBH b.property⟩,hBA ▸ b.property⟩
    have ha : q a.val ∈ cubicPair.range := hm ▸ mem_map_of_mem q a.property
    obtain ⟨c,hc⟩ := ha
    have hc1 : c = 1 := by
      apply cubic_faithful c
      intro X hX
      obtain ⟨v,rfl⟩ := e.surjective X
      have hv := (mem_originalFixed V H hHV q hq e he v.toMul).mpr hX
      have hfix := congrArg (fun f : MulAut (originalFixed V H q) => f ⟨v.toMul,hv⟩) hb
      have hval : (b : G)*(v.toMul : G)*(b : G)⁻¹ = v.toMul :=
        congrArg (originalFixed V H q).subtype hfix
      have heq : V.normalizerMonoidHom ⟨a.val,hHV a.val.property⟩ v.toMul = v.toMul :=
        Subtype.ext hval
      rw [hc,←he,heq]
      rfl
    have haq : q a.val = 1 := by rw [←hc,hc1,map_one]
    have hi := injective_comp_subtype_of_coprime_ker q hcop A
      (IsElementaryAbelian.isPGroup 3 A)
    have ha1 : a = 1 := hi (haq.trans (map_one _).symm)
    exact Subtype.ext (congrArg (fun x : A => ((x : H) : G)) ha1)

include hq he in
/-- Align the tensor marking with a prescribed Sylow two-subgroup of the
original actor, transporting the vector coordinates by the same conjugation. -/
theorem exists_sylow_marking (S : Sylow 2 H) :
    ∃ (p : H →* Actor) (b : Additive V ≃ₗ[ZMod 2] Space),
      Function.Surjective p ∧ p.ker = q.ker ∧
      (S : Subgroup H).map p = Matrix.PSL3Two.WreathPair.borel ∧
      ∀ (a : H) (v : Additive V),
        b (Additive.ofMul (V.normalizerMonoidHom ⟨a,hHV a.property⟩ v.toMul)) =
          action (PointParabolic.tensorHom (p a)) (b v) := by
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq Actor (S.mapSurjective hq)
    Matrix.PSL3Two.WreathPair.sylow
  let p := (MulAut.conj c).toMonoidHom.comp q
  let f := PointParabolic.tensorHom
  let b := e.trans (LinearEquiv.ofBijective (action (f c)) (action.apply_bijective (f c)))
  refine ⟨p,b,(MulAut.conj c).surjective.comp hq,?_,?_,?_⟩
  · exact MonoidHom.ker_comp_of_injective _ _ (MulAut.conj c).injective
  · have hh := congrArg Sylow.toSubgroup hc
    rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def,Sylow.coe_mapSurjective,
      Matrix.PSL3Two.WreathPair.sylow_eq] at hh
    change ((S : Subgroup H).map q).map (MulAut.conj c).toMonoidHom = _ at hh
    simpa only [p,map_map] using hh
  · intro a v
    change action (f c) (e _) = action (f (c*q a*c⁻¹)) (action (f c) (e v))
    rw [he]
    simp only [map_mul,map_inv,Module.End.mul_apply]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,mul_one]
    rw [f.map_mul]

omit [Finite G] in
/-- The full radical preimage lies in the original Sylow subgroup, including
the two-group action kernel. -/
theorem originalRadical_le_sylow (S : Sylow 2 H) (hk : IsPGroup 2 q.ker)
    (hS : (S : Subgroup H).map q = Matrix.PSL3Two.WreathPair.borel) :
    originalRadical H q ≤ (S : Subgroup H).map H.subtype := by
  apply map_mono
  have hr : radicalPair.range ≤ Matrix.PSL3Two.WreathPair.borel := by
    rintro a ⟨b,rfl⟩
    exact radical_mem_borel b
  rw [←hS] at hr
  have hh := comap_mono (f := q) hr
  rw [comap_map_eq,sup_eq_left.mpr (hk.le_sylow_of_normal S)] at hh
  exact hh

end BinaryTensorThree.PlaneFixed
