module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedCoreInvolutions
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicPerfect
public import Mathlib.GroupTheory.Complement

/-!
# An involutory complement in the original cubic normalizer

The native sextet scalar has an explicit involutory inverter. The original
marked cocode quotient lifts that involution, and equivariance puts its lift
inside H = C_G(z). Commuting it with a scalar lift in the original normal
cubic subgroup gives a product of conjugate involutions with image of order
three. A power of this product has order three and is still inverted.
Sylow conjugacy inside the original cubic lift transports the inverter to
every original X without changing the cubic marking. It lies outside
C_H(X), whose index in N_H(X) is two, so its order-two subgroup is a literal
complement.

This proves the splitting clause of Aschbacher--Segev (4.9) under the genuine
marked cocode hypotheses already present in the original Mathieu consumer.
It uses neither a Todd complement nor LocalData-dependent fusion. The
construction of those packages from IsTypeJ4 alone is not asserted here.
The actual original consumer is MathieuJ4RecognitionApplication.CoreInvolutions.
Source: The uniqueness of groups of type J4, Invent. Math. 105 (1991),
(4.8)--(4.9), p.599, DOI 10.1007/BF01232280. The native hexacode
inverter is the existing attributed ATLAS construction; LICENSES/ATLAS.txt.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
noncomputable section
namespace CubicWitness
open Atlas.Codes MathieuCode.SextetLayers.CoordinateTransport

def nativeInverter (S : Sextet) : M24 :=
  (nativeStabilizerEquiv S (sextetSection (hexLift 0))).val

theorem nativeInverter_square (S : Sextet) : nativeInverter S ^ 2 = 1 := by
  change ((sextetStabilizer S).subtype (nativeStabilizerEquiv S (sextetSection (hexLift 0))))^2=1
  rw [←map_pow,←map_pow,←map_pow,pow_two,hexLift_sq,map_one,map_one,map_one]

theorem nativeInverter_inverts (S : Sextet) :
    nativeInverter S * nativeScalar S * (nativeInverter S)⁻¹ = (nativeScalar S)⁻¹ := by
  change ((sextetStabilizer S).subtype (nativeStabilizerEquiv S (sextetSection (hexLift 0)))) *
    ((sextetStabilizer S).subtype (nativeStabilizerEquiv S (sextetSection hexZ))) *
    ((sextetStabilizer S).subtype (nativeStabilizerEquiv S (sextetSection (hexLift 0))))⁻¹ =
    ((sextetStabilizer S).subtype (nativeStabilizerEquiv S (sextetSection hexZ)))⁻¹
  simp only [←map_inv,←map_mul]
  rw [hexLift_inverts]

theorem nativeInverter_order (S : Sextet) : orderOf (nativeInverter S) = 2 := by
  apply orderOf_eq_prime (nativeInverter_square S)
  intro he
  have hi := nativeInverter_inverts S
  rw [he,one_mul,inv_one,mul_one] at hi
  have hs : nativeScalar S ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (fun t => t * nativeScalar S) hi).trans (inv_mul_cancel _)
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [nativeScalar_order] at hd
  norm_num at hd
end CubicWitness

/-- Extract an inverted cubic from a product of conjugate involutions,
inside the original normal subgroup. -/
theorem inverted_cubic_of_commutator
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) [A.Normal]
    (w : H) (hw : w^2=1) (x : A)
    (hthree : 3 ∣ orderOf (w*x.val*w⁻¹*x.val⁻¹)) :
    ∃ y : A, orderOf y=3 ∧ w*y.val*w⁻¹=y.val⁻¹ := by
  let c : A := ⟨w*x.val*w⁻¹*x.val⁻¹,
    A.mul_mem ((inferInstance : A.Normal).conj_mem x.val x.property w) (A.inv_mem x.property)⟩
  have hc : 3 ∣ orderOf c := by rw [←Subgroup.orderOf_coe c]; exact hthree
  let y := c ^ (orderOf c / 3)
  have hy : orderOf y=3 := orderOf_pow_orderOf_div (orderOf_pos c).ne' hc
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
  have hww : w*w=1 := by simpa only [pow_two] using hw
  have hci : w*c.val*w⁻¹=c.val⁻¹ := by
    change w*(w*x.val*w⁻¹*x.val⁻¹)*w⁻¹=(w*x.val*w⁻¹*x.val⁻¹)⁻¹
    simp only [mul_inv_rev,inv_inv,hwi,←mul_assoc,hww,one_mul]
  refine ⟨y,hy,?_⟩
  change MulAut.conj w (c.val ^ (orderOf c / 3)) = (c.val ^ (orderOf c / 3))⁻¹
  rw [map_pow]
  change (w*c.val*w⁻¹) ^ (orderOf c / 3) = _
  rw [hci,inv_pow]

variable {G : Type*} [Group G] [Finite G]

theorem marked_cocode_exists_inverted_cubic
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G))) :
    ∃ Y : Sylow 3 (CubicLift.subgroup e), ∃ w : centralizer (z : G), orderOf w=2 ∧
      ∀ y ∈ cubicSylowImage e Y, w*y*w⁻¹=y⁻¹ := by
  obtain ⟨n,hn,hn2⟩ := marked_cocode_involution_lift W f hf hk E hE z S hz h e
    (CubicWitness.nativeInverter S) (CubicWitness.nativeInverter_order S)
  have hnH : n.val ∈ centralizer (z : G) := by
    apply (marked_cocode_plane_preimage W f E hE z S hz).ge
    change f n ∈ sextetStabilizer S
    rw [hn]
    exact (SextetLayers.CoordinateTransport.nativeStabilizerEquiv S
      (Atlas.Codes.sextetSection (Atlas.Codes.hexLift 0))).property
  let w : centralizer (z : G) := ⟨n.val,hnH⟩
  have hw2 : orderOf w=2 := by
    rw [←Subgroup.orderOf_coe w,Subgroup.orderOf_coe n]
    exact hn2
  obtain ⟨hLN,x,hfx,_⟩ := marked_cocode_source_cubic_lift W f hf hk E hE z S hz h e
  let j : CubicLift.subgroup e →* normalizer (W : Set G) := {
    toFun t := ⟨t.val.val,hLN t.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hfj : f (j x) = CubicWitness.nativeScalar S := hfx
  let cN := n*j x*n⁻¹*(j x)⁻¹
  have hcimage : f cN = (CubicWitness.nativeScalar S)⁻¹ * (CubicWitness.nativeScalar S)⁻¹ := by
    change f (n*j x*n⁻¹*(j x)⁻¹) = _
    rw [map_mul,map_mul,map_mul,map_inv,map_inv,hn,hfj,CubicWitness.nativeInverter_inverts]
  have hco : orderOf (f cN)=3 := by
    rw [hcimage,←pow_two,orderOf_pow,orderOf_inv,CubicWitness.nativeScalar_order]
    norm_num
  have hthree : 3 ∣ orderOf (w*x.val*w⁻¹*x.val⁻¹) := by
    have hh : 3 ∣ orderOf cN := hco ▸ orderOf_map_dvd f cN
    rw [←Subgroup.orderOf_coe cN] at hh
    rw [←Subgroup.orderOf_coe (w*x.val*w⁻¹*x.val⁻¹)]
    exact hh
  obtain ⟨y,hy,hwy⟩ := inverted_cubic_of_commutator (CubicLift.subgroup e) w
    (hw2 ▸ pow_orderOf_eq_one w) x hthree
  let Y : Sylow 3 (CubicLift.subgroup e) := Sylow.ofCard (zpowers y) (by
    rw [Nat.card_zpowers,hy,CubicLift.subgroup_card e h]
    decide +kernel)
  refine ⟨Y,w,hw2,?_⟩
  have hY : cubicSylowImage e Y = zpowers y.val := MonoidHom.map_zpowers _ y
  rw [hY]
  rintro t ⟨k,rfl⟩
  change MulAut.conj w (y.val ^ k) = (y.val ^ k)⁻¹
  rw [map_zpow]
  change (w*y.val*w⁻¹)^k = _
  rw [hwy,inv_zpow]

/-- Sylow conjugacy retains the original cubic marking and gives an
involutory inverter for every original cubic Sylow choice. -/
theorem fullCubic_inverter_transport {z : G} (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (Y : Sylow 3 (CubicLift.subgroup e)) (w : centralizer z) (hw : orderOf w=2)
    (hinv : ∀ y ∈ cubicSylowImage e Y, w*y*w⁻¹=y⁻¹)
    (X : Sylow 3 (CubicLift.subgroup e)) :
    ∃ v : fullCubicNormalizer e X, orderOf v=2 ∧
      v.val ∉ fullCubicCentralizer e X ∧
      ∀ x ∈ cubicSylowImage e X, v.val*x*v.val⁻¹=x⁻¹ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (CubicLift.subgroup e) Y X
  have he := congrArg (fun P : Sylow 3 (CubicLift.subgroup e) =>
    (P : Subgroup (CubicLift.subgroup e))) hg
  rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at he
  have hh := congrArg (Subgroup.map (CubicLift.subgroup e).subtype) he
  have hX : (cubicSylowImage e Y).map (MulAut.conj g.val).toMonoidHom = cubicSylowImage e X := by
    rw [cubicSylowImage,map_map]
    change ((Y : Subgroup (CubicLift.subgroup e)).map (MulAut.conj g).toMonoidHom).map
      (CubicLift.subgroup e).subtype = (X : Subgroup (CubicLift.subgroup e)).map
        (CubicLift.subgroup e).subtype at hh
    rw [map_map] at hh
    exact hh
  let v := MulAut.conj g.val w
  have hv : orderOf v=2 := ((MulAut.conj g.val).orderOf_eq w).trans hw
  have hvi : ∀ x ∈ cubicSylowImage e X, v*x*v⁻¹=x⁻¹ := by
    rw [←hX]
    rintro x ⟨y,hy,rfl⟩
    have hh := congrArg (MulAut.conj g.val) (hinv y hy)
    change (MulAut.conj g.val) w * (MulAut.conj g.val) y *
      ((MulAut.conj g.val) w)⁻¹ = ((MulAut.conj g.val) y)⁻¹
    simpa only [map_mul,map_inv] using hh
  have hvN : v ∈ fullCubicNormalizer e X := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      change v*y*v⁻¹ ∈ cubicSylowImage e X
      rw [hvi y hy]
      exact (cubicSylowImage e X).inv_mem hy
    · intro x hx
      refine ⟨x⁻¹,(cubicSylowImage e X).inv_mem hx,?_⟩
      change v*x⁻¹*v⁻¹=x
      rw [hvi _ ((cubicSylowImage e X).inv_mem hx),inv_inv]
  have hvC : v ∉ fullCubicCentralizer e X := by
    intro hvc
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3
      (by rw [cubicSylow_card e h X])
    have hxA : (x.val : CubicLift.subgroup e).val ∈ cubicSylowImage e X :=
      mem_map_of_mem _ x.property
    have hc := hvc x.val.val hxA
    have he := hvi x.val.val hxA
    rw [←hc,mul_inv_cancel_right] at he
    have hx2 : x^2=1 := by
      apply Subtype.ext
      apply Subtype.ext
      change x.val.val ^ 2=1
      rw [pow_two]
      exact (congrArg (fun t => t*x.val.val) he).trans (inv_mul_cancel _)
    have hd := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at hd
    norm_num at hd
  exact ⟨⟨v,hvN⟩,(Subgroup.orderOf_coe _).symm.trans hv,hvC,hvi⟩

/-- A genuine involution in the other coset splits the original normalizer. -/
theorem fullCubic_complement_of_inverter {z : G} (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (CubicLift.subgroup e)) (v : fullCubicNormalizer e X)
    (hv : orderOf v=2) (hout : v.val ∉ fullCubicCentralizer e X) :
    IsComplement' ((fullCubicCentralizer e X).subgroupOf (fullCubicNormalizer e X))
      (zpowers v) := by
  classical
  let C := (fullCubicCentralizer e X).subgroupOf (fullCubicNormalizer e X)
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_zpowers,hv]
    have hh := C.card_mul_index
    rw [show C.index=2 from fullCubicCentralizer_normalizer_index h e X] at hh
    exact hh
  · apply disjoint_def.mpr
    intro x hxC hxv
    rw [mem_zpowers_iff_mem_range_orderOf,hv] at hxv
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hxv
    have hi2 := Finset.mem_range.mp hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl|rfl
    · simpa using he.symm
    · have hxv : x=v := by simpa using he.symm
      exact (hout (hxv ▸ hxC)).elim
/-- AS91 (4.9)'s splitting clause, with the same original cubic marking
and an arbitrary original Sylow choice. -/
theorem marked_fullCubicNormalizer_split
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G)))
    (X : Sylow 3 (CubicLift.subgroup e)) :
    ∃ v : fullCubicNormalizer e X, orderOf v=2 ∧
      v.val ∉ fullCubicCentralizer e X ∧
      (∀ x ∈ cubicSylowImage e X, v.val*x*v.val⁻¹=x⁻¹) ∧
      IsComplement' ((fullCubicCentralizer e X).subgroupOf (fullCubicNormalizer e X))
        (zpowers v) := by
  obtain ⟨Y,w,hw,hinv⟩ := marked_cocode_exists_inverted_cubic W f hf hk E hE z S hz h e
  obtain ⟨v,hv,hout,hvi⟩ := fullCubic_inverter_transport h e Y w hw hinv X
  exact ⟨v,hv,hout,hvi,fullCubic_complement_of_inverter h e X v hv hout⟩

end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
