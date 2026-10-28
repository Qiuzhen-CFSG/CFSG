module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCubicWitness
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicCentralizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.OverlapIndices
public import Theory.GroupTheory.CoprimeSubgroupCentralizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups.ElementLift
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Perfectness of the full cubic centralizer from the marked cocode

The actual elementary kernel allows commuting actors to lift through the
original Mathieu quotient. The native displacement certificate therefore
puts the original marker z in a commutator of subgroups centralizing the
same cubic. The index-77 point-plane overlap contains the entire original
cubic lift. Its normal image in the sextet stabilizer contains the native
scalar, and coprime lifting chooses the cubic INSIDE that original lift.
Thus the witness is in the actual C_H(X), before quotienting by z.

The earlier central-extension theorem then makes C_H(X) perfect and equal
to its layer. Sylow conjugacy proves this for every original X, keeping the
original cubic quotient e. The group is quasisimple with the already proved
center of order six. The Mathieu application constructs every marked-cocode
premise from its original arguments; no Todd splitting is assumed.

This proves the perfectness clause of Aschbacher--Segev (4.9) for a genuine
marked cocode normalizer. Construction of that normalizer from IsTypeJ4
alone, the involutory splitting clause, and ambient recognition remain
separate obligations. Source: The uniqueness of groups of type J4,
Invent. Math. 105 (1991), p.599, DOI 10.1007/BF01232280.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped commutatorElement BigOperators IsMulCommutative
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Lift the native cubic-fixed displacement certificate through the original
marked cocode quotient. Both commutator factors centralize the same cubic. -/
theorem marked_cocode_cubic_commutator
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (x : normalizer (W : Set G)) (hx : x ^ 3 = 1)
    (hfx : f x = CubicWitness.nativeScalar S) :
    (z : G) ∈ ⁅W ⊓ Subgroup.centralizer ({(x : G)} : Set G),
      normalizer (W : Set G) ⊓ Subgroup.centralizer ({(z : G)} : Set G) ⊓
        Subgroup.centralizer ({(x : G)} : Set G)⁆ := by
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe W.le_normalizer).toEquiv]
    have hc : Nat.card W = 2 ^ 11 := by
      change Nat.card (Additive W) = _
      rw [Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2),
        finrank_cocode, Nat.card_zmod]
    rw [hc]
    decide
  have hp : IsPGroup 3 (zpowers x) := isPGroup_iff_card_dvd_pow.mpr
    ⟨1,by simpa only [pow_one,Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hx⟩
  have hmap := map_centralizer_eq_of_isPGroup_of_surjective_coprime 3
    (zpowers x) hp f hf hcop
  have hlift (i : Fin 3) : ∃ n : normalizer (W : Set G),
      Commute n x ∧ f n = CubicWitness.nativeActor S i := by
    have hc : CubicWitness.nativeActor S i ∈
        Subgroup.centralizer ((zpowers x).map f : Set M24) := by
      rw [MonoidHom.map_zpowers, hfx]
      intro y hy
      obtain ⟨k,rfl⟩ := hy
      exact ((CubicWitness.nativeActor_commutes S i).zpow_right k).eq.symm
    obtain ⟨n,hn,he⟩ := hmap.ge hc
    exact ⟨n,(hn x (mem_zpowers x)).symm,he⟩
  choose n hn hfn using hlift
  let v (i : Fin 3) : W := (E.symm (CubicWitness.nativeVector S i)).toMul
  have hvE (i : Fin 3) : E (Additive.ofMul (v i)) = CubicWitness.nativeVector S i :=
    E.apply_symm_apply _
  have hvc (i : Fin 3) : (v i : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    have he := hE x (v i)
    rw [hfx,hvE,CubicWitness.nativeVector_fixed] at he
    have hfix : W.normalizerMonoidHom x (v i) = v i := by
      apply Additive.ofMul.injective
      exact E.injective (he.trans (hvE i).symm)
    have hh := congrArg Subtype.val hfix
    change (x : G) * (v i : G) * (x : G)⁻¹ = (v i : G) at hh
    exact mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul.mp hh).symm)
  have hnz (i : Fin 3) : (n i : G) ∈ Subgroup.centralizer ({(z : G)} : Set G) := by
    have he := hE (n i) z
    rw [hfn,hz] at he
    rw [sextetVector_fixed S ⟨_,CubicWitness.nativeActor_mem S i⟩] at he
    have hfix : W.normalizerMonoidHom (n i) z = z := by
      apply Additive.ofMul.injective
      exact E.injective (he.trans hz.symm)
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix))
  let delta (i : Fin 3) : W := W.normalizerMonoidHom (n i) (v i) * (v i)⁻¹
  have hdE (i : Fin 3) : E (Additive.ofMul (delta i)) =
      cocodeRepresentation (CubicWitness.nativeActor S i) (CubicWitness.nativeVector S i) -
        CubicWitness.nativeVector S i := by
    dsimp only [delta]
    rw [ofMul_mul, ofMul_inv, map_add, map_neg,hE,hfn,hvE]
    exact (sub_eq_add_neg _ _).symm
  have hzprod : delta 0 * delta 1 * delta 2 = z := by
    apply Additive.ofMul.injective
    apply E.injective
    change E (Additive.ofMul (delta 0) + Additive.ofMul (delta 1) + Additive.ofMul (delta 2)) = _
    rw [map_add,map_add,hdE,hdE,hdE,hz]
    simpa only [Fin.sum_univ_three]
      using CubicWitness.native_displacement_sum S
  let A := W ⊓ Subgroup.centralizer ({(x : G)} : Set G)
  let B := normalizer (W : Set G) ⊓ Subgroup.centralizer ({(z : G)} : Set G) ⊓
    Subgroup.centralizer ({(x : G)} : Set G)
  have hd (i : Fin 3) : (delta i : G) ∈ ⁅A,B⁆ := by
    rw [commutator_comm]
    have hnB : (n i : G) ∈ B := ⟨⟨(n i).property,hnz i⟩,
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hn i).eq)⟩
    exact commutator_mem_commutator hnB ⟨(v i).property,hvc i⟩
  have hh := (⁅A,B⁆).mul_mem ((⁅A,B⁆).mul_mem (hd 0) (hd 1)) (hd 2)
  change ((delta 0 * delta 1 * delta 2 : W) : G) ∈ ⁅A,B⁆ at hh
  rwa [hzprod] at hh
end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicWitness
open Subgroup Atlas.Codes Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode.SextetLayers.CoordinateTransport

/-- A normal subgroup of the original cubic-lift order admits a scalar lift
of order three through an elementary kernel. -/
theorem exists_scalar_lift {B : Type*} [Group B] [Finite B]
    (S : Sextet) (q : B →* sextetStabilizer S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (L : Subgroup B) [L.Normal]
    (hL : Nat.card L = 3 * 2^13) :
    ∃ x : L, q x.val = nativeStabilizerEquiv S scalar ∧ x ^ 3 = 1 := by
  let A := L.map q
  let : A.Normal := Subgroup.Normal.map inferInstance q hq
  let r := q.subgroupMap L
  have hrk : IsPGroup 2 r.ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  obtain ⟨n,hn⟩ := hrk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card r.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hc := r.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective L),card_top,hL] at hc
  have hthree : 3 ∣ Nat.card A := by
    have hd : 3 ∣ Nat.card r.ker * Nat.card A := by rw [hc]; exact dvd_mul_right _ _
    exact (Nat.prime_three.dvd_mul.mp hd).resolve_left
      (fun hd => by
        rw [hn] at hd
        have hh := Nat.prime_three.dvd_of_dvd_pow hd
        norm_num at hh)
  have hfive : ¬ 5 ∣ Nat.card A := by
    intro hd
    have he := hd.trans (L.card_map_dvd q)
    rw [hL] at he
    norm_num at he
  have hm := nativeScalar_mem_normal S A hthree hfive
  let t : A := ⟨nativeStabilizerEquiv S scalar,hm⟩
  have ht : t^3=1 := by
    apply Subtype.ext
    change (nativeStabilizerEquiv S scalar)^3=1
    rw [←map_pow,scalar_cube,map_one]
  obtain ⟨x,hx,hpow⟩ := exists_prime_exponent_lift r (q.subgroupMap_surjective L) hcop t ht
  exact ⟨x,congrArg Subtype.val hx,hpow⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicWitness

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup LocalGeometry Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped IsMulCommutative
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- The native scalar lifts INSIDE the original cubic lift in H, with no
change to the marked cocode quotient or the original map H→H/Q. -/
theorem marked_cocode_source_cubic_lift
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G))) :
    ∃ (hLN : CubicLift.subgroup e ≤ (normalizer (W : Set G)).subgroupOf (centralizer (z : G)))
      (x : CubicLift.subgroup e),
      f ⟨x.val.val,hLN x.property⟩ = CubicWitness.nativeScalar S ∧ x ^ 3 = 1 := by
  let N := normalizer (W : Set G)
  let P := (centralizer (z : G)).subgroupOf N
  have hWc : Nat.card W = 2048 := by
    change Nat.card (Additive W) = _
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hc := marked_cocode_plane_card W f hf hk hWc E hE z S hz
  have hLN := marked_pointPlane_contains_cubic h e N hc
  let j : P →* centralizer (z : G) := {
    toFun p := ⟨p.val.val,p.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := fun a b hh =>
    Subtype.ext (Subtype.ext (congrArg (fun t : centralizer (z : G) => t.val) hh))
  let Q := (CubicLift.subgroup e).comap j
  let r : Q →* CubicLift.subgroup e := {
    toFun q := ⟨j q.val,q.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hri : Function.Injective r := fun a b hh =>
    Subtype.ext (hj (congrArg Subtype.val hh))
  have hrs : Function.Surjective r := by
    intro q
    exact ⟨⟨⟨⟨q.val.val,hLN q.property⟩,q.val.property⟩,q.property⟩,rfl⟩
  have hQc : Nat.card Q = 3*2^13 :=
    (Nat.card_congr (MulEquiv.ofBijective r ⟨hri,hrs⟩).toEquiv).trans (CubicLift.subgroup_card e h)
  have hpre := marked_cocode_plane_preimage W f E hE z S hz
  let q : P →* sextetStabilizer S := (f.comp P.subtype).codRestrict _ (fun p => by
    exact (show P = (sextetStabilizer S).comap f from hpre).le p.property)
  have hqs : Function.Surjective q := by
    intro s
    obtain ⟨n,hn,he⟩ := (marked_cocode_plane_image W f hf E hE z S hz).ge s.property
    exact ⟨⟨n,hn⟩,Subtype.ext he⟩
  have hqk : q.ker = f.ker.comap P.subtype := by
    ext p
    change (q p = 1) ↔ f p.val = 1
    exact Subtype.ext_iff
  have hq2 : IsPGroup 2 q.ker := by
    rw [hqk,hk]
    exact ((IsElementaryAbelian.isPGroup 2 W).comap_subtype).comap_subtype
  obtain ⟨x,hx,hpow⟩ := CubicWitness.exists_scalar_lift S q hqs hq2 Q hQc
  refine ⟨hLN,r x,?_,?_⟩
  · exact congrArg Subtype.val hx
  · rw [←map_pow,hpow,map_one]
end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition


namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup LocalGeometry Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped IsMulCommutative
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- The actual marker lies in the derived group of a source cubic centralizer,
using the transported Todd-module displacement witness. -/
theorem marked_cocode_exists_perfect_cubic
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G))) :
    ∃ X : Sylow 3 (CubicLift.subgroup e), Group.IsPerfect (fullCubicCentralizer e X) := by
  obtain ⟨hLN,x,hfx,hx⟩ := marked_cocode_source_cubic_lift W f hf hk E hE z S hz h e
  let n : normalizer (W : Set G) := ⟨x.val.val,hLN x.property⟩
  have hn : n^3=1 := congrArg (fun t : CubicLift.subgroup e =>
    (⟨t.val.val,hLN t.property⟩ : normalizer (W : Set G))) hx
  have hxo : orderOf x = 3 := by
    apply orderOf_eq_prime hx
    intro he
    have hh : CubicWitness.nativeScalar S = 1 := by
      rw [←hfx,he]
      exact f.map_one
    have ho := CubicWitness.nativeScalar_order S
    rw [hh,orderOf_one] at ho
    omega
  let X : Sylow 3 (CubicLift.subgroup e) := Sylow.ofCard (zpowers x) (by
    rw [Nat.card_zpowers,hxo,CubicLift.subgroup_card e h]
    decide +kernel)
  have hX : cubicSylowImage e X = zpowers x.val := MonoidHom.map_zpowers _ x
  have hm := marked_cocode_cubic_commutator W f hf hk E hE z S hz n hn hfx
  let C := (fullCubicCentralizer e X).map (centralizer (z : G)).subtype
  have hC (y : G) (hyz : y ∈ centralizer (z : G))
      (hyx : y ∈ Subgroup.centralizer ({(n : G)} : Set G)) : y ∈ C := by
    refine ⟨⟨y,hyz⟩,?_,rfl⟩
    change ∀ a ∈ cubicSylowImage e X, a * ⟨y,hyz⟩ = ⟨y,hyz⟩ * a
    rw [hX]
    rintro a ⟨k,rfl⟩
    have hh : Commute (⟨y,hyz⟩ : centralizer (z : G)) x.val :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hyx)
    exact (hh.zpow_right k).eq.symm
  have hleft : W ⊓ Subgroup.centralizer ({(n : G)} : Set G) ≤ C := by
    intro y hy
    apply hC y _ hy.2
    exact mem_centralizer_singleton_iff.mpr
      (((Commute.all (⟨y,hy.1⟩ : W) z).map W.subtype).eq)
  have hright : normalizer (W : Set G) ⊓ Subgroup.centralizer ({(z : G)} : Set G) ⊓
      Subgroup.centralizer ({(n : G)} : Set G) ≤ C := by
    intro y hy
    exact hC y hy.1.2 hy.2
  have hzm : (z : G) ∈ ⁅C,C⁆ := commutator_mono hleft hright hm
  have hmarker : fullCubicMarker e X ∈ _root_.commutator (fullCubicCentralizer e X) := by
    dsimp only [C] at hzm
    rw [←map_commutator,←map_subtype_commutator,map_map] at hzm
    obtain ⟨c,hc,he⟩ := hzm
    have he' : c = fullCubicMarker e X := Subtype.ext (Subtype.ext he)
    exact he' ▸ hc
  have hl := (fullCubicCentralizer_layer_eq_top_iff h e X).mpr hmarker
  rw [fullCubicCentralizer_layer h e X] at hl
  exact ⟨X,⟨hl⟩⟩
end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition


namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup LocalGeometry Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped IsMulCommutative Pointwise
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- All original Sylow choices have isomorphic full cubic centralizers. -/
theorem fullCubicCentralizer_equiv {z : G}
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X Y : Sylow 3 (CubicLift.subgroup e)) :
    Nonempty (fullCubicCentralizer e X ≃* fullCubicCentralizer e Y) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (CubicLift.subgroup e) X Y
  have he := congrArg (fun P : Sylow 3 (CubicLift.subgroup e) =>
    (P : Subgroup (CubicLift.subgroup e))) hg
  rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at he
  have hh := congrArg (Subgroup.map (CubicLift.subgroup e).subtype) he
  have hX : (cubicSylowImage e X).map (MulAut.conj g.val).toMonoidHom = cubicSylowImage e Y := by
    rw [cubicSylowImage,map_map]
    change ((X : Subgroup (CubicLift.subgroup e)).map (MulAut.conj g).toMonoidHom).map
      (CubicLift.subgroup e).subtype = (Y : Subgroup (CubicLift.subgroup e)).map
        (CubicLift.subgroup e).subtype at hh
    rw [map_map] at hh
    exact hh
  have hC : (fullCubicCentralizer e X).map (MulAut.conj g.val).toMonoidHom =
      fullCubicCentralizer e Y := by
    change (Subgroup.centralizer _).map _ = _
    rw [Theory.GroupTheory.map_centralizer_equiv]
    change Subgroup.centralizer ((cubicSylowImage e X).map (MulAut.conj g.val).toMonoidHom :
      Set (centralizer z)) = _
    rw [hX]
    rfl
  exact ⟨((fullCubicCentralizer e X).equivMapOfInjective
    (MulAut.conj g.val).toMonoidHom (MulAut.conj g.val).injective).trans
      (MulEquiv.subgroupCongr hC)⟩

/-- The perfectness clause of AS91 (4.9) from a genuine marked cocode
normalizer. The original quotient marking and arbitrary original X are retained. -/
theorem marked_fullCubicCentralizer_perfect
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G)))
    (X : Sylow 3 (CubicLift.subgroup e)) : Group.IsPerfect (fullCubicCentralizer e X) := by
  obtain ⟨Y,hY⟩ := marked_cocode_exists_perfect_cubic W f hf hk E hE z S hz h e
  let := hY
  obtain ⟨r⟩ := fullCubicCentralizer_equiv e Y X
  exact Group.IsPerfect.ofSurjective (f := r.toMonoidHom) r.surjective

/-- In the same original centralizer, the layer is the whole group. -/
theorem marked_fullCubicCentralizer_layer
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
    componentLayer (fullCubicCentralizer e X) = ⊤ := by
  let := marked_fullCubicCentralizer_perfect W f hf hk E hE z S hz h e X
  rw [fullCubicCentralizer_layer h e X,Group.IsPerfect.commutator_eq_top]

/-- The full source cubic centralizer, with its center of order six, is quasisimple. -/
theorem marked_fullCubicCentralizer_quasisimple
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G)))
    (X : Sylow 3 (CubicLift.subgroup e)) : IsQuasisimple (fullCubicCentralizer e X) := by
  let := marked_fullCubicCentralizer_perfect W f hf hk E hE z S hz h e X
  have ht := fullCubicDerived_quasisimple h e X
  rw [Group.IsPerfect.commutator_eq_top] at ht
  let := ht
  exact IsQuasisimple.of_mulEquiv Subgroup.topEquiv
end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
