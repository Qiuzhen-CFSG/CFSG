module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.LocalRestrictions
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.Representation.NormalClosureDisplacement

/-!
# The literal line and displacement in the abelian-U case

The commutator bound [V,U]≤ZS places every V-star displacement in ZS/Z.
Faithfulness makes a nonidentity marked displacement equal to this line,
and the definition U=⟨ZS^H⟩ gives its conjugate generation. The ambient
normalizer restriction transports to the actual line stabilizer. When the
quotient has dimension two, the marked fixed space is this same line,
so the full preimage gives C_U(V)≤ZS.

Source: Aschbacher–Smith, Lemmas 15.3.51–52, printed p.1145.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
open Recognition Recognition.LocalRestrictions
variable {G : Type*} [Group G] [Finite G]
variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

 theorem line_finrank (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4) :
    Module.finrank (ZMod 2) (vectorSubspace Z ZS ZS) = 1 := by
  let e : vectorSubspace Z ZS ZS ≃ distinguishedLine Z ZS := {
    toFun w := ⟨w.val.toMul, w.property⟩
    invFun w := ⟨Additive.ofMul w.val, w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : Nat.card (vectorSubspace Z ZS ZS) = 2 :=
    (Nat.card_congr e).trans (card_distinguishedLine Z ZS hZZS hZ hZS)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := vectorSubspace Z ZS ZS)
  rw [hc, Nat.card_zmod] at hh
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hh.symm)

omit [Finite G] in
 theorem displacement_le_line
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V : Subgroup G) (hcomm : ⁅V, closureU Z ZS⁆ ≤ ZS)
    (t : ActorQuotient Z) (ht : t ∈ Recognition.actorImage Z V) :
    LinearMap.range (actorRepresentation Z ZS hkernel t - LinearMap.id) ≤
      vectorSubspace Z ZS ZS := by
  obtain ⟨v, hv, rfl⟩ := ht
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w.toMul
  have hw : w = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
  rw [hw]
  change Additive.ofMul (quotientAction Z ZS v (QuotientGroup.mk' _ u)) -
    Additive.ofMul (QuotientGroup.mk' _ u) ∈ vectorSubspace Z ZS ZS
  have hc : ⁅(v : G), (u : G)⁆ ∈ ZS :=
    hcomm (commutator_mem_commutator hv u.property)
  let c : closureU Z ZS := ⟨⁅(v : G), (u : G)⁆, ZS_le_closureU Z ZS hc⟩
  have he : quotientAction Z ZS v (QuotientGroup.mk' _ u) *
      (QuotientGroup.mk' _ u)⁻¹ = QuotientGroup.mk' _ c := by
    rw [quotientAction_mk, ← map_inv, ← map_mul]
    congr 1
  change quotientAction Z ZS v (QuotientGroup.mk' _ u) /
    (QuotientGroup.mk' _ u) ∈ vectorImage Z ZS ZS
  rw [div_eq_mul_inv, he]
  exact mem_map_of_mem _ hc

 theorem displacement_eq_line
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V : Subgroup G) (hcomm : ⁅V, closureU Z ZS⁆ ≤ ZS)
    (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4)
    (t : ActorQuotient Z) (ht : t ∈ Recognition.actorImage Z V) (hne : t ≠ 1) :
    LinearMap.range (actorRepresentation Z ZS hkernel t - LinearMap.id) =
      vectorSubspace Z ZS ZS := by
  have hl := displacement_le_line Z ZS hkernel V hcomm t ht
  have hd := line_finrank Z ZS hZZS hZ hZS
  apply Submodule.eq_of_le_of_finrank_eq hl
  have hm := Submodule.finrank_mono hl
  have hn : LinearMap.range (actorRepresentation Z ZS hkernel t - LinearMap.id) ≠ ⊥ := by
    intro hh
    have he : actorRepresentation Z ZS hkernel t = 1 := by
      have hz := LinearMap.range_eq_bot.mp hh
      exact sub_eq_zero.mp hz
    exact hne (actorRepresentation_injective Z ZS hkernel (he.trans (map_one _).symm))
  have hp : Module.finrank (ZMod 2) (LinearMap.range
      (actorRepresentation Z ZS hkernel t - LinearMap.id)) ≠ 0 :=
    fun hz => hn (Submodule.finrank_eq_zero.mp hz)
  omega

omit [Finite G] in
 theorem displacement_generates
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (t : ActorQuotient Z)
    (he : LinearMap.range (actorRepresentation Z ZS hkernel t - LinearMap.id) =
      vectorSubspace Z ZS ZS) :
    conjugateDisplacementSpan (actorRepresentation Z ZS hkernel) t ⊤ = ⊤ := by
  let ρ := actorRepresentation Z ZS hkernel
  let W := conjugateDisplacementSpan ρ t ⊤
  let D : Subgroup (VectorQuotient Z ZS) := W.toAddSubgroup.toSubgroup'
  let := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
  have hg : closure {w : VectorQuotient Z ZS |
      ∃ h : centralizerH Z, ∃ z ∈ distinguishedLine Z ZS, h • z = w} ≤ D := by
    apply (closure_le _).mpr
    rintro _ ⟨h, z, hz, rfl⟩
    have hz' : Additive.ofMul z ∈ LinearMap.range (ρ t - LinearMap.id) := by
      rw [he]
      exact hz
    obtain ⟨w, hw⟩ := hz'
    change Additive.ofMul (quotientAction Z ZS h z) ∈ W
    change ρ (QuotientGroup.mk' _ h) (Additive.ofMul z) ∈ W
    rw [← hw]
    exact Submodule.subset_span ⟨QuotientGroup.mk' _ h, mem_top _, w, rfl⟩
  rw [distinguishedLine_generates Z ZS] at hg
  apply top_unique
  intro w _
  exact hg (mem_top w.toMul)

omit [Finite G] in
 theorem line_stabilizer_three_prime
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZZS : Z ≤ ZS) (hthree : Nat.Coprime 3 (Nat.card (normalizer (ZS : Set G)))) :
    Nat.Coprime 3 (Nat.card (subspaceStabilizer (actorRepresentation Z ZS hkernel)
      (vectorSubspace Z ZS ZS))) := by
  rw [stabilizer_eq_actorImage_normalizer Z ZS hkernel ZS hZZS (ZS_le_closureU Z ZS)]
  exact hthree.of_dvd_right ((card_actorImage_dvd Z _).trans (card_dvd_of_le inf_le_left))

 theorem small_fixed_of_dimension_two
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V : Subgroup G) (hZZS : Z ≤ ZS) (hZSV : ZS ≤ V)
    (hV : IsMulCommutative V)
    (t : ActorQuotient Z) (ht : t ∈ Recognition.actorImage Z V)
    (hr : Module.finrank (ZMod 2) (LinearMap.range
      (actorRepresentation Z ZS hkernel t - LinearMap.id)) = 1)
    (hline : Module.finrank (ZMod 2) (vectorSubspace Z ZS ZS) = 1)
    (hd : Module.finrank (ZMod 2) (Space Z ZS) = 2) :
    closureU Z ZS ⊓ centralizer (V : Set G) ≤ ZS := by
  let ρ := actorRepresentation Z ZS hkernel
  have hfix (u : closureU Z ZS) (hu : (u : G) ∈ centralizer (V : Set G)) :
      ρ t (Additive.ofMul (QuotientGroup.mk' _ u)) = Additive.ofMul (QuotientGroup.mk' _ u) := by
    obtain ⟨v, hv, rfl⟩ := ht
    change Additive.ofMul (quotientAction Z ZS v (QuotientGroup.mk' _ u)) = _
    rw [quotientAction_mk]
    congr 2
    apply Subtype.ext
    have hc := mem_centralizer_iff.mp hu v hv
    simp only [hc, mul_inv_cancel_right]
  have hl : vectorSubspace Z ZS ZS ≤ LinearMap.ker (ρ t - LinearMap.id) := by
    intro w hw
    obtain ⟨u, hu, he⟩ := hw
    have huC : (u : G) ∈ centralizer (V : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr hV (hZSV hu)
    have hf := hfix u huC
    change ρ t w - w = 0
    have hw : w = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul he.symm
    rw [hw]
    exact sub_eq_zero.mpr hf
  have hke : LinearMap.ker (ρ t - LinearMap.id) = vectorSubspace Z ZS ZS := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hl
    have hh := (ρ t - LinearMap.id).finrank_range_add_finrank_ker
    rw [hr, hd] at hh
    rw [hline]
    omega
  intro u hu
  let uU : closureU Z ZS := ⟨u, hu.1⟩
  have hm : Additive.ofMul (QuotientGroup.mk' _ uU) ∈ LinearMap.ker (ρ t - LinearMap.id) := by
    exact sub_eq_zero.mpr (hfix uU hu.2)
  rw [hke] at hm
  have hp : uU ∈ (vectorImage Z ZS ZS).comap (QuotientGroup.mk' _) := hm
  rw [vectorImage_preimage Z ZS ZS hZZS] at hp
  exact hp

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
