module
public import Theory.GroupTheory.QuaternionCentralProductOrderFourResidual
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Abelian conjugate spans in cyclic central products with SL₂(3)

An element of SL₂(3) commuting with all of its conjugates lies in its
central involution subgroup. Decomposing an element of a central product
then shows that a square-one element with the same property belongs to
the shared central involution of the cyclic factor. The finite check uses
the 24-element binary tetrahedral model, followed by structural transport.

The normal-subgroup extension shows that a normal two-subgroup missing
that involution is trivial. These are the residual-centralizer calculations
used in Aschbacher--Smith,
14.3.22, printed p.999, to exclude a central normal plane.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
private abbrev BT := QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action] Multiplicative (ZMod 3)
private instance : DecidableEq BT := SemidirectProduct.equivProd.injective.decidableEq
private instance : Fintype BT := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
private theorem bt_abelian_conjugates : ∀ x : BT,
    (∀ y : BT, x * (y*x*y⁻¹) = (y*x*y⁻¹)*x) → x^2=1 := by decide +kernel
private theorem bt_unique_involution : ∀ z x : BT,
    z ≠ 1 → z^2=1 → x^2=1 → x=1 ∨ x=z := by decide +kernel

variable {G : Type*} [Group G]
theorem sl23_abelian_conjugates (B : Subgroup G)
    (e : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (z : G) (hzB : z ∈ B) (hz1 : z≠1) (hz2 : z^2=1)
    (b : G) (hb : b∈B)
    (hcomm : ∀ c∈B, b*(c*b*c⁻¹)=(c*b*c⁻¹)*b) : b=1 ∨ b=z := by
  let f := e.trans GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
  let bb : B := ⟨b,hb⟩
  let zz : B := ⟨z,hzB⟩
  have hsq : (f bb)^2=1 := bt_abelian_conjugates (f bb) (by
    intro y
    obtain ⟨c,rfl⟩ := f.surjective y
    have hh : bb*(c*bb*c⁻¹)=(c*bb*c⁻¹)*bb := Subtype.ext (hcomm c c.property)
    simpa only [map_mul,map_inv] using congrArg f hh)
  have hz1' : f zz≠1 := by
    intro he
    exact hz1 (congrArg Subtype.val (f.injective (he.trans f.map_one.symm)))
  have hz2' : (f zz)^2=1 := by
    rw [←map_pow,show zz^2=1 from Subtype.ext hz2,map_one]
  rcases bt_unique_involution (f zz) (f bb) hz1' hz2' hsq with hh|hh
  · exact Or.inl (congrArg Subtype.val (f.injective (hh.trans f.map_one.symm)))
  · exact Or.inr (congrArg Subtype.val (f.injective hh))

/-- In a cyclic central product with SL₂(3), a square-one element commuting with all
its conjugates belongs to the shared central involution. -/
theorem cyclic_sl23_abelian_conjugates
    (E B : Subgroup G) [Finite E] [IsCyclic E]
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hEB : E ≤ centralizer (B : Set G))
    (z : G) (hzE : z∈E) (hzB : z∈B) (hz2 : orderOf z=2)
    (x : G) (hx : x∈E⊔B) (hx2 : x^2=1)
    (hcomm : ∀ c∈B, x*(c*x*c⁻¹)=(c*x*c⁻¹)*x) : x∈zpowers z := by
  have hx' : x∈(↑(E⊔B):Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left E B
    ((le_centralizer_iff.mp hEB).trans (Subgroup.centralizer_le_normalizer _))] at hx'
  obtain ⟨u,hu,b,hb,rfl⟩ := hx'
  have hbc : ∀ c∈B, b*(c*b*c⁻¹)=(c*b*c⁻¹)*b := by
    intro c hc
    let v := c*b*c⁻¹
    have hvB : v∈B := B.mul_mem (B.mul_mem hc hb) (B.inv_mem hc)
    have hub : b*u=u*b := hEB hu b hb
    have huc : c*u=u*c := hEB hu c hc
    have huv : v*u=u*v := hEB hu v hvB
    have he : c*(u*b)*c⁻¹=u*v := by
      dsimp only [v]
      rw [←mul_assoc c u b,huc]
      simp only [mul_assoc]
    have hh := hcomm c hc
    rw [he] at hh
    have hleft : (u*b)*(u*v)=(u*u)*(b*v) := by
      calc
        _ = u*(b*u)*v := by group
        _ = u*(u*b)*v := by rw [hub]
        _ = _ := by group
    have hright : (u*v)*(u*b)=(u*u)*(v*b) := by
      calc
        _ = u*(v*u)*b := by group
        _ = u*(u*v)*b := by rw [huv]
        _ = _ := by group
    rw [hleft,hright] at hh
    exact mul_left_cancel hh
  have hz1 : z≠1 := by intro hh; simp [hh] at hz2
  have hxE : u*b∈E := by
    rcases sl23_abelian_conjugates B eB z hzB hz1 (hz2 ▸ pow_orderOf_eq_one z) b hb hbc with hh|hh
    · simpa [hh] using hu
    · exact E.mul_mem hu (hh.symm ▸ hzE)
  change u*b∈zpowers z
  by_cases hx1 : u*b=1
  · simpa only [hx1] using (zpowers z).one_mem
  have he : (⟨u*b,hxE⟩:E)=⟨z,hzE⟩ := IsCyclic.eq_of_orderOf_eq_two
    (orderOf_eq_prime (Subtype.ext hx2) (fun hh => hx1 (congrArg Subtype.val hh)))
    ((orderOf_coe (⟨z,hzE⟩:E)).symm.trans hz2)
  have hh : u*b=z := congrArg Subtype.val he
  exact (congrArg (fun y : G => y∈zpowers z) hh).mpr (mem_zpowers z)

private theorem bt_normal_witness : ∀ z b : BT,
    z≠1 → z^2=1 → b=1 ∨ b=z ∨ b^2=z ∨
      ∃ c : BT, (b*c*b⁻¹*c⁻¹)^2=z := by decide +kernel

/-- Every nonidentity normal subgroup of SL₂(3) contains its central involution. -/
theorem sl23_normal_contains_involution (B N : Subgroup G)
    (e : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hBN : B≤normalizer (N:Set G))
    (z : G) (hzB : z∈B) (hz2 : orderOf z=2) (hzN : z∉N) : N⊓B=⊥ := by
  let f := e.trans GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
  let zz : B := ⟨z,hzB⟩
  have hz1 : z≠1 := by intro hh; simp [hh] at hz2
  have hz1' : f zz≠1 := by
    intro hh
    exact hz1 (congrArg Subtype.val (f.injective (hh.trans f.map_one.symm)))
  have hz2' : (f zz)^2=1 := by
    rw [←map_pow,show zz^2=1 from Subtype.ext (hz2 ▸ pow_orderOf_eq_one z),map_one]
  apply bot_unique
  intro b hb
  let bb : B := ⟨b,hb.2⟩
  rcases bt_normal_witness (f zz) (f bb) hz1' hz2' with hh|hh|hh|⟨c,hc⟩
  · exact mem_bot.mpr (congrArg Subtype.val (f.injective (hh.trans f.map_one.symm)))
  · have he : b=z := congrArg Subtype.val (f.injective hh)
    exact (hzN (he ▸ hb.1)).elim
  · have he : b^2=z := congrArg Subtype.val (f.injective (by simpa only [map_pow] using hh : f (bb^2)=f zz))
    exact (hzN (he ▸ N.pow_mem hb.1 2)).elim
  · obtain ⟨c,rfl⟩ := f.surjective c
    have he : (b*(c:G)*b⁻¹*(c:G)⁻¹)^2=z := congrArg Subtype.val
      (f.injective (by simpa only [map_pow,map_mul,map_inv] using hc : f ((bb*c*bb⁻¹*c⁻¹)^2)=f zz))
    have hm : b*(c:G)*b⁻¹*(c:G)⁻¹∈N := by
      have hcN := le_normalizer_iff.mp hBN c c.property b⁻¹ (N.inv_mem hb.1)
      simpa only [mul_assoc] using N.mul_mem hb.1 hcN
    exact (hzN (he ▸ N.pow_mem hm 2)).elim

variable [Finite G]
/-- A normal two-subgroup of a cyclic central product with SL₂(3) is
trivial if it misses the shared involution. -/
theorem cyclic_sl23_normal_twoSubgroup_eq_bot (E B N : Subgroup G) [IsCyclic E]
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hEB : E≤centralizer (B:Set G))
    (hNJ : N≤E⊔B) (hJN : E⊔B≤normalizer (N:Set G)) (hN : IsPGroup 2 N)
    (z : G) (hzE : z∈E) (hzB : z∈B) (hz2 : orderOf z=2) (hzN : z∉N) : N=⊥ := by
  have hBN : B≤normalizer (N:Set G) := le_sup_right.trans hJN
  have hi : N⊓B=⊥ := sl23_normal_contains_involution B N eB hBN z hzB hz2 hzN
  have hJB : E⊔B≤normalizer (B:Set G) :=
    sup_le (hEB.trans (Subgroup.centralizer_le_normalizer _)) B.le_normalizer
  have hNB : ⁅N,B⁆=⊥ := bot_unique (by
    rw [←hi]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hBN)
      (le_normalizer_iff_commutator_le_right.mp (hNJ.trans hJB)))
  have hNE : N≤E := by
    intro x hx
    have hh : x∈(↑(E⊔B):Set G) := hNJ hx
    rw [coe_mul_of_right_le_normalizer_left E B
      ((le_centralizer_iff.mp hEB).trans (Subgroup.centralizer_le_normalizer _))] at hh
    obtain ⟨u,hu,b,hb,he⟩ := hh
    have hbc : ∀ c∈B, b*(c*b*c⁻¹)=(c*b*c⁻¹)*b := by
      intro c hc
      have hbC : b∈centralizer (B:Set G) := by
        have hm := (centralizer (B:Set G)).mul_mem
          ((centralizer (B:Set G)).inv_mem (hEB hu))
          (commutator_eq_bot_iff_le_centralizer.mp hNB hx)
        have he' : u*b=x := he
        simpa only [←he',inv_mul_cancel_left] using hm
      exact (hbC _ (B.mul_mem (B.mul_mem hc hb) (B.inv_mem hc))).symm
    have hz1 : z≠1 := by intro hh; simp [hh] at hz2
    have hbE : b∈E := by
      rcases sl23_abelian_conjugates B eB z hzB hz1 (hz2 ▸ pow_orderOf_eq_one z) b hb hbc with hh|hh
      · exact hh ▸ E.one_mem
      · exact hh.symm ▸ hzE
    exact he ▸ E.mul_mem hu hbE
  rcases hN.card_eq_or_dvd with hh|hh
  · exact Subgroup.card_eq_one.mp hh
  · obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G:=N) 2 hh
    let vv : E := ⟨v,hNE v.property⟩
    have hv2 : orderOf vv=2 := (orderOf_coe vv).symm.trans ((orderOf_coe v).trans hv)
    have he : vv=⟨z,hzE⟩ := IsCyclic.eq_of_orderOf_eq_two hv2
      ((orderOf_coe (⟨z,hzE⟩:E)).symm.trans hz2)
    have hh : (v:G)=z := congrArg Subtype.val he
    exact (hzN (hh ▸ v.property)).elim

end Subgroup
