module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanReflection

/-!
# Natural-module reflection choice and fusion

The natural kernel in characteristic two has exponent two. A nonidentity
diagonal actor has no fixed vector, which makes its Cartan centralizer
trivial. Every fixed vector of an anti-diagonal reflection is a difference
for that same reflection. Consequently two involutions above that reflection
are conjugate by the original kernel.

An actual upper root involution is first conjugated to an anti-diagonal
reflection. Hall correction then gives a Cartan normalizer; the natural
calculation makes it an involution and preserves its original root conjugacy
class. A trivial Cartan is handled directly, including the binary field.
No splitting of the extension is assumed.

Finally, a normal subgroup of binary SL₂ contained in the upper triangular
subgroup is trivial. This allows the source application to treat the full
local permutation kernel distinctly from O₂.

Source: DGS, *Groups and Graphs* (1985), (14.2), pp.210--211, and the
natural local profile in (10.5), pp.155--156. These are local calculations;
the other profiles and Chapter 14 exchange alternatives remain separate.
-/

@[expose] public noncomputable section
open Matrix Matrix.SpecialLinearGroup Subgroup
open scoped MatrixGroups
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F X : Type*} [Field F] [CharP F 2] [Group X]
variable {π : X →* SL(2,F)} (d : NaturalKernel π)

include d in
/-- The natural kernel has exponent two. -/
theorem NaturalKernel.square (z : π.ker) : z*z=1 := by
  apply d.coords.injective
  rw [map_mul,map_one]
  apply Multiplicative.toAdd.injective
  ext i
  exact CharTwo.add_self_eq_zero _

include d in
/-- The kernel coordinates certify that it is a two-group. -/
theorem NaturalKernel.isTwo : IsPGroup 2 π.ker := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro z
  exact ⟨1,by simpa only [pow_one,pow_two] using d.square z⟩

omit [CharP F 2] in
/-- A nonidentity diagonal matrix fixes no nonzero natural vector. -/
theorem diagonal_fixed (a : F) (ha : a≠0) (hne : a≠1) (v : Fin 2 → F)
    (hv : (diag2 a ha).val *ᵥ v=v) : v=0 := by
  have h0 : a*v 0=v 0 := by
    simpa [diag2_coe',Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun hv 0
  have h1 : a⁻¹*v 1=v 1 := by
    simpa [diag2_coe',Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun hv 1
  have hz0 : v 0=0 := by
    by_contra hz
    exact hne (mul_right_cancel₀ hz (h0.trans (one_mul _).symm))
  have hz1 : v 1=0 := by
    by_contra hz
    exact (inv_ne_one.mpr hne) (mul_right_cancel₀ hz (h1.trans (one_mul _).symm))
  ext i
  fin_cases i <;> assumption

include d in
omit [CharP F 2] in
/-- One nonidentity diagonal actor kills the entire kernel centralizer. -/
theorem NaturalKernel.diagonal_centralizer (K : Subgroup X) (k : X) (hk : k∈K)
    (a : F) (ha : a≠0) (hne : a≠1) (hπk : π k=diag2 a ha) :
    π.ker ⊓ centralizer (K : Set X)=⊥ := by
  apply le_bot_iff.mp
  intro z hz
  let zQ : π.ker := ⟨z,hz.1⟩
  have hc : (⟨k*zQ*k⁻¹, (inferInstance : π.ker.Normal).conj_mem zQ zQ.property k⟩ : π.ker)=zQ := by
    apply Subtype.ext
    change k*z*k⁻¹=z
    rw [(mem_centralizer_iff.mp hz.2 k hk),mul_inv_cancel_right]
  have he := d.equivariant k zQ
  rw [hc,hπk] at he
  have hzero : (d.coords zQ).toAdd=0 :=
    diagonal_fixed a ha hne _ (congrArg Multiplicative.toAdd he).symm
  have hzQ : zQ=1 := d.coords.injective (by
    rw [map_one]
    exact Multiplicative.toAdd.injective hzero)
  exact congrArg Subtype.val hzQ

/-- Every vector fixed by a braid reflection is a difference for that same
reflection. This retains the actual anti-diagonal parameter. -/
theorem braid_fixed_difference (a : F) (ha : a≠0) (v : Fin 2 → F)
    (hv : (upper a*lower a⁻¹*upper a).val *ᵥ v=v) :
    ∃ b : Fin 2 → F, b-(upper a*lower a⁻¹*upper a).val *ᵥ b=v := by
  have h1 : a⁻¹*v 0=v 1 := by
    simpa [braid_matrix a ha,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun hv 1
  refine ⟨![v 0,0],?_⟩
  ext i
  fin_cases i
  · simp [braid_matrix a ha]
  · simpa [braid_matrix a ha,CharTwo.neg_eq] using (mul_comm (v 0) a⁻¹).trans h1

include d in
/-- Two actual involutions with the same braid image are conjugate by an
element of the original natural kernel. No splitting is assumed. -/
theorem NaturalKernel.reflection_fiber_conjugate (t x : X)
    (ht : t*t=1) (hx : x*x=1) (himage : π x=π t)
    (a : F) (ha : a≠0) (hπt : π t=upper a*lower a⁻¹*upper a) :
    ∃ b : π.ker, (b:X)*t*(b:X)⁻¹=x := by
  let c : π.ker := ⟨x*t⁻¹,by simp [MonoidHom.mem_ker,himage]⟩
  have hci : (c:X)⁻¹=(c:X) := congrArg Subtype.val
    (inv_eq_of_mul_eq_one_right (d.square c))
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right ht
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  have hcomm : (c:X)*t=t*(c:X) := by
    calc
      _ = x := by simp [c]
      _ = x⁻¹ := hxi.symm
      _ = t*(c:X) := by
        rw [show x=(c:X)*t by simp [c],_root_.mul_inv_rev,hci,hti]
  have hc : (⟨t*c*t⁻¹,(inferInstance : π.ker.Normal).conj_mem c c.property t⟩ : π.ker)=c := by
    apply Subtype.ext
    change t*(c:X)*t⁻¹=(c:X)
    rw [←hcomm,mul_inv_cancel_right]
  have he := d.equivariant t c
  rw [hc,hπt] at he
  obtain ⟨v,hv⟩ := braid_fixed_difference a ha (d.coords c).toAdd
    (congrArg Multiplicative.toAdd he).symm
  let b := d.coords.symm (Multiplicative.ofAdd v)
  have hb : b*(⟨t*b*t⁻¹,(inferInstance : π.ker.Normal).conj_mem b b.property t⟩ : π.ker)⁻¹=c := by
    apply d.coords.injective
    rw [map_mul,map_inv,d.equivariant,hπt]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul,toAdd_inv,
      Matrix.SL2.naturalAction_apply,←sub_eq_add_neg]
    simpa only [b,MulEquiv.apply_symm_apply,toAdd_ofAdd] using hv
  refine ⟨b,?_⟩
  have hh := congrArg (fun z : π.ker => (z:X)*t) hb
  change ((b:X)*(t*(b:X)*t⁻¹)⁻¹)*t=(x*t⁻¹)*t at hh
  convert hh using 1 <;> group

/-- The same braid reflection inverts every diagonal Cartan element. -/
theorem braid_inverts_diagonal (a b : F) (ha : a≠0) (hb : b≠0) :
    (upper a*lower a⁻¹*upper a)*diag2 b hb*(upper a*lower a⁻¹*upper a)⁻¹ =
      (diag2 b hb)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right (braid_square a ha),diag2_inv]
  apply Subtype.ext
  change ((upper a*lower a⁻¹*upper a).val * (diag2 b hb).val) *
    (upper a*lower a⁻¹*upper a).val = (diag2 b⁻¹ (inv_ne_zero hb)).val
  rw [braid_matrix a ha,diag2_coe',diag2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,ha,mul_comm]

/-- Conjugating an upper root involution by the opposite root gives the
reflection with its same nonzero root parameter. -/
theorem lower_conjugates_upper (a : F) (ha : a≠0) :
    lower a⁻¹*upper a*(lower a⁻¹)⁻¹=upper a*lower a⁻¹*upper a := by
  rw [inv_eq_of_mul_eq_one_right (lower_square a⁻¹)]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul,braid_matrix a ha,upper,lower,transvection_coe,Matrix.mul_apply,
      Fin.sum_univ_two,mul_inv_cancel₀ ha,inv_mul_cancel₀ ha,CharTwo.add_self_eq_zero]

include d in
/-- In a natural extension, an actual root involution gives a Cartan
normalizing reflection conjugate to that same involution. The Cartan may
be trivial, so the binary field is retained. -/
theorem NaturalKernel.exists_diagonal_cartan_reflection [Finite X]
    (honto : Function.Surjective π) (K : Subgroup X)
    [Group.IsSolvable K] (hodd : Nat.Coprime 2 (Nat.card K))
    (hdiag : ∀ k∈K, ∃ b : F, ∃ hb : b≠0, π k=diag2 b hb)
    (x : X) (hx : x*x=1) (a : F) (ha : a≠0) (hπx : π x=upper a) :
    ∃ t : X, t∈normalizer (K : Set X) ∧ t*t=1 ∧ orderOf t=2 ∧
      π t=upper a*lower a⁻¹*upper a ∧ ∃ g : X, g*x*g⁻¹=t := by
  obtain ⟨g,hg⟩ := honto (lower a⁻¹)
  let v := g*x*g⁻¹
  have hv : v*v=1 := by
    calc
      _ = g*(x*x)*g⁻¹ := by dsimp [v]; group
      _ = 1 := by rw [hx,mul_one,mul_inv_cancel]
  have hπv : π v=upper a*lower a⁻¹*upper a := by
    change π (g*x*g⁻¹)=_
    rw [map_mul,map_mul,map_inv,hg,hπx,lower_conjugates_upper a ha]
  have hne : π v≠1 := by
    intro he
    have hh := congrArg (fun z : SL(2,F) => z.val 0 1) he
    rw [hπv,braid_matrix a ha] at hh
    exact ha hh
  have hnorm : π v∈normalizer (K.map π : Set SL(2,F)) := by
    apply mem_normalizer_iff.mpr
    intro y
    constructor
    · rintro ⟨k,hk,rfl⟩
      obtain ⟨b,hb,hbπ⟩ := hdiag k hk
      have he : π v*π k*(π v)⁻¹=π (k⁻¹) := by
        rw [hπv,hbπ,braid_inverts_diagonal a b ha hb,map_inv,hbπ]
      rw [he]
      exact mem_map_of_mem π (K.inv_mem hk)
    · intro hy
      have hnormInv : π v*π v=1 := by rw [←map_mul,hv,map_one]
      have hvInv : (π v)⁻¹=π v := inv_eq_of_mul_eq_one_right hnormInv
      obtain ⟨k,hk,hke⟩ := hy
      obtain ⟨b,hb,hbπ⟩ := hdiag k hk
      have he : π v*π k*(π v)⁻¹=π (k⁻¹) := by
        rw [hπv,hbπ,braid_inverts_diagonal a b ha hb,map_inv,hbπ]
      rw [hke,hvInv] at he
      have hy' : y=π (k⁻¹) := by
        calc
          y = π v*(π v*y*π v)*π v := by
            symm
            calc
              _ = (π v*π v)*y*(π v*π v) := by group
              _ = y := by rw [hnormInv,one_mul,mul_one]
          _ = π (k⁻¹) := he
      rw [hy']
      exact mem_map_of_mem π (K.inv_mem hk)
  by_cases hbot : K=⊥
  · refine ⟨v,?_,hv,?_,hπv,g,rfl⟩
    · rw [hbot,normalizer_eq_top]
      exact mem_top _
    · apply orderOf_eq_prime (show v^2=1 by simpa only [pow_two] using hv)
      intro he
      exact hne (he ▸ π.map_one)
  obtain ⟨k,hk,hk1⟩ := K.bot_or_exists_ne_one.resolve_left hbot
  have hdis : K ⊓ π.ker=⊥ := by
    obtain ⟨n,hn⟩ := d.isTwo.exists_card_eq
    exact (disjoint_of_coprime_natCard (by rw [hn]; exact hodd.symm.pow_right n)).eq_bot
  have hkπ : π k≠1 := by
    intro he
    have hm : k∈K ⊓ π.ker := ⟨hk,he⟩
    rw [hdis] at hm
    exact hk1 hm
  obtain ⟨b,hb,hbπ⟩ := hdiag k hk
  have hb1 : b≠1 := by
    intro he
    apply hkπ
    rw [hbπ]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe',he]
  have hcentral := d.diagonal_centralizer K k hk b hb hb1 hbπ
  obtain ⟨t,ht,htsq,ho,hπt,_⟩ := exists_cartan_reflection π K d.isTwo hodd hcentral v
    (by rw [←map_mul,hv,map_one]) hne hnorm
  obtain ⟨z,hz⟩ := d.reflection_fiber_conjugate v t hv htsq hπt a ha hπv
  refine ⟨t,ht,htsq,ho,hπt.trans hπv,(z:X)*g,?_⟩
  calc
    _ = (z:X)*v*(z:X)⁻¹ := by dsimp [v]; group
    _ = t := hz

/-- A normal subgroup of binary SL₂ contained in the upper triangular
subgroup is trivial. In particular an actual local permutation kernel
cannot survive inside that Borel after this marked quotient. -/
theorem normal_triangular_eq_bot (H : Subgroup SL(2,F)) [H.Normal]
    (htri : ∀ g∈H, g.val 1 0=0) : H=⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have h10 := htri g hg
  let w : SL(2,F) := ⟨!![0,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
  have h01 : g.val 0 1=0 := by
    have he := htri _ ((inferInstance : H.Normal).conj_mem g hg w)
    change ((w.val*g.val)*Matrix.adjugate w.val) 1 0=0 at he
    simpa [w,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,CharTwo.neg_eq] using he
  have heq : g.val 0 0=g.val 1 1 := by
    have he := htri _ ((inferInstance : H.Normal).conj_mem g hg (lower 1))
    have hsum : g.val 0 0+g.val 1 1=0 := by
      simpa [lower,SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_inv,transvection_coe,
        Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,h10,h01,CharTwo.neg_eq] using he
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hsum
  have hd : g.val 0 0 ^ 2=1 := by
    simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero,←heq,pow_two] using g.property
  have h00 : g.val 0 0=1 := by
    rcases sq_eq_one_iff.mp hd with he | he
    · exact he
    · simpa only [CharTwo.neg_eq] using he
  change g=1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10,h01,←heq,h00]

end Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
