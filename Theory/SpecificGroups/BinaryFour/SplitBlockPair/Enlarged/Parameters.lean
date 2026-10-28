module
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Labels
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
/-! Binary labels, the two orientations of a rotating cubic, and its
basis-image parameterization. These calculations retain the trivial central
plane in the split-block argument of Aschbacher–Smith 14.4.4, p.1007. -/
@[expose] public section
namespace BinarySixSplitPair
open Subgroup
abbrev r : MulAut E := extend BinaryFourSplitPair.row
abbrev c : MulAut E := extend BinaryFourSplitPair.column
theorem overlap_closure : overlap = closure ({r,c} : Set (MulAut E)) := by
  rw [overlap,BinaryFourSplitPair.overlap,MonoidHom.map_closure]
  simp only [Set.image_insert_eq,Set.image_singleton]

theorem rotating_cubic_orientation (q : MulAut E) (hq : RotatingCubic q) :
    (q*r*q⁻¹=c ∧ q*c*q⁻¹=r*c) ∨ (q*r*q⁻¹=r*c ∧ q*c*q⁻¹=r) := by
  have hrs : r*r=1 := by rw [←map_mul,BinaryFourSplitPair.row_sq,map_one]
  have hcs : c*c=1 := by rw [←map_mul,BinaryFourSplitPair.column_sq,map_one]
  have hrc : Commute r c := by
    change r*c=c*r
    rw [←map_mul,←map_mul,BinaryFourSplitPair.row_column_commute]
  have hone : r ≠ 1 ∧ c ≠ 1 ∧ r ≠ c := by
    constructor
    · intro h
      have he := extend_injective (h.trans extend.map_one.symm)
      exact (by decide +kernel : BinaryFourSplitPair.row (Multiplicative.ofAdd ![0,0,1,0]) ≠ Multiplicative.ofAdd ![0,0,1,0]) (DFunLike.congr_fun he _)
    · constructor
      · intro h
        have he := extend_injective (h.trans extend.map_one.symm)
        exact (by decide +kernel : BinaryFourSplitPair.column (Multiplicative.ofAdd ![1,0,0,0]) ≠ Multiplicative.ofAdd ![1,0,0,0]) (DFunLike.congr_fun he _)
      · intro h
        have he := extend_injective h
        exact (by decide +kernel : BinaryFourSplitPair.row (Multiplicative.ofAdd ![0,0,1,0]) ≠ BinaryFourSplitPair.column (Multiplicative.ofAdd ![0,0,1,0])) (DFunLike.congr_fun he _)
  have hover : overlap = closure ({r,c} : Set (MulAut E)) := by
    rw [overlap,BinaryFourSplitPair.overlap,MonoidHom.map_closure]
    simp only [Set.image_insert_eq,Set.image_singleton]
  have hrm : r ∈ overlap := hover ▸ subset_closure (by simp)
  have hcm : c ∈ overlap := hover ▸ subset_closure (by simp)
  let f := MulAut.conj q
  have hcube (x : MulAut E) : f (f (f x))=x := by
    change q*(q*(q*x*q⁻¹)*q⁻¹)*q⁻¹=x
    calc
      _ = q^3*x*(q^3)⁻¹ := by simp only [pow_succ,pow_zero,one_mul]; group
      _ = x := by rw [hq.1]; simp
  have hrf := (mem_normalizer_iff.mp hq.2.2.1 r).mp hrm
  have hcf := (mem_normalizer_iff.mp hq.2.2.1 c).mp hcm
  rw [hover,mem_closure_pair_iff r c hrs hcs hrc] at hrf hcf
  change f r=1 ∨ f r=r ∨ f r=c ∨ f r=r*c at hrf
  change f c=1 ∨ f c=r ∨ f c=c ∨ f c=r*c at hcf
  rcases hrf with hr | hr | hr | hr
  · exact (hone.1 (f.injective (hr.trans f.map_one.symm))).elim
  · rcases hcf with hc | hc | hc | hc
    · exact (hone.2.1 (f.injective (hc.trans f.map_one.symm))).elim
    · exact (hone.2.2 (f.injective (hr.trans hc.symm))).elim
    · exfalso
      apply hq.2.2.2.1
      rw [hover]
      intro x hx
      rcases (mem_closure_pair_iff r c hrs hcs hrc x).mp hx with rfl | rfl | rfl | rfl
      · simp
      · exact (mul_inv_eq_iff_eq_mul.mp hr).symm
      · exact (mul_inv_eq_iff_eq_mul.mp hc).symm
      · exact (mul_inv_eq_iff_eq_mul.mp (show f (r*c)=r*c from by rw [map_mul,hr,hc])).symm
    · have hh := hcube c
      simp only [hc,map_mul,hr] at hh
      have hh' : r*c=c := by simpa only [←mul_assoc,hrs,one_mul] using hh
      exact (hone.1 (mul_right_cancel (hh'.trans (one_mul c).symm))).elim
  · rcases hcf with hc | hc | hc | hc
    · exact (hone.2.1 (f.injective (hc.trans f.map_one.symm))).elim
    · have hh := hcube r
      rw [hr,hc,hr] at hh
      exact (hone.2.2 hh.symm).elim
    · exact (hone.2.2 (f.injective (hr.trans hc.symm))).elim
    · exact Or.inl ⟨hr,hc⟩
  · rcases hcf with hc | hc | hc | hc
    · exact (hone.2.1 (f.injective (hc.trans f.map_one.symm))).elim
    · exact Or.inr ⟨hr,hc⟩
    · have hh := hcube r
      simp only [hr,map_mul,hc] at hh
      have hh' : r*c=r := by simpa only [mul_assoc,hcs,mul_one] using hh
      exact (hone.2.1 (mul_left_cancel (hh'.trans (mul_one r).symm))).elim
    · exact (hone.2.2 (f.injective (hr.trans hc.symm))).elim
end BinarySixSplitPair

namespace BinarySixSplitPair
def bx (a b : Fin 64) : Fin 64 := ⟨(a.val ^^^ b.val)%64,Nat.mod_lt _ (by decide)⟩
private def bit (n i : ℕ) : ZMod 2 := if n.testBit i then 1 else 0
private theorem bit_eq (n i : ℕ) : ((n/2^i%2:ℕ):ZMod 2) = bit n i := by
  rcases Nat.mod_two_eq_zero_or_one (n/2^i) with h | h
  · simp [bit,Nat.testBit_eq_decide_div_mod_eq,h]
  · simp [bit,Nat.testBit_eq_decide_div_mod_eq,h]
private theorem bit_bx (a b : Fin 64) (i : ℕ) (hi : i<6) :
    bit (bx a b).val i = bit a.val i + bit b.val i := by
  dsimp only [bit,bx]
  rw [Nat.testBit_mod_two_pow (a.val ^^^ b.val) 6 i,Nat.testBit_xor]
  simp only [show decide (i<6)=true from decide_eq_true hi,Bool.true_and]
  cases a.val.testBit i <;> cases b.val.testBit i <;> decide

theorem decode_bx (a b : Fin 64) : decode (bx a b) = decode a * decode b := by
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> dsimp [decode]
    all_goals first
      | simpa only [Nat.pow_zero,Nat.div_one] using (bit_eq (bx a b).val 0).trans ((bit_bx a b 0 (by decide)).trans
          (congrArg₂ (·+·) (bit_eq a.val 0).symm (bit_eq b.val 0).symm))
      | exact (bit_eq _ 1).trans ((bit_bx a b 1 (by decide)).trans
          (congrArg₂ (·+·) (bit_eq _ 1).symm (bit_eq _ 1).symm))
      | exact (bit_eq _ 2).trans ((bit_bx a b 2 (by decide)).trans
          (congrArg₂ (·+·) (bit_eq _ 2).symm (bit_eq _ 2).symm))
      | exact (bit_eq _ 3).trans ((bit_bx a b 3 (by decide)).trans
          (congrArg₂ (·+·) (bit_eq _ 3).symm (bit_eq _ 3).symm))
  · apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> dsimp [decode]
    all_goals first
      | exact (bit_eq _ 4).trans ((bit_bx a b 4 (by decide)).trans
          (congrArg₂ (·+·) (bit_eq _ 4).symm (bit_eq _ 4).symm))
      | exact (bit_eq _ 5).trans ((bit_bx a b 5 (by decide)).trans
          (congrArg₂ (·+·) (bit_eq _ 5).symm (bit_eq _ 5).symm))

theorem labels_mul (a b : E) : labels (a*b) = bx (labels a) (labels b) := by
  apply labels.symm.injective
  change decode (labels (a*b)) = decode (bx (labels a) (labels b))
  rw [decode_bx]
  exact (labels.symm_apply_apply (a*b)).trans
    (congrArg₂ (·*·) (labels.symm_apply_apply a).symm (labels.symm_apply_apply b).symm)
end BinarySixSplitPair

namespace BinarySixSplitPair
def basisSix (i : Fin 6) : E := decode (![1,2,4,8,16,32] i)
def binaryWord (a : Fin 6 → E) (x : Fin 64) : E :=
  a 0 ^ ((decode x).1.toAdd 0).val * a 1 ^ ((decode x).1.toAdd 1).val *
  a 2 ^ ((decode x).1.toAdd 2).val * a 3 ^ ((decode x).1.toAdd 3).val *
  a 4 ^ ((decode x).2.toAdd 0).val * a 5 ^ ((decode x).2.toAdd 1).val
private theorem basis_word : ∀ x, binaryWord basisSix x = decode x := by decide +kernel

theorem automorphism_expansion (f : MulAut E) (x : Fin 64) :
    f (decode x) = binaryWord (fun i => f (basisSix i)) x := by
  conv_lhs => rw [←basis_word x]
  simp only [binaryWord,map_mul,map_pow]

theorem oriented_basis_images (f : MulAut E)
    (hr : f*r*f⁻¹=c) (hc : f*c*f⁻¹=r*c) (hz : f point=point) :
    (fun i : Fin 6 => f (basisSix i)) =
      ![c (f (basisSix 2))*f (basisSix 2), point, f (basisSix 2),
        (r*c) (f (basisSix 2))*f (basisSix 2),f (basisSix 4),f (basisSix 5)] := by
  have hre (v : E) : f (r v)=c (f v) :=
    DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.mp hr) v
  have hce (v : E) : f (c v)=(r*c) (f v) :=
    DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.mp hc) v
  funext i
  fin_cases i
  · change f (basisSix 0) = c (f (basisSix 2))*f (basisSix 2)
    rw [show basisSix 0 = r (basisSix 2)*basisSix 2 from by decide +kernel,map_mul,hre]
  · change f (basisSix 1)=point
    rw [show basisSix 1=point from by decide +kernel]
    exact hz
  · rfl
  · change f (basisSix 3) = (r*c) (f (basisSix 2))*f (basisSix 2)
    rw [show basisSix 3 = c (basisSix 2)*basisSix 2 from by decide +kernel,map_mul,hce]
  · rfl
  · rfl
end BinarySixSplitPair
