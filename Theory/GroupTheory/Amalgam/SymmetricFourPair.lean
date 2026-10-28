module
public import Theory.GroupTheory.Amalgam.MixedDihedralEight.Models
public import Theory.GroupTheory.Amalgam.ParabolicRecognition

/-!
# The faithful symmetric-four amalgam

Two copies of S₄ meet in a dihedral Sylow subgroup of order eight. After
Sylow normalization the two embeddings differ by an automorphism of D₈.
Its eight automorphisms fall into two cosets of the inner automorphism group.
One coset preserves the same normal four-subgroup on both sides and violates
faithfulness. The other gives a unique compatible amalgam.

The small certificates check only the eight-element overlap and square action.
This is the binary linear case of Aschbacher–Smith F.1.12(I)(1) and F.6.5.
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam.SymmetricFourPair
open Subgroup MixedEight

def shiftWord : D8 → D8
  | .r i => .r i
  | .sr i => .sr (i+1)
def unshiftWord : D8 → D8
  | .r i => .r i
  | .sr i => .sr (i-1)
def shift : MulAut D8 where
  toFun := shiftWord
  invFun := unshiftWord
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def amalgam : RankTwoAmalgam S4 D8 S4 :=
  ⟨square, square.comp shift.toMonoidHom⟩

private theorem hom_ext {f g : D8 →* D8}
    (hr : f (.r 1)=g (.r 1)) (hs : f (.sr 0)=g (.sr 0)) : f=g := by
  ext x
  rcases x with i | i
  · have he : (DihedralGroup.r i : D8) = (.r 1)^i.val := by
      rw [DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
    rw [he,map_pow,map_pow,hr]
  · have he : (DihedralGroup.sr i : D8) = .sr 0*(.r 1)^i.val := by
      rw [DihedralGroup.r_one_pow,ZMod.natCast_zmod_val,DihedralGroup.sr_mul_r,zero_add]
    rw [he,map_mul,map_mul,map_pow,map_pow,hr,hs]

private theorem generator_certificate : ∀ x y : D8,
    x^2≠1 → y^2=1 → x*y≠y*x →
      (∃ a : D8, x=(MulAut.conj a) (.r 1) ∧ y=(MulAut.conj a) (.sr 0)) ∨
      (∃ a : D8, shift x=(MulAut.conj a) (.r 1) ∧ shift y=(MulAut.conj a) (.sr 0)) := by
  decide +kernel

theorem automorphism_cases (d : MulAut D8) :
    (∃ a : D8, d=MulAut.conj a) ∨
      (∃ a : D8, d.trans shift=MulAut.conj a) := by
  have hr : (d (.r 1))^2≠1 := by
    rw [←map_pow,←d.map_one,d.injective.ne_iff]
    decide +kernel
  have hs : (d (.sr 0))^2=1 := by rw [←map_pow]; exact d.map_one
  have hnc : d (.r 1)*d (.sr 0)≠d (.sr 0)*d (.r 1) := by
    rw [←map_mul,←map_mul,d.injective.ne_iff]
    decide +kernel
  rcases generator_certificate _ _ hr hs hnc with ⟨a,ha,hb⟩ | ⟨a,ha,hb⟩
  · exact Or.inl ⟨a, MulEquiv.toMonoidHom_injective (hom_ext ha hb)⟩
  · exact Or.inr ⟨a, MulEquiv.toMonoidHom_injective (hom_ext ha hb)⟩

private theorem normal_sign_image : (signCharacter.ker.map square).Normal := by
  have cert : ∀ (g : S4) (d : D8), signCharacter d=1 →
      ∃ e : D8, signCharacter e=1 ∧ square e=g*square d*g⁻¹ := by decide +kernel
  constructor
  rintro x ⟨d,hd,rfl⟩ g
  obtain ⟨e,he,hge⟩ := cert g d hd
  exact ⟨e,he,hge⟩

private theorem not_faithful_of_shift_inner (d : MulAut D8) (a : D8)
    (hd : d.trans shift=MulAut.conj a) : ¬ Faithful (twistRight amalgam d) := by
  intro hf
  have he : (twistRight amalgam d).right =
      (MulAut.conj (square a)).toMonoidHom.comp square := by
    apply MonoidHom.ext
    intro x
    have hh := DFunLike.congr_fun hd x
    change shift (d x)=a*x*a⁻¹ at hh
    change square (shift (d x))=square a*square x*(square a)⁻¹
    rw [hh,map_mul,map_mul,map_inv]
  have hn : (signCharacter.ker.map (twistRight amalgam d).right).Normal := by
    rw [he,←Subgroup.map_map]
    exact normal_sign_image.map _ (MulAut.conj (square a)).surjective
  have hh := hf signCharacter.ker normal_sign_image hn
  have hm : (DihedralGroup.r 2 : D8)∈signCharacter.ker := by decide +kernel
  rw [hh] at hm
  exact (by decide : (DihedralGroup.r 2 : D8)≠1) hm

/-- A faithful twist preserves the normal four-subgroup on the first side,
and is corrected by an inner automorphism of the whole first vertex. -/
theorem faithful_twist_factors (d : MulAut D8) (hf : Faithful (twistRight amalgam d)) :
    FactorsThrough amalgam d := by
  rcases automorphism_cases d with ⟨a,rfl⟩ | ⟨a,ha⟩
  · refine ⟨MulAut.conj a,MulEquiv.refl _,?_,?_,?_⟩
    · refine ⟨MulAut.conj (square a),?_⟩
      intro x
      change square a*square x*(square a)⁻¹=square (a*x*a⁻¹)
      simp only [map_mul,map_inv]
    · exact ⟨MulEquiv.refl _,fun _ => rfl⟩
    · rfl
  · exact (not_faithful_of_shift_inner d a ha hf).elim

theorem sylow : SylowEmbedded 2 amalgam where
  left_injective := square_injective
  right_injective := square_injective.comp shift.injective
  left_sylow := ⟨squareSylow,rfl⟩
  right_sylow := ⟨squareSylow,by
    change square.range=(square.comp shift.toMonoidHom).range
    rw [MonoidHom.range_comp,show shift.toMonoidHom.range=⊤ from MonoidHom.range_eq_top.mpr shift.surjective]
    exact square.range_eq_map⟩

/-- Compatible recognition of every faithful S₄--D₈--S₄ inclusion pair. -/
theorem iso_of_parabolic_equiv {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) (hi : Function.Injective α.left)
    (hj : Function.Injective α.right) (hf : Faithful α)
    (eL : L≃*S4) (eB : B≃*D8) (eR : R≃*S4) : Nonempty (Iso α amalgam) := by
  let e : ParabolicEquiv α amalgam := ⟨eL,eB,eR⟩
  exact iso_of_faithful_twist_factorization
    (sylow.of_parabolicEquiv e hi hj) sylow hf e faithful_twist_factors

end Theory.GroupTheory.RankTwoAmalgam.SymmetricFourPair
