module
public import Theory.GroupTheory.Amalgam.MixedSixteen.Models
public import Theory.GroupTheory.Amalgam.SymmetricFourPair

/-!
# Automorphisms of the split dihedral overlap

For C₂ × D₈ embedded in C₂ × S₄, the endpoint automorphisms restrict to
inner automorphisms and the sign shear. Once a twist moves both the central
line and the elementary core, these restrictions place it in one double
coset. The certificates enumerate only three generator images in the
sixteen-element overlap; all resulting maps are actual automorphisms.

Source: Aschbacher–Smith F.1.12(I)(2), binary case.
-/

@[expose] public section
open Subgroup
open Theory.GroupTheory RankTwoAmalgam
namespace Theory.GroupTheory.RankTwoAmalgam.SplitSymmetricFourPair
abbrev B := MixedSixteen.Middle
abbrev L := MixedSixteen.Left
def z : B := (-1,1)
def r : B := (1,DihedralGroup.r 1)
def s : B := (1,DihedralGroup.sr 0)
def chi : B →* ℤˣ := MixedEight.signCharacter.comp (MonoidHom.snd _ _)
def deltaWord (x : B) : B :=
  (x.1, (if x.1=1 then 1 else DihedralGroup.r 2) * SymmetricFourPair.shift x.2)
def deltaInvWord (x : B) : B :=
  (x.1, SymmetricFourPair.shift.symm ((if x.1=1 then 1 else DihedralGroup.r 2) * x.2))
def delta : MulAut B where
  toFun := deltaWord
  invFun := deltaInvWord
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
abbrev Param := ℤˣ × MixedEight.D8
def restrict (p : Param) : MulAut B :=
  (MulAut.conj (1,p.2)).trans
    (MixedSixteen.shear (if p.1=1 then 1 else MixedEight.signCharacter))
def extend (p : Param) : MulAut L :=
  (MulAut.conj (1,MixedEight.square p.2)).trans
    (MixedSixteen.shear (if p.1=1 then 1 else Equiv.Perm.sign))
theorem restrict_extends (p : Param) (x : B) :
    extend p (MixedSixteen.left x)=MixedSixteen.left (restrict p x) := by
  rcases p with ⟨e,d⟩
  simp only [extend,restrict,MulEquiv.trans_apply,MulAut.conj_apply]
  split <;> simp [MixedSixteen.left,MixedSixteen.shear,MixedEight.signCharacter]

set_option synthInstance.maxSize 512 in
set_option maxSynthPendingDepth 128 in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
theorem generator_certificate : ∀ x y w : B,
    x^2≠1 → y^2=1 → x*y≠y*x → w^2=1 → w*x=x*w → w*y=y*w →
    w≠1 → w≠x^2 → w≠z → chi y=1 →
    ∃ a b : Param,
      (restrict a).trans (delta.trans (restrict b)) r=x ∧
      (restrict a).trans (delta.trans (restrict b)) s=y ∧
      (restrict a).trans (delta.trans (restrict b)) z=w := by
  decide +kernel
end Theory.GroupTheory.RankTwoAmalgam.SplitSymmetricFourPair

public section
namespace Theory.GroupTheory.RankTwoAmalgam.SplitSymmetricFourPair

/-- Homomorphisms are determined by the central involution, rotation and reflection. -/
theorem hom_ext {H : Type*} [Group H] {f g : B →* H}
    (hz : f z=g z) (hr : f r=g r) (hs : f s=g s) : f=g := by
  apply MonoidHom.ext
  rintro ⟨e,d⟩
  have he : f (e,1)=g (e,1) := by
    rcases Int.units_eq_one_or e with h | h
    · subst e; exact (map_one f).trans (map_one g).symm
    · subst e; exact hz
  have hd : f (1,d)=g (1,d) := by
    rcases d with i | i
    · have hi : ((1,DihedralGroup.r i) : B)=r^i.val := by
        apply Prod.ext
        · simp [r]
        · simp [r]
      rw [hi,map_pow,map_pow,hr]
    · have hi : ((1,DihedralGroup.sr i) : B)=s*r^i.val := by
        apply Prod.ext
        · simp [r,s]
        · simp [r,s,DihedralGroup.sr_mul_r]
      rw [hi,map_mul,map_mul,map_pow,map_pow,hs,hr]
  have hh : ((e,d) : B)=(e,1)*(1,d) := by simp
  rw [hh,map_mul,map_mul,he,hd]

/-- The elementary invariants of the three actual automorphism images. -/
theorem generator_relations (d : MulAut B) :
    (d r)^2≠1 ∧ (d s)^2=1 ∧ d r*d s≠d s*d r ∧ (d z)^2=1 ∧
      d z*d r=d r*d z ∧ d z*d s=d s*d z ∧ d z≠1 ∧ d z≠(d r)^2 := by
  have hp (x : B) : (d x)^2=1 ↔ x^2=1 := by
    rw [←map_pow,d.map_eq_one_iff]
  have hc (x y : B) : d x*d y=d y*d x ↔ x*y=y*x := by
    rw [←map_mul,←map_mul,d.injective.eq_iff]
  have hn : d z=1 ↔ z=1 := d.map_eq_one_iff
  have hq : d z=(d r)^2 ↔ z=r^2 := by rw [←map_pow,d.injective.eq_iff]
  simp only [ne_eq,hp,hc,hn,hq]
  decide +kernel

private theorem character_certificate : ∀ x y w : B,
    x^2≠1 → x*y≠y*x → w*x=x*w → w*y=y*w → chi x = -1 ∧ chi w = 1 := by
  decide +kernel

/-- Every overlap automorphism preserves the sign values on the rotation
and the central generator. Only the reflection value can change. -/
theorem character_generator_values (d : MulAut B) : chi (d r) = -1 ∧ chi (d z)=1 := by
  obtain ⟨h1,_,h3,_,h5,h6,_,_⟩ := generator_relations d
  exact character_certificate _ _ _ h1 h3 h5 h6

/-- Moving the two normal source subgroups selects the unique compatible
amalgam double coset. -/
theorem automorphism_factors (d : MulAut B) (hz : d z≠z) (hs : chi (d s)=1) :
    ∃ a b : Param, d=(restrict a).trans (delta.trans (restrict b)) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := generator_relations d
  obtain ⟨a,b,hr,hs',hz'⟩ := generator_certificate _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hz hs
  exact ⟨a,b,MulEquiv.toMonoidHom_injective (hom_ext hz'.symm hr.symm hs'.symm)⟩

end Theory.GroupTheory.RankTwoAmalgam.SplitSymmetricFourPair
