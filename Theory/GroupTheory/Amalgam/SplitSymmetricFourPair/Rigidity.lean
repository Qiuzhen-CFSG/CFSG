module
public import Theory.GroupTheory.Amalgam.SplitSymmetricFourPair
public import Theory.GroupTheory.Amalgam.ParabolicRecognition

/-!
# Faithful split symmetric-four amalgams

Faithfulness forbids preserving either the central C₂ or the whole normal
C₂×V₄ of an endpoint. The overlap calculation then corrects both embeddings
simultaneously. Thus every faithful C₂×S₄ -- C₂×D₈ -- C₂×S₄ pair has the same
marked amalgam, independently of its completion.

Source: Aschbacher–Smith F.1.12(I)(2), binary case, printed p.262.
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam.SplitSymmetricFourPair
open Subgroup

def base : RankTwoAmalgam L B L := ⟨MixedSixteen.left,MixedSixteen.left⟩
def amalgam : RankTwoAmalgam L B L := twistRight base delta

private theorem central_image_normal :
    (((MonoidHom.snd ℤˣ MixedEight.D8).ker).map MixedSixteen.left).Normal := by
  have he : ((MonoidHom.snd ℤˣ MixedEight.D8).ker).map MixedSixteen.left =
      (MonoidHom.snd ℤˣ MixedEight.S4).ker := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      change MixedEight.square b.2=1
      rw [show b.2=1 from hb,map_one]
    · intro hx
      refine ⟨(x.1,1),rfl,?_⟩
      exact Prod.ext rfl ((map_one MixedEight.square).trans (show x.2=1 from hx).symm)
  rw [he]
  infer_instance

private theorem elementary_image_normal : (chi.ker.map MixedSixteen.left).Normal := by
  have cert : ∀ (g : L) (b : B), chi b=1 →
      ∃ e : B, chi e=1 ∧ MixedSixteen.left e=g*MixedSixteen.left b*g⁻¹ := by
    decide +kernel
  constructor
  rintro x ⟨b,hb,rfl⟩ g
  obtain ⟨e,he,hge⟩ := cert g b hb
  exact ⟨e,he,hge⟩

/-- A faithful overlap gluing cannot preserve the central endpoint line. -/
theorem central_moved (d : MulAut B) (hf : Faithful (twistRight base d)) : d z≠z := by
  intro hz
  let N := (MonoidHom.snd ℤˣ MixedEight.D8).ker
  have hfix (x : B) (hx : x∈N) : d x=x := by
    rcases x with ⟨e,b⟩
    change b=1 at hx
    subst b
    rcases Int.units_eq_one_or e with he | he
    · subst e; exact d.map_one
    · subst e; exact hz
  have he : N.map d.toMonoidHom=N := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change d y∈N
      rwa [hfix y hy]
    · intro hx; exact ⟨x,hx,hfix x hx⟩
  have hn : (N.map (twistRight base d).right).Normal := by
    change (N.map (MixedSixteen.left.comp d.toMonoidHom)).Normal
    rw [←Subgroup.map_map,he]
    exact central_image_normal
  have hb := hf N central_image_normal hn
  have hzN : z∈N := rfl
  rw [hb] at hzN
  exact (by decide +kernel : z≠1) hzN

/-- Faithfulness also moves the whole elementary normal core of an endpoint. -/
theorem reflection_sign (d : MulAut B) (hf : Faithful (twistRight base d)) : chi (d s)=1 := by
  rcases Int.units_eq_one_or (chi (d s)) with hs | hs
  · exact hs
  · have hv := character_generator_values d
    have hc : chi.comp d.toMonoidHom=chi := hom_ext hv.2 hv.1 hs
    have he : chi.ker.map d.toMonoidHom=chi.ker := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        change chi (d y)=1
        exact (DFunLike.congr_fun hc y).trans hy
      · intro hx
        refine ⟨d.symm x,?_,d.apply_symm_apply x⟩
        change chi (d.symm x)=1
        rw [←DFunLike.congr_fun hc (d.symm x)]
        simpa using hx
    have hn : (chi.ker.map (twistRight base d).right).Normal := by
      change (chi.ker.map (MixedSixteen.left.comp d.toMonoidHom)).Normal
      rw [←Subgroup.map_map,he]
      exact elementary_image_normal
    have hb := hf chi.ker elementary_image_normal hn
    have hzN : z∈chi.ker := by decide +kernel
    rw [hb] at hzN
    exact ((by decide +kernel : z≠1) hzN).elim

/-- The three simultaneous corrections retain the original two overlap maps. -/
theorem twist_iso (d : MulAut B) (hf : Faithful (twistRight base d)) :
    Nonempty (Iso (twistRight base d) amalgam) := by
  obtain ⟨a,b,hd⟩ := automorphism_factors d (central_moved d hf) (reflection_sign d hf)
  refine ⟨{ left := extend a
            middle := restrict a
            right := (extend b).symm
            left_commutes := restrict_extends a
            right_commutes := ?_ }⟩
  intro x
  change (extend b).symm (MixedSixteen.left (d x)) =
    MixedSixteen.left (delta (restrict a x))
  apply (extend b).injective
  rw [(extend b).apply_symm_apply,restrict_extends,hd]
  rfl

theorem base_sylow : SylowEmbedded 2 base where
  left_injective := MixedSixteen.left_injective
  right_injective := MixedSixteen.left_injective
  left_sylow := ⟨MixedSixteen.leftSylow,rfl⟩
  right_sylow := ⟨MixedSixteen.leftSylow,rfl⟩

/-- Every faithful pair with these three groups is compatibly isomorphic to
the same explicit split symmetric-four pair. -/
theorem iso_of_parabolic_equiv {L' B' R' : Type*} [Group L'] [Group B'] [Group R']
    (α : RankTwoAmalgam L' B' R') (hi : Function.Injective α.left)
    (hj : Function.Injective α.right) (hf : Faithful α)
    (eL : L'≃*L) (eB : B'≃*B) (eR : R'≃*L) : Nonempty (Iso α amalgam) := by
  let e : ParabolicEquiv α base := ⟨eL,eB,eR⟩
  obtain ⟨d,⟨f⟩⟩ := exists_twist_iso (base_sylow.of_parabolicEquiv e hi hj) base_sylow e
  obtain ⟨g⟩ := twist_iso d (f.faithful hf)
  exact ⟨f.trans g⟩

end Theory.GroupTheory.RankTwoAmalgam.SplitSymmetricFourPair
