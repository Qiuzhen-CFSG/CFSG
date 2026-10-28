module
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Ambient

/-!
# Extending a natural alternating-five cover

The actual normal subgroup may have a nontrivial action kernel. Transport its
natural coordinates, identify the alternating image using surjectivity, and
apply the concrete five-point normalizer theorem. The resulting ambient
permutation action retains the original kernel and the same intertwiner.

Source application: Aschbacher–Smith C.1.23–28, pp.129–134.
-/
public section
open Subgroup BinaryPermutation
namespace Representation.OrthogonalFourMinus.FivePoint
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The ambient action extends a natural A5 cover without deleting its kernel. -/
theorem exists_ambient_permutation_of_cover
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (a : L →* alternatingGroup (Fin 5)) (ha : Function.Surjective a)
    (E : V ≃ₗ[ZMod 2] natural (Fin 5))
    (hE : ∀ (l : L) (v : V),
      E (ρ l.val v) = naturalRepresentation (Fin 5) (a l).val (E v)) :
    ∃ p : G →* Equiv.Perm (Fin 5),
      (∀ g v, E (ρ g v) = naturalRepresentation (Fin 5) (p g) (E v)) ∧
      (∀ l : L, p l.val = (a l).val) := by
  let b : G →* MulAut (Multiplicative (natural (Fin 5))) := {
    toFun g := (E.symm.trans ((LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)).trans
      E)).toAddEquiv.toMultiplicative
    map_one' := by
      apply MulEquiv.ext
      intro v
      change Multiplicative.ofAdd (E (ρ 1 (E.symm v.toAdd))) = v
      simp
    map_mul' := by
      intro g h
      apply MulEquiv.ext
      intro v
      change Multiplicative.ofAdd (E (ρ (g * h) (E.symm v.toAdd))) =
        Multiplicative.ofAdd (E (ρ g (E.symm (E (ρ h (E.symm v.toAdd))))))
      rw [E.symm_apply_apply,map_mul,Module.End.mul_apply] }
  let j := naturalMulAction (Fin 5)
  have hj : Function.Injective j := naturalMulAction_injective_of_odd (Fin 5) (by decide)
  have hbl (l : L) : b l.val = j (a l).val := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (E (ρ l.val (E.symm v.toAdd))) =
      Multiplicative.ofAdd (naturalRepresentation (Fin 5) (a l).val v.toAdd)
    rw [hE,E.apply_symm_apply]
  have him : L.map b = (alternatingGroup (Fin 5)).map j := by
    ext f
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨a ⟨l,hl⟩,(a ⟨l,hl⟩).property,(hbl ⟨l,hl⟩).symm⟩
    · rintro ⟨l,hl,rfl⟩
      obtain ⟨k,hk⟩ := ha ⟨l,hl⟩
      exact ⟨k,k.property,by rw [hbl,hk]⟩
  have hm (g : G) : b g ∈ j.range := by
    apply normalizer_alternatingFive_naturalMulAction_le_range
    rw [←him]
    exact le_normalizer_map b ⟨g,by rw [normalizer_eq_top]; exact mem_top _,rfl⟩
  let k : G →* j.range := b.codRestrict j.range hm
  let p := (MonoidHom.ofInjective hj).symm.toMonoidHom.comp k
  have hp (g : G) : j (p g) = b g := MonoidHom.apply_ofInjective_symm hj (k g)
  refine ⟨p,?_,?_⟩
  · intro g v
    have hh := congrArg Multiplicative.toAdd
      (DFunLike.congr_fun (hp g) (Multiplicative.ofAdd (E v)))
    change naturalRepresentation (Fin 5) (p g) (E v) = E (ρ g (E.symm (E v))) at hh
    simpa only [E.symm_apply_apply] using hh.symm
  · intro l
    exact hj ((hp l.val).trans (hbl l))
end Representation.OrthogonalFourMinus.FivePoint
