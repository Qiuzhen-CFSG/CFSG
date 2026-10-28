module

public import Theory.Representation.BinaryAlternatingFiveNormalizer

/-!
# Extending a marked five-point action to the ambient group

If a normal subgroup acts as the actual binary A₅ module, every ambient
operator belongs to the normalizer of that image. The five-point normalizer
theorem therefore constructs a permutation action of the whole group. It
extends the given marking of A₅ and uses the same linear coordinates.
Faithfulness of the original action gives faithfulness of this permutation
action. No ambient recognition or module comparison is assumed.

Source: Aschbacher–Smith, K.3.1.2, printed p.454.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.FivePoint
open BinaryPermutation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  (e : L ≃* alternatingGroup (Fin 5))
  (E : V ≃ₗ[ZMod 2] natural (Fin 5))
  (hE : ∀ (l : L) (v : V),
    E (ρ l.val v) = naturalRepresentation (Fin 5) (e l).val (E v))

private def transported : G →* MulAut (Multiplicative (natural (Fin 5))) where
  toFun g := (E.symm.trans ((LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)).trans
    E)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (E (ρ 1 (E.symm v.toAdd))) = v
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (E (ρ (g * h) (E.symm v.toAdd))) =
      Multiplicative.ofAdd (E (ρ g (E.symm (E (ρ h (E.symm v.toAdd))))))
    rw [E.symm_apply_apply, map_mul, Module.End.mul_apply]

include hE in
private theorem transported_layer (l : L) :
    transported ρ E l.val = naturalMulAction (Fin 5) (e l).val := by
  apply MulEquiv.ext
  intro v
  change Multiplicative.ofAdd (E (ρ l.val (E.symm v.toAdd))) =
    Multiplicative.ofAdd (naturalRepresentation (Fin 5) (e l).val v.toAdd)
  rw [hE, E.apply_symm_apply]

include hE in
private theorem transported_image : L.map (transported ρ E) =
    (alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) := by
  ext f
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨e ⟨l, hl⟩, (e ⟨l, hl⟩).property, (transported_layer ρ L e E hE ⟨l, hl⟩).symm⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨l, hl⟩
    exact ⟨k, k.property, by rw [transported_layer ρ L e E hE, hk]⟩

include hE in
/-- A faithful ambient representation extending this marked A₅ action has a
faithful five-point action with the very same intertwiner. -/
theorem exists_ambient_permutation [L.Normal] (hρ : Function.Injective ρ) :
    ∃ f : G →* Equiv.Perm (Fin 5), Function.Injective f ∧
      (∀ g v, E (ρ g v) = naturalRepresentation (Fin 5) (f g) (E v)) ∧
      (∀ l : L, f l.val = (e l).val) := by
  let j := naturalMulAction (Fin 5)
  have hj : Function.Injective j := naturalMulAction_injective_of_odd (Fin 5) (by decide)
  have hm (g : G) : transported ρ E g ∈ j.range := by
    apply normalizer_alternatingFive_naturalMulAction_le_range
    rw [← transported_image ρ L e E hE]
    apply Subgroup.le_normalizer_map (transported ρ E)
    exact ⟨g, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _, rfl⟩
  let k : G →* j.range := (transported ρ E).codRestrict j.range hm
  let f : G →* Equiv.Perm (Fin 5) := (MonoidHom.ofInjective hj).symm.toMonoidHom.comp k
  have hf (g : G) : j (f g) = transported ρ E g :=
    MonoidHom.apply_ofInjective_symm hj (k g)
  have hi (g : G) (v : V) :
      E (ρ g v) = naturalRepresentation (Fin 5) (f g) (E v) := by
    have ht := congrArg Multiplicative.toAdd
      (DFunLike.congr_fun (hf g) (Multiplicative.ofAdd (E v)))
    change naturalRepresentation (Fin 5) (f g) (E v) = E (ρ g (E.symm (E v))) at ht
    simpa only [E.symm_apply_apply] using ht.symm
  refine ⟨f, ?_, hi, ?_⟩
  · intro g h hgh
    apply hρ
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [hi, hi, hgh]
  · intro l
    apply hj
    exact (hf l.val).trans (transported_layer ρ L e E hE l)

/-- A faithful five-point action whose marked alternating subgroup is proper
is the full symmetric action. -/
theorem surjective_of_marked_alternating (f : G →* Equiv.Perm (Fin 5))
    (hf : Function.Injective f) (hL : L.map f = alternatingGroup (Fin 5))
    (hne : L ≠ ⊤) : Function.Surjective f := by
  have heven : alternatingGroup (Fin 5) ≤ f.range := by
    rw [← hL]
    exact Subgroup.map_le_range f L
  obtain ⟨g, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have hodd : Equiv.Perm.sign (f g) = -1 := by
    apply (Int.units_eq_one_or _).resolve_left
    intro h
    have hm : f g ∈ L.map f := by
      rw [hL]
      exact Equiv.Perm.mem_alternatingGroup.mpr h
    obtain ⟨l, hl, hlg⟩ := hm
    exact hg.2 (hf hlg ▸ hl)
  intro p
  by_cases hp : Equiv.Perm.sign p = 1
  · exact heven (Equiv.Perm.mem_alternatingGroup.mpr hp)
  · have hpn : Equiv.Perm.sign p = -1 := (Int.units_eq_one_or _).resolve_left hp
    have hm : p * (f g)⁻¹ ∈ f.range := by
      apply heven
      apply Equiv.Perm.mem_alternatingGroup.mpr
      simp [map_mul, map_inv, hpn, hodd]
    obtain ⟨k, hk⟩ := hm
    exact ⟨k * g, by rw [map_mul, hk, inv_mul_cancel_right]⟩

end Representation.OrthogonalFourMinus.FivePoint
