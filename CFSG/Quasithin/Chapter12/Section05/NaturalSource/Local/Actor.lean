module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Subgroups
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer

/-!
# Extending the original exterior actor to LT

Conjugation on the unchanged V transports to its exterior coordinates.
The image of L is exactly SL₅(2)'s exterior image. Since T normalizes L,
the whole LT image normalizes it; the checked self-normalizer theorem
therefore gives an actor LT → SL₅(2). Faithfulness of the exterior action
forces this actor to extend the original quotient projection on L.

Source: Aschbacher--Smith, notation preceding 12.5.2, printed p.817.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)

/-- The linear coordinates underlying the original multiplicative marking. -/
def linearCoordinates : let := D.elementary
    Additive V ≃ₗ[ZMod 2] Representation.SL5ExteriorSquare.V := by
  let := D.elementary
  let c : Additive V ≃+ Representation.SL5ExteriorSquare.V := {
    toFun v := (a.coordinates v.toMul).toAdd
    invFun w := Additive.ofMul (a.coordinates.symm (Multiplicative.ofAdd w))
    left_inv v := congrArg Additive.ofMul (a.coordinates.symm_apply_apply v.toMul)
    right_inv w := congrArg Multiplicative.toAdd
      (a.coordinates.apply_symm_apply (Multiplicative.ofAdd w))
    map_add' v w := congrArg Multiplicative.toAdd (a.coordinates.map_mul v.toMul w.toMul) }
  exact c.toLinearEquiv (ZMod.map_smul c)

/-- Extend the literal quotient actor to LT, before choosing a Sylow flag. -/
theorem exists_join_actor (hn : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ∃ α : (L ⊔ (T : Subgroup G) : Subgroup G) →*
        Representation.SL5TenDimensional.Group,
      (∀ l : L, α ⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩ =
        a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∧
      ∀ (h : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
        a.coordinates ⟨(h : G) * v * (h : G)⁻¹,
          (mem_normalizer_iff.mp ((sup_le D.normalizes hn) h.property) v).mp v.property⟩ =
        Multiplicative.ofAdd (Representation.SL5TenDimensional.exteriorAction 2 (α h)
          (a.coordinates v).toAdd) := by
  let := D.elementary
  let H := L ⊔ (T : Subgroup G)
  let c := a.linearCoordinates
  let φ : H →* MulAut V := V.normalizerMonoidHom.comp
    (inclusion (sup_le D.normalizes hn))
  have hφ (h : H) (v : V) : φ h v =
      ⟨(h : G) * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp ((sup_le D.normalizes hn) h.property) v).mp v.property⟩ := by
    apply Subtype.ext
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  let ρ := Representation.elementaryRepresentation (p := 2) φ
  let τ : Representation (ZMod 2) H Representation.SL5ExteriorSquare.V :=
    c.conjRingEquiv.toMonoidHom.comp ρ
  let σ := Representation.SL5TenDimensional.exteriorAction 2
  have hres (l : L) : τ.asGroupHom ⟨l, (le_sup_left : L ≤ H) l.property⟩ =
      σ.asGroupHom (a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    change (a.coordinates (φ ⟨l, (le_sup_left : L ≤ H) l.property⟩
      (a.coordinates.symm (Multiplicative.ofAdd w)))).toAdd = _
    rw [hφ]
    have hh := congrArg Multiplicative.toAdd
      (a.equivariant l (a.coordinates.symm (Multiplicative.ofAdd w)))
    simpa only [MulEquiv.apply_symm_apply, Representation.asGroupHom_apply, toAdd_ofAdd] using hh
  have himg : (L.subgroupOf H).map τ.asGroupHom = σ.asGroupHom.range := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩),
        (hres ⟨l, hl⟩).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨q, rfl⟩ := a.quotientEquiv.surjective g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
      exact ⟨⟨l, (le_sup_left : L ≤ H) l.property⟩, l.property, hres l⟩
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hnorm := (L.subgroupOf H).le_normalizer_map τ.asGroupHom
  rw [normalizer_eq_top, himg, Representation.SL5TenDimensional.ExteriorNormalizer.normalizer_two]
    at hnorm
  have hmem (h : H) : τ.asGroupHom h ∈ σ.asGroupHom.range :=
    hnorm ⟨h, mem_top h, rfl⟩
  let β : H →* σ.asGroupHom.range := τ.asGroupHom.codRestrict _ hmem
  let e := MonoidHom.ofInjective
    (Representation.SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0)
  let α := e.symm.toMonoidHom.comp β
  have he (h : H) : σ.asGroupHom (α h) = τ.asGroupHom h :=
    congrArg Subtype.val (e.apply_symm_apply (β h))
  refine ⟨α, ?_, ?_⟩
  · intro l
    apply Representation.SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0
    exact (he _).trans (hres l)
  · intro h v
    have hh := LinearMap.congr_fun (congrArg Units.val (he h))
      (a.coordinates v).toAdd
    change σ (α h) (a.coordinates v).toAdd =
      (a.coordinates (φ h (a.coordinates.symm (a.coordinates v)))).toAdd at hh
    rw [MulEquiv.symm_apply_apply, hφ] at hh
    exact congrArg Multiplicative.ofAdd hh.symm

end ExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
