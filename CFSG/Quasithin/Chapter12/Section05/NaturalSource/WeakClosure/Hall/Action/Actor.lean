module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Actor

/-!
# The exterior actor on the full module normalizer inside M

The image of L under literal conjugation on V is its marked exterior image.
Every element of M ∩ N_G(V) normalizes this image. Its self-normalizer in
GL(V) is itself, so the quotient actor extends to this whole intersection.

Source: Aschbacher--Smith, 12.2.10 and 12.2.11(a), printed pp.798--799.
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

/-- Extend the original quotient actor to M ∩ N_G(V), on the unchanged V. -/
theorem exists_normalizer_actor :
    ∃ α : (a.M ⊓ normalizer (V : Set G) : Subgroup G) →*
        Representation.SL5TenDimensional.Group,
      (∀ l : L, α ⟨l, (le_inf L.le_normalizer D.normalizes : L ≤ a.M ⊓ normalizer (V : Set G)) l.property⟩ =
        a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∧
      ∀ (h : (a.M ⊓ normalizer (V : Set G) : Subgroup G)) (v : V),
        a.coordinates ⟨(h : G) * v * (h : G)⁻¹,
          (mem_normalizer_iff.mp (h.property.2) v).mp v.property⟩ =
        Multiplicative.ofAdd (Representation.SL5TenDimensional.exteriorAction 2 (α h)
          (a.coordinates v).toAdd) := by
  let := D.elementary
  let H := a.M ⊓ normalizer (V : Set G)
  have hLH : L ≤ H := le_inf L.le_normalizer D.normalizes
  let c := a.linearCoordinates
  let φ : H →* MulAut V := V.normalizerMonoidHom.comp
    (inclusion inf_le_right)
  have hφ (h : H) (v : V) : φ h v =
      ⟨(h : G) * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp (h.property.2) v).mp v.property⟩ := by
    apply Subtype.ext
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  let ρ := Representation.elementaryRepresentation (p := 2) φ
  let τ : Representation (ZMod 2) H Representation.SL5ExteriorSquare.V :=
    c.conjRingEquiv.toMonoidHom.comp ρ
  let σ := Representation.SL5TenDimensional.exteriorAction 2
  have hres (l : L) : τ.asGroupHom ⟨l, hLH l.property⟩ =
      σ.asGroupHom (a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    change (a.coordinates (φ ⟨l, hLH l.property⟩
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
      exact ⟨⟨l, hLH l.property⟩, l.property, hres l⟩
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (inf_le_left : H ≤ normalizer (L : Set G))
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
