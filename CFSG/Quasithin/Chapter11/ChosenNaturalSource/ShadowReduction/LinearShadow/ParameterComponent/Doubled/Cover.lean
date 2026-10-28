module
public import Theory.Representation.SL2OrthogonalCover.Sylow

/-!
# A full Sylow commutator identifies the orthogonal cover

Every binary central natural SL₂ cover is a quotient of the universal
orthogonal cover. If its Sylow commutator has dimension twice the field degree,
that quotient is injective on the model's Sylow commutator. Its whole kernel
lies in that commutator, so the quotient is an isomorphism over the original
natural projection. This is the maximal-extension step needed after the
doubled SL₃ calculation gives commutator rank 4n at field degree 2n.

Source: Aschbacher--Smith, 11.3.6 and I.2.3(1), printed pp.773 and 413.
-/

@[expose] public noncomputable section
open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open Representation.SL2OrthogonalCover
variable {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The orthogonal cover's Sylow commutator has binary dimension twice the field degree. -/
theorem orthogonal_sylow_moved_dimension (n : ℕ) (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (P : Sylow 2 (SL F)) :
    Module.finrank (ZMod 2)
      (Coinvariants.ker ((binaryAction (F := F)).comp P.toSubgroup.subtype)) = 2 * n := by
  have hc : Coinvariants.ker ((binaryAction (F := F)).comp P.toSubgroup.subtype) =
      (fixed ((action (F := F)).comp P.toSubgroup.subtype)).restrictScalars (ZMod 2) := by
    rw [show (binaryAction (F := F)).comp P.toSubgroup.subtype =
      restrictScalars ((action (F := F)).comp P.toSubgroup.subtype) from rfl,
      coinvariants_restrictScalars,sylow_commutator (card_gt_two n hn hF) P]
  rw [hc]
  obtain ⟨U,hU,he,hd,_⟩ := sylow_fixed_geometry (F := F) P
  have hdim : Module.finrank F (fixed ((action (F := F)).comp P.toSubgroup.subtype)) = 2 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq U (form (F := F)).polarBilin.ker
    rw [hd.eq_bot,finrank_bot,add_zero,hU,radical_dimension] at hh
    rw [he]
    exact hh
  rw [((Submodule.restrictScalarsEquiv (ZMod 2) F (Space F)
    (fixed ((action (F := F)).comp P.toSubgroup.subtype))).restrictScalars (ZMod 2)).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F,
    Representation.SL2NaturalH1.field_finrank n hF,hdim]
  omega

/-- Attaining the full Sylow commutator dimension identifies the central cover
with the orthogonal cover over its actual natural projection. -/
theorem orthogonal_equiv_of_sylow_moved_dimension (n : ℕ) (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) (SL F) W)
    (p : ρ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p)
    (P : Sylow 2 (SL F))
    (hmove : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp P.toSubgroup.subtype)) = 2 * n) :
    ∃ e : Space F ≃ₗ[ZMod 2] W,
      (∀ g v, e (binaryAction g v) = ρ g (e v)) ∧
      ∀ v, p (e v) = binaryProjection v := by
  have hmodel := binaryProjection_isCover (F := F) (card_gt_two n hn hF)
  have hk : Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) := by
    rw [binary_kernel_finrank n hF,binary_dual_H1_finrank n hn hF]
  obtain ⟨f,hf,hover⟩ := exists_quotient_of_finrank_ker_eq
    (binaryProjection (F := F)) hmodel hk p hp
  let C := Coinvariants.ker ((binaryAction (F := F)).comp P.toSubgroup.subtype)
  let D := Coinvariants.ker (ρ.comp P.toSubgroup.subtype)
  let fP : Representation.IntertwiningMap
      ((binaryAction (F := F)).comp P.toSubgroup.subtype) (ρ.comp P.toSubgroup.subtype) :=
    f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun g v => LinearMap.congr_fun (f.isIntertwining' g.val) v)
  have hmap : C.map f.toLinearMap = D := map_coinvariants_of_surjective fP hf
  let fC : C →ₗ[ZMod 2] D :=
    (f.toLinearMap.comp C.subtype).codRestrict D
      (fun v => hmap ▸ Submodule.mem_map_of_mem v.property)
  have hsur : Function.Surjective fC := by
    intro v
    have hv : v.val ∈ C.map f.toLinearMap := by rw [hmap]; exact v.property
    obtain ⟨u,hu,he⟩ := hv
    exact ⟨⟨u,hu⟩,Subtype.ext he⟩
  have hinj : Function.Injective fC :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((orthogonal_sylow_moved_dimension n hn hF P).trans hmove.symm)).mpr hsur
  have hkerC : f.toLinearMap.ker ≤ C := by
    intro v hv
    have hpv : (binaryProjection (F := F)) v = 0 := by
      rw [← hover]
      change p (f v) = 0
      rw [show f v = 0 from hv,map_zero]
    have hgeom := cover_sylow_geometry n hn hF
      (binaryProjection (F := F)) hmodel P
    change v ∈ Coinvariants.ker ((binaryAction (F := F)).comp P.toSubgroup.subtype)
    rw [← hgeom.2.1]
    exact hgeom.1 (hmodel.2.1 hpv)
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have he : fC ⟨v,hkerC hv⟩ = fC 0 := by
      apply Subtype.ext
      change f v = f 0
      rw [map_zero]
      exact hv
    exact congrArg Subtype.val (hinj he)
  let e := LinearEquiv.ofBijective f.toLinearMap ⟨hfi,hf⟩
  exact ⟨e,fun g v => LinearMap.congr_fun (f.isIntertwining' g) v,hover⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
