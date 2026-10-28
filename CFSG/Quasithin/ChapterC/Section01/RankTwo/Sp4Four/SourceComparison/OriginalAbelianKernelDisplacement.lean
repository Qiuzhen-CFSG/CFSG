module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalKernelDisplacement

/-!
# Abelian neighbors and the original critical hyperplane

The critical-root comparison needs commutativity only of the subgroup acting
on the endpoint natural module. If that subgroup contains the starting seed
and is normalized by the critical hyperplane, its quadratic action identifies
the hyperplane commutator with the full critical root. This formulation also
applies to the abelian join of two seeds on a common edge at distance four.

Source: MS93 (3.3)(ii), pp.866--867, and (5.7), p.919.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open RootHyperplaneComparison TwoLocalCover
variable {M F : Type*} [Group M] [Field F] [CharP F 2]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}

/-- The original hyperplane commutator is exactly the critical root, of field order. -/
theorem critical_root_abelian_kernel_commutator
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hZU : Z R z = U R z)
    (Y : Subgroup (FreeAmalgam R)) (hYQ : Y ≤ Q R a)
    (hZY : Z R a ≤ Y) (hYZ : Y ≤ stabilizer R z) (habel : IsMulCommutative Y)
    (f : Y →* Sp F) (hf : f.ker = (Q R z).subgroupOf Y)
    (hroot : ∀ u : Y, u.val ∈ Z R a → Module.finrank F (InvolutionTypes.movedSpace (f u)) ≤ 1)
    (π : U R z ≃* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector F))
    (hact : ∀ (y : Y) (u : U R z),
      π ⟨y.val*u.val*y.val⁻¹,
        (mem_normalizer_iff.mp (U_normalized z (hYZ y.property)) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (f y • (π u).toAdd))
    (hAn : Z R z ⊓ Q R a ≤ normalizer (Y : Set (FreeAmalgam R)))
    (hbad : ¬ Z R z ≤ normalizer (Y : Set (FreeAmalgam R))) :
    ⁅Y,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
      Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) = Nat.card F := by
  let j := (U R z).subtype.comp π.symm.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp π.symm.injective
  have hjr : j.range = Z R z := by
    rw [MonoidHom.range_comp,π.symm.toMonoidHom.range_eq_top_of_surjective π.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype,←hZU]
  have hconj (y : Y) v : j (Multiplicative.ofAdd (f y • v)) =
      y.val*j (Multiplicative.ofAdd v)*y.val⁻¹ := by
    have hh := hact y (π.symm (Multiplicative.ofAdd v))
    rw [π.apply_symm_apply,toAdd_ofAdd] at hh
    have hh' := congrArg π.symm hh
    rw [π.symm_apply_apply] at hh'
    exact congrArg Subtype.val hh'.symm
  let g : Z R a →* Sp F := f.comp (inclusion hZY)
  let := geometry.Z_elementary (by omega) a path.start_color
  let : IsElementaryAbelian 2 g.range := IsElementaryAbelian.of_surjective g.rangeRestrict
    g.rangeRestrict_surjective
  have hgne : g.range ≠ ⊥ := by
    intro h
    apply path.critical.2
    intro x hx
    have hg : g ⟨x,hx⟩ = 1 := mem_bot.mp (h ▸ (show g ⟨x,hx⟩ ∈ g.range from ⟨_,rfl⟩))
    have hk : inclusion hZY ⟨x,hx⟩ ∈ f.ker := hg
    rw [hf] at hk
    exact hk
  obtain ⟨_,_,_,hd⟩ := elementary_transvection_common_line g.range hgne
    (by rintro x ⟨x,rfl⟩; exact hroot (inclusion hZY x) x.property)
  let P := displacementSpace g.range
  have hline := displacement_lifts_to_commutator (Z R a) (Z R z) j hjr g
    (fun x v => hconj (inclusion hZY x) v)
  have hcommZ := ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path
  have hPfix : ∀ y : Y, ∀ v ∈ P, f y • v=v := by
    intro y v hv
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hconj]
    have hh := (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes a path.start_color)) (hcommZ (hline v hv)) y.val (hYQ y.property)
    rw [hh,mul_inv_cancel_right]
  have hza : Z R z ≤ stabilizer R a := path.endpoint_Z_le_start_stabilizer (by omega)
  have hA : ∀ v, j (Multiplicative.ofAdd v) ∈ Z R z ⊓ Q R a ↔
      v ∈ (form F).orthogonal P := by
    intro v
    rw [orthogonal_displacementSpace]
    constructor
    · intro hv x hx
      obtain ⟨x,rfl⟩ := hx
      apply Multiplicative.ofAdd.injective
      apply hj
      change j (Multiplicative.ofAdd (f (inclusion hZY x) • v)) = _
      rw [hconj]
      have hh := (show j (Multiplicative.ofAdd v) ∈ C R a from hCa.symm ▸ hv.2).2 x.val x.property
      change x.val * j (Multiplicative.ofAdd v) * x.val⁻¹ = _
      rw [hh,mul_inv_cancel_right]
    · intro hv
      have hz : j (Multiplicative.ofAdd v) ∈ Z R z := hjr ▸ (show j (Multiplicative.ofAdd v) ∈ j.range from ⟨_,rfl⟩)
      refine ⟨hz,?_⟩
      rw [←hCa]
      refine ⟨hza hz,?_⟩
      intro x hx
      have hh := hconj (inclusion hZY ⟨x,hx⟩) v
      change j (Multiplicative.ofAdd (g ⟨x,hx⟩ • v)) = _ at hh
      rw [hv (g ⟨x,hx⟩) ⟨⟨x,hx⟩,rfl⟩] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hquad : ∀ x y : Y, ∀ v ∈ (form F).orthogonal P,
      f x • (f y • v-v)=f y • v-v := by
    intro x y v hv
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hconj]
    have hdisp : j (Multiplicative.ofAdd (f y • v-v)) = ⁅y.val,j (Multiplicative.ofAdd v)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hconj,commutatorElement_def]
    have hcY : j (Multiplicative.ofAdd (f y • v-v)) ∈ Y := by
      rw [hdisp]
      exact le_normalizer_iff_commutator_le_left.mp hAn
        (commutator_mem_commutator y.property ((hA v).mpr hv))
    have hh := (le_centralizer_iff_isMulCommutative.mpr habel) x.property _ hcY
    rw [←hh,mul_inv_cancel_right]
  have hle := embedded_hyperplane_commutator_eq_root Y (Z R z ⊓ Q R a) j hj
    (inf_le_left.trans_eq hjr.symm) f hconj P hd hPfix hquad hA
    (fun v hv => hZY (hcommZ (hline v hv))) hAn (hjr.symm ▸ hbad)
  have heq := commutator_eq_displacement_image (Z R a) (Z R z) j hjr g
    (fun x v => hconj (inclusion hZY x) v)
  refine ⟨hle.trans heq.symm,?_⟩
  rw [heq,card_map_of_injective hj]
  change Nat.card P = Nat.card F
  rw [Module.natCard_eq_pow_finrank (K := F),hd,pow_one]
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
