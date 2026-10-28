module

public import Theory.Representation.HexacodeAction.PlaneStabilizer.Planes
public import Theory.Representation.HexacodeAction.Cover

/-!
# The alternating action on the six full-weight planes

Even hexacode automorphisms commute with the actual scalar and preserve
weight, so they permute the six full-weight scalar planes. The scalar kernel
acts trivially. Thus the action descends to the coordinate quotient `A₆`.
The explicit lift `hexX` moves the published full-weight plane; simplicity
makes the descended action injective. Perfectness makes every induced
permutation even, and the six-plane count then makes the alternating action
surjective.

This is the six-point action needed for the plane-stabilizer quotient on
printed p.1155 of Aschbacher–Smith, *The Classification of Quasithin Groups*
(combined manuscript, 1 March 2004). All concrete generators and coordinate
maps used here are from the existing licensed ATLAS ports.
-/

@[expose] public section

open Atlas.Codes
namespace Representation.Hexacode

private theorem even_action_scalar (g : HexEvenAutomorphisms) (w : hexacode) :
    action g.val (action hexZ w) = action hexZ (action g.val w) := by
  have hc : g.val * hexZ = hexZ * g.val :=
    (mul_inv_eq_iff_eq_mul).mp (hex_conjugation_even g.val g.property)
  simpa only [map_mul, Module.End.mul_apply] using congrArg (fun h => action h w) hc

private theorem image_full (g : HexEvenAutomorphisms) (P : FullWeightScalarPlane) :
    IsFullWeightScalarPlane (P.val.map (action g.val)) := by
  refine ⟨(hexAction g.val).finrank_map_eq P.val |>.trans P.property.1, ?_, ?_⟩
  · intro w
    change (action hexZ w ∈ P.val.map (hexAction g.val).toLinearMap) ↔
      w ∈ P.val.map (hexAction g.val).toLinearMap
    simp only [Submodule.mem_map_equiv]
    have he : (hexAction g.val).symm = hexAction g.val⁻¹ := (map_inv hexAction g.val).symm
    rw [he]
    change action g.val⁻¹ (action hexZ w) ∈ P.val ↔ action g.val⁻¹ w ∈ P.val
    have hc := even_action_scalar (g⁻¹) w
    change action g.val⁻¹ (action hexZ w) = action hexZ (action g.val⁻¹ w) at hc
    rw [hc]
    exact P.property.2.1 (action g.val⁻¹ w)
  · rintro ⟨v,w,hw,rfl⟩ hn
    have hwn : (⟨w,hw⟩ : P.val) ≠ 0 := by
      intro he
      apply hn
      apply Subtype.ext
      change action g.val w = 0
      rw [show w = 0 from congrArg Subtype.val he, map_zero]
    exact (Monomial.act_weight g.val.val w.val).trans (P.property.2.2 ⟨w,hw⟩ hwn)

def planeImage (g : HexEvenAutomorphisms) (P : FullWeightScalarPlane) : FullWeightScalarPlane :=
  ⟨P.val.map (action g.val), by exact image_full g P⟩

theorem planeImage_one (P : FullWeightScalarPlane) : planeImage 1 P = P := by
  apply Subtype.ext
  change P.val.map (action 1) = P.val
  rw [map_one]
  exact Submodule.map_id _

theorem planeImage_mul (g h : HexEvenAutomorphisms) (P : FullWeightScalarPlane) :
    planeImage (g*h) P = planeImage g (planeImage h P) := by
  apply Subtype.ext
  change P.val.map (action (g.val*h.val)) = (P.val.map (action h.val)).map (action g.val)
  rw [← Submodule.map_comp, map_mul]
  rfl

def planePerm : HexEvenAutomorphisms →* Equiv.Perm FullWeightScalarPlane where
  toFun g :=
    { toFun := planeImage g
      invFun := planeImage g⁻¹
      left_inv := by intro P; rw [← planeImage_mul, inv_mul_cancel, planeImage_one]
      right_inv := by intro P; rw [← planeImage_mul, mul_inv_cancel, planeImage_one] }
  map_one' := by apply _root_.Equiv.ext; intro P; exact planeImage_one P
  map_mul' g h := by apply _root_.Equiv.ext; intro P; exact planeImage_mul g h P

theorem planePerm_fixed_iff (g : HexEvenAutomorphisms) (P : FullWeightScalarPlane) :
    planePerm g P = P ↔ g.val ∈ BinaryOffender.subspaceStabilizer action P.val := by
  change planeImage g P = P ↔ _
  rw [Subtype.ext_iff]
  change P.val.map (action g.val) = P.val ↔ _
  constructor
  · intro he w
    constructor
    · intro hw
      have hh : action g.val w ∈ P.val.map (action g.val) := he.symm ▸ hw
      obtain ⟨v,hv,hvw⟩ := hh
      exact (hexAction g.val).injective hvw ▸ hv
    · intro hw
      rw [← he]
      exact ⟨w,hw,rfl⟩
  · intro hg
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (hg v).2 hv
    · intro hw
      refine ⟨action g.val⁻¹ w, ?_, ?_⟩
      · apply (hg (action g.val⁻¹ w)).1
        simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply] using hw
      · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply]

theorem planePerm_scalar : planePerm hexEvenZ = 1 := by
  apply _root_.Equiv.ext
  intro P
  exact (planePerm_fixed_iff hexEvenZ P).2 P.property.2.1

private theorem planePerm_kernel_le : hexEvenCoordinate.ker ≤ planePerm.ker := by
  rw [hexEvenCoordinate_kernel]
  exact Subgroup.zpowers_le.mpr planePerm_scalar

private noncomputable def coordinatePlanePerm :
    alternatingGroup (Fin 6) →* Equiv.Perm FullWeightScalarPlane :=
  hexEvenCoordinate.liftOfSurjective hexEvenCoordinate_surjective ⟨planePerm, planePerm_kernel_le⟩

private theorem coordinatePlanePerm_apply (g : HexEvenAutomorphisms) :
    coordinatePlanePerm (hexEvenCoordinate g) = planePerm g := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem planePerm_nontrivial : planePerm ⟨hexX,hexX_even⟩ ≠ 1 := by
  intro he
  let P : FullWeightScalarPlane := ⟨fullWeightPlane,fullWeightPlane_isFullWeightScalarPlane⟩
  have hf : planePerm ⟨hexX,hexX_even⟩ P = P := congrArg (fun e : Equiv.Perm _ => e P) he
  have hs := (planePerm_fixed_iff _ P).1 hf
  have hw : fullWeightWord ∈ fullWeightPlane := by
    refine ⟨a,?_⟩
    change (1 : Bit) • fullWeightWord + (0 : Bit) • hexAction hexZ fullWeightWord = fullWeightWord
    simp
  obtain ⟨r,hr⟩ := (hs fullWeightWord).2 hw
  have hc : ∀ r : K, fullWeightPlaneEncoder r ≠ action hexX fullWeightWord := by decide
  exact hc r hr

private theorem coordinatePlanePerm_injective : Function.Injective coordinatePlanePerm := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : coordinatePlanePerm.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact coordinatePlanePerm.ker_eq_bot_iff.mp hb
  · have hh : hexEvenCoordinate ⟨hexX,hexX_even⟩ ∈ coordinatePlanePerm.ker := by rw [ht]; trivial
    have he : coordinatePlanePerm (hexEvenCoordinate ⟨hexX,hexX_even⟩) = 1 := hh
    rw [coordinatePlanePerm_apply] at he
    exact False.elim (planePerm_nontrivial he)

private theorem planePerm_even (g : HexEvenAutomorphisms) :
    planePerm g ∈ alternatingGroup FullWeightScalarPlane := by
  let : Group.IsPerfect HexEvenAutomorphisms := even_isPerfect
  have h := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp planePerm)
  rw [Group.IsPerfect.commutator_eq_top] at h
  exact h (Subgroup.mem_top g)

noncomputable def planeAlternating : HexEvenAutomorphisms →* alternatingGroup FullWeightScalarPlane :=
  planePerm.codRestrict _ (by exact planePerm_even)

private noncomputable def coordinatePlaneAlternating :
    alternatingGroup (Fin 6) →* alternatingGroup FullWeightScalarPlane :=
  coordinatePlanePerm.codRestrict _ (by
    intro g
    obtain ⟨h,rfl⟩ := hexEvenCoordinate_surjective g
    rw [coordinatePlanePerm_apply]
    exact planePerm_even h)

private theorem coordinatePlaneAlternating_bijective :
    Function.Bijective coordinatePlaneAlternating := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro g h he
    exact coordinatePlanePerm_injective (congrArg Subtype.val he)
  · rw [Nat.card_congr (Equiv.altCongrHom
      (Fintype.equivFinOfCardEq fullWeightScalarPlane_card)).toEquiv]

theorem planeAlternating_surjective : Function.Surjective planeAlternating := by
  intro p
  obtain ⟨g,hg⟩ := coordinatePlaneAlternating_bijective.2 p
  obtain ⟨h,rfl⟩ := hexEvenCoordinate_surjective g
  refine ⟨h,?_⟩
  apply Subtype.ext
  exact (coordinatePlanePerm_apply h).symm.trans (congrArg Subtype.val hg)

end Representation.Hexacode
