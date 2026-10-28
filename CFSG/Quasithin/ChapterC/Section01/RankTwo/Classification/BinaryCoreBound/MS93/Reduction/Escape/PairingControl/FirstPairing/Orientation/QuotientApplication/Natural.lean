module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic

/-!
# Natural coordinates on the actual Z-image

In G_alpha/D_alpha the fixed summand of Z_alpha vanishes and U_alpha
embeds. Hence the image of Z_alpha is genuinely isomorphic to U_alpha,
and its coordinates inherit the given marking and conjugation formula.
No recognition tag or new quotient carrier is used. The decomposition
argument follows the natural-image construction in EdgeTransfer/Extension.

Source: Meierfrankenfeld--Stellmacher (1993), first application of (1.7)
in (4.3.2)(2), printed p.883.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
theorem natural_disjoint_denominator (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    Disjoint ((U R a).subgroupOf (stabilizer R a)) (denominator a) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  apply Subtype.ext
  exact (EdgeTransfer.U_fixed_eq_bot modules a ha).le ⟨hx.1, hx.2.2⟩

/-- The two images are literally equal in G_alpha/D_alpha. -/
theorem quotientImage_Z_eq_U (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    quotientImage a (Z R a) = quotientImage a (U R a) := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hjoin : Z R a ⊔ fixedCore R a = U R a ⊔ fixedCore R a := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [s.decomposition_at a ha]
      refine sup_le le_sup_left (le_trans ?_ le_sup_right)
      exact le_inf (inf_le_left.trans (by
        rw [← modules.X_eq_Z a ha]
        exact omegaCenter_le _))
        (inf_le_right.trans (centralizer_le (Ltilde_le_stabilizer a)))
    · exact sup_le_sup_right (U_le_Z a) _
  have hZS := Z_le_stabilizer R a
  have hUS := (U_le_Z (R := R) a).trans hZS
  have hDS : fixedCore R a ≤ stabilizer R a := inf_le_left.trans (fun _ hx => hx.1)
  have hz := congrArg (fun K : Subgroup (FreeAmalgam R) => quotientImage a K) hjoin
  have hkill : quotientImage a (fixedCore R a) = ⊥ :=
    (quotientImage_eq_bot_iff a _ hDS).mpr le_rfl
  simpa only [quotientImage, subgroupOf_sup hZS hDS, subgroupOf_sup hUS hDS,
    Subgroup.map_sup, show ((fixedCore R a).subgroupOf (stabilizer R a)).map
      (quotientMap a) = ⊥ from hkill, sup_bot_eq] using hz

/-- The restriction of the quotient map has the exact natural image. -/
noncomputable def naturalImageMap (a : Vertex R) :
    (U R a).subgroupOf (stabilizer R a) →* quotientImage a (Z R a) :=
  ((quotientMap a).comp ((U R a).subgroupOf (stabilizer R a)).subtype).codRestrict _
    (fun x => mem_map_of_mem _ (U_le_Z a x.property))

theorem naturalImageMap_bijective (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) : Function.Bijective (naturalImageMap a) := by
  constructor
  · apply (naturalImageMap a).ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hq : quotientMap a (x : stabilizer R a) = 1 := congrArg Subtype.val hx
    have hD : (x : stabilizer R a) ∈ denominator a := (QuotientGroup.eq_one_iff _).mp hq
    exact disjoint_iff_inf_le.mp (natural_disjoint_denominator modules a ha) ⟨x.property, hD⟩
  · intro z
    have hz : (z : LocalQuotient a) ∈ quotientImage a (U R a) :=
      (quotientImage_Z_eq_U modules a ha) ▸ z.property
    obtain ⟨u, hu, he⟩ := hz
    exact ⟨⟨u, hu⟩, Subtype.ext he⟩

/-- The natural subgroup and the literal Z-image are actually isomorphic. -/
noncomputable def naturalImageEquiv (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    (U R a).subgroupOf (stabilizer R a) ≃* quotientImage a (Z R a) :=
  MulEquiv.ofBijective (naturalImageMap a) (naturalImageMap_bijective modules a ha)

@[simp] theorem naturalImageEquiv_apply (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false)
    (u : (U R a).subgroupOf (stabilizer R a)) :
    (naturalImageEquiv modules a ha u : LocalQuotient a) =
      quotientMap a (u : stabilizer R a) := rfl

/-- Descend the supplied coordinates, preserving their exact marking. -/
noncomputable def naturalZ (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) (f : FrameAt a) :
    NaturalFactor (quotientProjection a f.projection f.natural_section.projection_kernel)
      ⊤ (quotientImage a (Z R a)) ⊥ := by
  let E := naturalImageEquiv modules a ha
  let c := E.symm.trans f.naturalU.equivOfBot
  let hn := quotientImage_normal a (Z R a) (Z_normalized R a)
  refine {
    marking := f.naturalU.marking
    coordinates := c.toMonoidHom
    surjective := c.surjective
    kernel := ?_
    normalized := le_normalizer_of_normal
    action := ?_ }
  · rw [bot_subgroupOf]
    exact c.toMonoidHom.ker_eq_bot_iff.mpr c.injective
  · intro l _ x y hy
    obtain ⟨l₀, rfl⟩ := QuotientGroup.mk'_surjective (denominator a) l
    let u := E.symm x
    let v := E.symm y
    have hu : (l₀ : stabilizer R a) * (u : stabilizer R a) * l₀⁻¹ ∈
        (U R a).subgroupOf (stabilizer R a) :=
      (mem_normalizer_iff.mp (f.naturalU.normalized (mem_top l₀)) _).mp u.property
    let z : (U R a).subgroupOf (stabilizer R a) := ⟨_, hu⟩
    have hz : E z = y := by
      apply Subtype.ext
      change quotientMap a (l₀ * (u : stabilizer R a) * l₀⁻¹) = (y : LocalQuotient a)
      rw [map_mul, map_mul, map_inv]
      have hx : quotientMap a (u : stabilizer R a) = (x : LocalQuotient a) :=
        congrArg Subtype.val (E.apply_symm_apply x)
      rw [hx]
      exact hy.symm
    have hv : (v : stabilizer R a) = l₀ * (u : stabilizer R a) * l₀⁻¹ := by
      have he : v = z := E.injective ((E.apply_symm_apply y).trans hz.symm)
      exact congrArg Subtype.val he
    exact f.naturalU.action l₀ (mem_top _) u v hv

@[simp] theorem naturalZ_marking (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) (f : FrameAt a) :
    (naturalZ modules a ha f).marking = f.naturalU.marking := rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
