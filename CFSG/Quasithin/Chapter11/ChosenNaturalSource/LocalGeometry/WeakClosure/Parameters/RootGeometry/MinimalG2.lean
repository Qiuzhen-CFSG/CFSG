module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.Minimal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy

/-!
# Minimal fixed-space recognition on the original G₂ natural module

A minimal automizer involution cannot have nontrivial field action: such an
operator moves 3n quotient dimensions, exceeding the original codimension 2n.
The normalizer theorem removes the remaining scalar, making the involution
inner. The proved root conjugacy theorem places it in a long or short root;
both roots fix the standard three-space. Intrinsic flag uniqueness aligns
that space with the given flag, and exact fixed-vector lifting returns its
full preimage through the original central cover.

This supplies the G₂ minimal-fixed clause of RootGeometry. Source.lean
assembles it with the classical rows and consumes it in the global-parameter
alternative. Source: Aschbacher--Smith 11.2.2(3), printed p.768, using B.4.6.
Root conjugacy uses the existing attributed ATLAS model; no new port is copied.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Atlas.G2
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed
open FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

theorem g2_small_involution_inner
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    letI := D.elementary
    ∀ a : Automizer V, orderOf a = 2 →
      fixedCodim (automizerRepresentation V) (zpowers a) ≤ 2 * S.field.degree →
      a ∈ inducedAutomizer V L := by
  let := D.elementary
  intro a ha hsmall
  let c := Coordinates.g2 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  let : Nontrivial c.Space := Module.nontrivial_of_finrank_pos
    (by change 0 < Module.finrank S.field.Carrier (Natural.Space S.field.Carrier)
        rw [Natural.finrank_space]; decide)
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
  let : Nontrivial (Natural.Space S.field.Carrier) := Module.nontrivial_of_finrank_pos
    (by rw [Natural.finrank_space]; decide :
      0 < Module.finrank S.field.Carrier (Natural.Space S.field.Carrier))
  let f : c.Space →+ Natural.Space S.field.Carrier := {
    toFun := id
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  let E : c.Space ≃ₗ[ZMod 2] Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective (f.toZModLinearMap 2) Function.bijective_id
  let τ : Representation (ZMod 2) (Automizer V) (Natural.Space S.field.Carrier) :=
    E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (a : Automizer V) (v : c.Space) : E (ρ a v) = τ a (E v) := by
    change E (ρ a v) = E (ρ a (E.symm (E v)))
    rw [E.symm_apply_apply]
  let eL : inducedAutomizer V L ≃* Model S.field.Carrier := layerEquiv D S c
  have hres' (b : inducedAutomizer V L) (v : Natural.Space S.field.Carrier) :
      τ b v = Natural.action S.field.Carrier (eL b) v := by
    change E (ρ b (E.symm v)) = _
    rw [hres]
    change Natural.action S.field.Carrier (eL b) (E (E.symm v)) = _
    rw [E.apply_symm_apply]
  let ν := Natural.Normalizer.binary S.field.Carrier
  have hnat (b : inducedAutomizer V L) :
      τ.asGroupHom b = ν.asGroupHom (eL b) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change τ b v = ν (eL b) v
    exact (hres' b v).trans (LinearMap.congr_fun
      (Natural.Normalizer.binary_apply S.field.Carrier (eL b)) v).symm
  have himage : actionImage (τ.comp (inducedAutomizer V L).subtype) = actionImage ν := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨eL b,(hnat b).symm⟩
    · rintro ⟨g,rfl⟩
      refine ⟨eL.symm g,?_⟩
      exact (hnat (eL.symm g)).trans
        (congrArg ν.asGroupHom (eL.apply_symm_apply g))
  let k : Automizer V →* linearNormalizer ν := τ.asGroupHom.codRestrict _ (fun a => by
    change τ.asGroupHom a ∈ normalizer (actionImage ν : Set _)
    rw [← himage]
    exact actionImage_le_linearNormalizer τ (inducedAutomizer V L) ⟨a,rfl⟩)
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
  have hcost : fixedCodim (normalizerRepresentation ν) (zpowers (k a)) =
      fixedCodim τ (zpowers a) := by
    have hf : fixedSpace (normalizerRepresentation ν) (zpowers (k a)) =
        fixedSpace τ (zpowers a) := by
      ext v
      simp only [mem_fixedSpace_zpowers_iff]
      rfl
    unfold fixedCodim
    rw [hf]
  have hbound : fixedCodim (normalizerRepresentation ν) (zpowers (k a)) ≤
      2 * S.field.degree := by
    rw [hcost]
    exact (fixedCodim_le_of_equivariant_surjection (automizerRepresentation V) τ
      (E.toLinearMap.comp (projectionLinear D S c))
      (E.surjective.comp (projectionLinear_surjective D S c))
      (fun a v => (congrArg E (he a v)).trans (hτ a _)) (zpowers a)).trans hsmall
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hi2 : k a ^ 2 = 1 := by rw [← map_pow,ha2,map_one]
  obtain ⟨z,hz⟩ := LieAutomorphismExtensions.semilinearAction_surjective hq
    (Natural.Normalizer.normalizerAutomorphism S.field.Carrier (k a))
  have hs : z.right = 1 := by
    by_contra hn
    have hd := Natural.Normalizer.field_involution_codim S.field.Carrier
      hq S.field.card_eq (k a) hi2 z hz hn
    change fixedCodim (normalizerRepresentation ν) (zpowers (k a)) =
      3 * S.field.degree at hd
    rw [hd] at hbound
    have hn := S.nonbinary
    omega
  obtain ⟨g,hg⟩ := Natural.Normalizer.inner_involution_mem S.field.Carrier hq (k a) hi2 z hz hs
  have heq : a = eL.symm g := hρ (by
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [hτ,hτ,hres',eL.apply_symm_apply]
    exact (congrArg (fun t : linearNormalizer ν => t.val.val (E v)) hg).symm.trans
      (LinearMap.congr_fun (Natural.Normalizer.binary_apply S.field.Carrier g) (E v)))
  rw [heq]
  exact (eL.symm g).property

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed
open Atlas.G2.Natural.OrthogonalCover.SylowFlag
open FullAutomizer

private theorem roots_fix_three {F : Type*} [Field F] [CharP F 2]
    (a : F) (v : Natural.Space F) (hv : v ∈ naturalThreeSpace F) :
    Natural.action F (rootA a) v = v ∧ Natural.action F (rootC a) v = v := by
  obtain ⟨h3,h4,h5⟩ := hv
  change Restricted.NaturalCoordinates.coordinates F v 3 = 0 at h3
  change Restricted.NaturalCoordinates.coordinates F v 4 = 0 at h4
  change Restricted.NaturalCoordinates.coordinates F v 5 = 0 at h5
  constructor <;> apply (coord F).injective
  all_goals
    rw [show coord F (Natural.action F _ v) =
      Restricted.NaturalCoordinates.action F _ (coord F v) from
      LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' _) v]
    ext i
    fin_cases i <;> simp [h3,h4,h5]

private theorem involution_fixes_moved_three {F : Type*} [Field F] [Finite F] [CharP F 2]
    (x : Model F) (hx : orderOf x = 2) :
    ∃ g : Model F, ∀ v ∈ (naturalThreeSpace F).map (Natural.action F g),
      Natural.action F x v = v := by
  have hx2 : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by intro hh; simp [hh] at hx
  rcases EvenInvolutionGeometry.involution_isRoot hx2 hx1 with
    ⟨g,a,_,rfl⟩ | ⟨g,a,_,rfl⟩
  all_goals
    refine ⟨g,?_⟩
    rintro _ ⟨v,hv,rfl⟩
    change Natural.action F (g * _ * g⁻¹) (Natural.action F g v) = _
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [map_mul, Module.End.mul_apply]
  · rw [(roots_fix_three a v hv).1]
  · rw [(roots_fix_three a v hv).2]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

theorem g2_minimal_fixed
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 2 * S.field.degree)
    (hCN : normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hres : ¬ oddCentralizerCondition (normalizer (L : Set G)) V U) :
    ∃ l : L, (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≤ U := by
  let := D.elementary
  let c := Coordinates.g2 m
  obtain ⟨a,ha,hca,hfix⟩ := exists_minimal_involution D S (g2_fixedCodimensions D S m)
    hUV hcor hCN hres
  have haL := g2_small_involution_inner D S m a ha hca.le
  let b : inducedAutomizer V L := ⟨a,haL⟩
  let x := layerEquiv D S c b
  have hx : orderOf x = 2 := ((layerEquiv D S c).orderOf_eq b).trans
    ((Subgroup.orderOf_coe b).symm.trans ha)
  obtain ⟨g,hg⟩ := involution_fixes_moved_three x hx
  obtain ⟨d,hd⟩ := exists_marking S.field.Carrier (G2.modelSylow S m)
  have hf : f.space 2 = movedThreeSpace S.field.Carrier d := by
    have hff := G2.flag_unique S m 2 (f.space 2) (f.dimension 2) (f.invariant 2)
    apply hff.trans
    change (G2.modelFlag S m).space 2 = _
    apply movedThreeSpace_unique S.field.Carrier d _
    · intro q
      exact (G2.modelFlag S m).invariant 2 ⟨q,hd.symm ▸ q.property⟩
    · exact (G2.modelFlag S m).dimension 2
  obtain ⟨l,hl⟩ := c.quotientMap_surjective (g * d.val⁻¹)
  have hmap : (f.space 2).map (c.modelAction (c.quotientMap l)) =
      (naturalThreeSpace S.field.Carrier).map (Natural.action S.field.Carrier g) := by
    rw [hl,hf]
    change ((naturalThreeSpace S.field.Carrier).map (Natural.action S.field.Carrier d.val)).map
      (Natural.action S.field.Carrier (g * d.val⁻¹)) = _
    rw [← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply,← Module.End.mul_apply,← map_mul,inv_mul_cancel_right]
  refine ⟨l,?_⟩
  change (c.preimage (f.space 2)).map (MulAut.conj (l : G)).toMonoidHom ≤ U
  rw [c.preimage_conjugate,hmap]
  intro u hu
  let v : Additive V := Additive.ofMul ⟨u,D.centralQuotientPreimage_le _ hu⟩
  have hv := (c.mem_preimage _ v.toMul).mp hu
  have hxf := hg (c.projection v.toMul).toAdd hv
  obtain ⟨lA,hlA⟩ := layerAction_surjective D b
  have hmodel : c.quotientMap lA = x := by
    rw [← layerEquiv_apply D S c,hlA]
  have hcent := (NaturalFixedSpaces.centralizes_vector_iff D S c lA v.toMul).mpr
    (by rw [hmodel]; exact hxf)
  have hact : automizerRepresentation V a v = v := by
    have hh : (layerAction D lA : Automizer V) = a := congrArg Subtype.val hlA
    rw [← hh]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hcent
  have hvfix := (mem_fixedSpace_zpowers_iff (automizerRepresentation V) a v).mpr hact
  rw [hfix] at hvfix
  exact hvfix

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed
