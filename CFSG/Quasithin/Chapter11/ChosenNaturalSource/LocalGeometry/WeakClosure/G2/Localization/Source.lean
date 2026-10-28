module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.SourceAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.G2

/-!
# R₁ localization through the original G₂ quotient

An A_(2n-1) actor in the original radical is inner by the proved A₂
calculation. Correcting its representative by O₂(LT) lifts it into
L intersect R₁. The concrete five-root calculation then fixes the whole
third preimage, using exact fixed-vector lifting through its central kernel.
The common-frame radical placement is constructed in Localization.Frame;
its source application there removes the image premise below.

Source: Aschbacher--Smith B.4.6(12) and 11.2.2(6), printed pp.89,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
open Atlas.G2 Parameters.FullAutomizer Parameters.RootActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- An inner actor contained in R₁ has a representative in L intersect R₁.
The correction lies in the original O₂(LT), which centralizes V and is
contained in R₁. -/
theorem inner_actor_lifts_in_radical
    {A : Subgroup G} (hAR : A ≤ f.Ri 0)
    (hinner : inducedAutomizer V A ≤ inducedAutomizer V L)
    (a : inducedAutomizer V A) :
    ∃ l : L, (l : G) ∈ f.Ri 0 ∧ (layerAction D l : Automizer V) = a.val := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQR : Q ≤ f.Ri 0 := originalCore_le_Ri D S f 0
  have hQC : Q ≤ centralizer (V : Set G) := by
    dsimp [Q]
    rw [← seed_sylow_centralizer D S]
    exact inf_le_right
  have hLN : L ≤ normalizer (Q : Set G) :=
    le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hjoin := le_component_join_core_of_image D S
    (hAR.trans (localRadical_le_sylow _)) hinner
  obtain ⟨x,hx,he⟩ := a.property
  have hxjoin : x.val ∈ L ⊔ Q := hjoin hx
  change x.val ∈ (↑(L ⊔ Q) : Set G) at hxjoin
  rw [coe_mul_of_left_le_normalizer_right L Q hLN] at hxjoin
  obtain ⟨l,hl,u,hu,hlu⟩ := hxjoin
  have hlR : l ∈ f.Ri 0 := by
    have hh := (f.Ri 0).mul_mem (hAR hx) ((f.Ri 0).inv_mem (hQR hu))
    change x.val * u⁻¹ ∈ f.Ri 0 at hh
    rw [← hlu, mul_inv_cancel_right] at hh
    exact hh
  refine ⟨⟨l,hl⟩,hlR,?_⟩
  rw [← he]
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change l * (v : G) * l⁻¹ = x.val * (v : G) * x.val⁻¹
  rw [← hlu]
  have hc : u * (v : G) * u⁻¹ = v :=
    mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hQC hu) v.val v.property).symm)
  simpa only [mul_inv_rev, mul_assoc] using
    (congrArg (fun z : G => l * z * l⁻¹) hc).symm

/-- Literal images for the point radical in one common model frame. The
first condition identifies the original full third-space preimage; the second
is solely placement of the inner part of the original R₁ action. -/
def PointRadicalImage (g : Model S.field.Carrier) : Prop :=
  f.space 2 =
    ((NaturalOffenders.upper (F := S.field.Carrier)).comap
      (Restricted.NaturalCoordinates.coordinates S.field.Carrier)).map
      (Natural.action S.field.Carrier g) ∧
  ((f.Ri 0).subgroupOf L).map (Coordinates.g2 m).quotientMap ≤
    (LieParabolicSetup.radical₂ (F := S.field.Carrier)).map
      (MulAut.conj g).toMonoidHom

/-- The concrete five-root calculation yields R₁ localization on the original
module and quotient. Only the earlier point-radical image identification is
explicit; no fixed-space or weak-closure conclusion is assumed. -/
theorem r1FamilyLocalization_of_pointRadicalImage
    (g : Model S.field.Carrier) (hg : PointRadicalImage D S m f g) :
    R1FamilyLocalization D S f := by
  let := D.elementary
  intro A hAR hA
  let c := Coordinates.g2 m
  let B := inducedAutomizer V A
  have hinner : B ≤ inducedAutomizer V L :=
    g2_original_two_family_inner D S m B
      (fixedSpaceFamily_mono (automizerRepresentation V) (by decide)
        (by have := S.nonbinary; omega : 2 ≤ 2 * S.field.degree - 1) hA)
  let j₀ : B →* Model S.field.Carrier :=
    (layerEquiv D S c).toMonoidHom.comp (inclusion hinner)
  let j := (MulAut.conj g⁻¹).toMonoidHom.comp j₀
  have hj : j.range ≤ LieParabolicSetup.radical₂ := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨l,hl,he⟩ := inner_actor_lifts_in_radical D S m f hAR hinner a
    have heL : layerAction D l = inclusion hinner a := Subtype.ext he
    have hm : (Coordinates.g2 m).quotientMap l = j₀ a := by
      rw [← layerEquiv_apply D S c, heL]
      rfl
    obtain ⟨b,hb,heq⟩ := hg.2 (mem_map_of_mem _ hl)
    rw [hm] at heq
    change (MulAut.conj g⁻¹) (j₀ a) ∈ _
    change (MulAut.conj g) b = j₀ a at heq
    rw [← heq]
    simpa [MulAut.conj_apply, mul_assoc] using hb
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let e₀ : c.Space ≃ₗ[ZMod 2] Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective
      (({ toFun := id, map_zero' := rfl, map_add' := fun _ _ => rfl } :
        c.Space →+ Natural.Space S.field.Carrier).toZModLinearMap 2)
      Function.bijective_id
  let e₁ := (Natural.OrthogonalCover.SylowFlag.Transport.linear
    (Natural.action S.field.Carrier) g⁻¹).restrictScalars (ZMod 2)
  let e₂ := (Restricted.NaturalCoordinates.equiv S.field.Carrier).restrictScalars (ZMod 2)
  let E := (e₀.trans e₁).trans e₂
  let τ : Representation (ZMod 2) (Automizer V) (Fin 6 → S.field.Carrier) :=
    E.conjRingEquiv.toMonoidHom.comp ρ
  let q := E.toLinearMap.comp (projectionLinear D S c)
  have hτ (a : Automizer V) (v : c.Space) : E (ρ a v) = τ a (E v) := by
    change E (ρ a v) = E (ρ a (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hjact (a : B) (v : Fin 6 → S.field.Carrier) :
      τ a v = Restricted.NaturalCoordinates.action S.field.Carrier (j a) v := by
    change E (ρ a (E.symm v)) = _
    have hr := hres (inclusion hinner a) (E.symm v)
    change ρ (a : Automizer V) (E.symm v) = c.modelAction (j₀ a) (E.symm v) at hr
    rw [hr]
    have hcoord (w : c.Space) :
        E (c.modelAction (j₀ a) w) =
          Restricted.NaturalCoordinates.action S.field.Carrier (j a) (E w) := by
      change Natural.Space S.field.Carrier at w
      change Restricted.NaturalCoordinates.coordinates S.field.Carrier
        (Natural.action S.field.Carrier g⁻¹ (Natural.action S.field.Carrier (j₀ a) w)) =
        Restricted.NaturalCoordinates.action S.field.Carrier (j a)
          (Restricted.NaturalCoordinates.coordinates S.field.Carrier
            (Natural.action S.field.Carrier g⁻¹ w))
      have hc := LinearMap.congr_fun
        ((Restricted.NaturalCoordinates.repEquiv S.field.Carrier).isIntertwining' (j a))
        (Natural.action S.field.Carrier g⁻¹ w)
      change Restricted.NaturalCoordinates.coordinates S.field.Carrier
          (Natural.action S.field.Carrier (j a) (Natural.action S.field.Carrier g⁻¹ w)) =
        Restricted.NaturalCoordinates.action S.field.Carrier (j a)
          (Restricted.NaturalCoordinates.coordinates S.field.Carrier
            (Natural.action S.field.Carrier g⁻¹ w)) at hc
      rw [← hc]
      congr 1
      simp [j, map_mul, Module.End.mul_apply]
    exact (hcoord (E.symm v)).trans
      (congrArg (Restricted.NaturalCoordinates.action S.field.Carrier (j a))
        (E.apply_symm_apply v))
  have hlift (a : B) (x : Additive V) (hx : τ a (q x) = q x) :
      automizerRepresentation V a x = x := by
    apply original_layer_fixed_lifts D S c ρ hres a (hinner a.property) x
    apply E.injective
    exact (hτ a _).trans hx
  intro v hv a ha
  let x : Additive V := Additive.ofMul ⟨v,D.centralQuotientPreimage_le _ hv⟩
  have hx : q x ∈ NaturalOffenders.upper := by
    have hv' := (c.mem_preimage (f.space 2) x.toMul).mp hv
    rw [hg.1] at hv'
    obtain ⟨w,hw,hwv⟩ := hv'
    change Restricted.NaturalCoordinates.coordinates S.field.Carrier
      (Natural.action S.field.Carrier g⁻¹ (c.projection x.toMul).toAdd) ∈ _
    change Natural.action S.field.Carrier g w = (c.projection x.toMul).toAdd at hwv
    rw [← hwv, (Natural.action S.field.Carrier).inv_self_apply]
    exact hw
  have hfix := radical_family_fixes_upper (automizerRepresentation V) τ q
    (E.surjective.comp (projectionLinear_surjective D S c))
    (fun a x => (congrArg E (he a x)).trans (hτ a _)) hA S.field.card_eq
    (by have := S.nonbinary; omega) j hj hjact hlift (q x) hx
  let a' : B := ⟨V.normalizerMonoidHom.rangeRestrict
      ⟨a,S.sylow_normalizes ((localRadical_le_sylow _) (hAR ha))⟩,
    ⟨⟨a,S.sylow_normalizes ((localRadical_le_sylow _) (hAR ha))⟩,ha,rfl⟩⟩
  have hh := hlift a' x (hfix a')
  have hh' := congrArg (fun z : Additive V => (z.toMul : G)) hh
  exact mul_inv_eq_iff_eq_mul.mp hh'

/-- Source 11.2.2(6) with its full fixed-family calculation discharged.
The point-radical image, s=2n and the preceding 11.1.4 bound are retained
literally for the owning source assembly. -/
theorem weakCentralizer_centralizer_le_of_pointRadicalImage
    (g : Model S.field.Carrier) (hg : PointRadicalImage D S m f g)
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) :=
  weakCentralizer_centralizer_le_of_family D S f hs
    (r1FamilyLocalization_of_pointRadicalImage D S m f g hg) hthree
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
