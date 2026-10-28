module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualLift
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction.ModelActions
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction.ParabolicQuotient
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The residual-action branch of 14.7.55

Let Y be the embedded two-residual of C_H(V₂), retaining the original V₂.
Literal conjugation on U/(V₁.subgroupOf U) identifies the image of Y with
the residual of the marked point stabilizer. The proof derives the required
centralizer containment and binary-layer commutator bound; it never assumes
that the full centralizer surjects onto the point stabilizer. Normalization
of V₂ gives normalization of Y, so the join Y ⊔ T is the normal product YT.

The actual Sylow supplement and two-group actor kernel transport the concrete
S₃ quotient. The imported coordinate calculation gives the full commutator
span and transitivity. The final theorem states all three clauses on the
literal source quotient, and quotientActor_source_apply identifies its
operators with actual conjugation on every coset.

Earlier source setup, an actual natural/Weyl model identification, and the
marked singular point remain explicit inputs. The natural and Weyl maps and
their equivariance proofs instantiate the common statement. No conclusion
of 14.7.55(6) is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.55(6),
printed p.1066, PDF p.1083; B.4.6, printed pp.88–90. The model uses the
existing attributed ATLAS port (LICENSES/ATLAS.txt).
-/

open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural Atlas.G2.Explicit
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction
@[expose] public noncomputable section

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem point_fixed (f : SingularMap W)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant σ)
    (p : SingularPoints (ZMod 2)) (g : Model (ZMod 2)) (hg : g • p = p)
    (v : W) (hv : v ∈ f.point p) : σ g v = v := by
  have he : (f.point p).map (σ g) = f.point p := by
    rw [← f.point_equivariant σ hf, hg]
  have hmem : σ g v ∈ f.point p := he ▸ Submodule.mem_map_of_mem hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have hinj : Function.Injective (σ g) := by
    intro x y h
    have hh := congrArg (σ g⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh
  have hne : (⟨σ g v,hmem⟩ : f.point p) ≠ 0 := by
    intro h
    exact hv0 (hinj ((congrArg Subtype.val h).trans (map_zero (σ g)).symm))
  have hvne : (⟨v,hv⟩ : f.point p) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨u,_,hu⟩ := (Nat.card_eq_two_iff' (0 : f.point p)).mp (f.point_card p)
  exact congrArg Subtype.val ((hu _ hne).trans (hu _ hvne).symm)

variable {H : Type*} [Group H] [Finite H]

/-- The actual two-residual of the centralizer of the original source subgroup. -/
def sourceResidual (V₂ : Subgroup H) : Subgroup H :=
  (pResidual 2 (centralizer (V₂ : Set H))).map (centralizer (V₂ : Set H)).subtype

omit [Finite H] in
/-- Normalization of V₂ implies normalization of its embedded centralizer residual. -/
theorem sourceResidual_normalized (V₂ T : Subgroup H)
    (hT : T ≤ normalizer (V₂ : Set H)) :
    T ≤ normalizer (sourceResidual V₂ : Set H) := by
  have hc : centralizer (V₂ : Set H) ≤ normalizer (V₂ : Set H) := centralizer_le_normalizer _
  have hn := normal_embedded_pResidual_subgroupOf 2 hc
    (inferInstance : ((centralizer (V₂ : Set H)).subgroupOf
      (normalizer (V₂ : Set H))).Normal)
  exact hT.trans ((normal_subgroupOf_iff_le_normalizer
    ((Subgroup.map_subtype_le _).trans hc)).mp hn)

omit [Finite H] in
open scoped Pointwise in
/-- The source notation YT is the literal normal subgroup product. -/
theorem sourceResidual_product (V₂ T : Subgroup H)
    (hT : T ≤ normalizer (V₂ : Set H)) :
    ((sourceResidual V₂ ⊔ T : Subgroup H) : Set H) = (sourceResidual V₂ : Set H) * (T : Set H) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (sourceResidual_normalized V₂ T hT)

/-- Derive the residual image from the literal quotient conjugation. No
surjectivity of the unquotiented centralizer onto a point stabilizer is assumed. -/
theorem sourceResidual_image
    (U V₁ V₂ : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] (h12 : V₁ ≤ V₂) (h2U : V₂ ≤ U)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (f : SingularMap W) (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant σ) (π : H →* Model (ZMod 2))
    (eQ : Multiplicative W ≃* U ⧸ V₁.subgroupOf U)
    (hact : ∀ (h : H) (u : U),
      σ (π h) (Multiplicative.toAdd (eQ.symm (QuotientGroup.mk' (V₁.subgroupOf U) u))) =
        Multiplicative.toAdd (eQ.symm (QuotientGroup.mk' (V₁.subgroupOf U)
          ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (transportGeometry f.geometry eQ).point p) :
    (sourceResidual V₂).map π = pointResidual π.range p := by
  let q : U →* Multiplicative W := eQ.symm.toMonoidHom.comp (QuotientGroup.mk' (V₁.subgroupOf U))
  have hactq : ∀ (h : H) (u : U), σ (π h) (Multiplicative.toAdd (q u)) =
      Multiplicative.toAdd (q ⟨h * (u : H) * h⁻¹,
        (inferInstance : U.Normal).conj_mem u u.property h⟩) := hact
  have hm : (V₂.subgroupOf U).map q = (f.point p).toAddSubgroup.toSubgroup := by
    apply Subgroup.map_injective (f := eQ.toMonoidHom) eQ.injective
    rw [Subgroup.map_map]
    have he : eQ.toMonoidHom.comp q = QuotientGroup.mk' (V₁.subgroupOf U) := by
      ext u
      exact eQ.apply_symm_apply _
    rw [he, hmark]
    rfl
  let D := (pointParabolic π.range p).comap π
  have hCD : centralizer (V₂ : Set H) ≤ D := by
    intro h hh
    refine ⟨?_, ⟨h,rfl⟩⟩
    change π h • p = p
    apply f.point_injective
    rw [f.point_equivariant σ hf]
    have hfix (v : W) (hv : v ∈ f.point p) : σ (π h) v = v := by
      have hvm : Multiplicative.ofAdd v ∈ (V₂.subgroupOf U).map q := by rw [hm]; exact hv
      obtain ⟨u,hu,he⟩ := hvm
      have he' : Multiplicative.toAdd (q u) = v := congrArg Multiplicative.toAdd he
      rw [← he', hactq]
      have hc : h * (u : H) * h⁻¹ = u := by
        have hc := (mem_centralizer_iff.mp hh) u hu
        rw [← hc]
        group
      exact congrArg (fun x : U => Multiplicative.toAdd (q x)) (Subtype.ext hc)
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      rwa [hfix v hv]
    · intro v hv
      exact ⟨v,hv,hfix v hv⟩
  have hcomm : ⁅V₂,D⁆ ≤ V₁ := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro h hh v hv
    let u : U := ⟨v,h2U hv⟩
    have hu : Multiplicative.toAdd (q u) ∈ f.point p := by
      change q u ∈ (f.point p).toAddSubgroup.toSubgroup
      rw [← hm]
      exact Subgroup.mem_map_of_mem q hv
    have hfix := point_fixed f σ hf p (π h) hh.1 (Multiplicative.toAdd (q u)) hu
    rw [hactq] at hfix
    have he : QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨h*v*h⁻¹,(inferInstance : U.Normal).conj_mem v (h2U hv) h⟩ = QuotientGroup.mk' (V₁.subgroupOf U) u :=
      eQ.symm.injective (Multiplicative.toAdd.injective hfix)
    have hk : QuotientGroup.mk' (V₁.subgroupOf U)
        (⟨h*v*h⁻¹,(inferInstance : U.Normal).conj_mem v (h2U hv) h⟩ * u⁻¹) = 1 := by
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hk' : (⟨h*v*h⁻¹,(inferInstance : U.Normal).conj_mem v (h2U hv) h⟩ : U) * u⁻¹ ∈
        V₁.subgroupOf U := (QuotientGroup.eq_one_iff _).mp hk
    exact hk'
  have hDimage : D.map π = pointParabolic π.range p :=
    Subgroup.map_comap_eq_self inf_le_right
  have he := source_centralizer_residual_image V₂ V₁ D h12 hcomm
    (le_top.trans hcentral) hCD π
  rw [hDimage] at he
  exact he


variable {Q : Type*} [Group Q]

/-- The model action transported to the literal quotient carrier. -/
def quotientActor (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (eQ : Multiplicative W ≃* Q) (g : Model (ZMod 2)) : Q →* Q :=
  eQ.toMonoidHom.comp ((σ g).toAddMonoidHom.toMultiplicative.comp eQ.symm.toMonoidHom)

private theorem quotientActor_image (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (eQ : Multiplicative W ≃* Q) (g : Model (ZMod 2)) (S : Submodule (ZMod 2) W) :
    (S.toAddSubgroup.toSubgroup.map eQ.toMonoidHom).map (quotientActor σ eQ g) =
      (S.map (σ g)).toAddSubgroup.toSubgroup.map eQ.toMonoidHom := by
  ext q
  constructor
  · rintro ⟨_,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd (σ g (Multiplicative.toAdd v)), ⟨_,hv,rfl⟩, ?_⟩
    simp [quotientActor]
  · rintro ⟨v,⟨w,hw,he⟩,rfl⟩
    refine ⟨eQ (Multiplicative.ofAdd w), ⟨_,hw,rfl⟩, ?_⟩
    simp only [quotientActor, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulEquiv.symm_apply_apply]
    change eQ (Multiplicative.ofAdd (σ g w)) = eQ v
    exact congrArg eQ (congrArg Multiplicative.ofAdd he)

theorem quotientActor_line (f : SingularMap W)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant σ)
    (eQ : Multiplicative W ≃* Q) (g : Model (ZMod 2)) (L : ZeroProductLine (ZMod 2)) :
    ((transportGeometry f.geometry eQ).line L).map (quotientActor σ eQ g) =
      (transportGeometry f.geometry eQ).line (g • L) := by
  change ((f.line L).toAddSubgroup.toSubgroup.map eQ.toMonoidHom).map _ =
    (f.line (g • L)).toAddSubgroup.toSubgroup.map eQ.toMonoidHom
  rw [quotientActor_image, f.line_equivariant σ hf]

/-- A Sylow supplement and a two-group actor kernel identify the literal
source quotient with the point-parabolic quotient. The latter's concrete
S₃ identification is a separate model calculation. -/
def residualSylowCoreEquiv (π : H →* Model (ZMod 2))
    (P : Subgroup (Model (ZMod 2))) (hP : P ≤ π.range) (Y : Subgroup H)
    (hY : Y.map π = (pResidual 2 P).map P.subtype)
    (T : Sylow 2 H) (hT : (T : Subgroup H) ≤ P.comap π)
    (hk : IsPGroup 2 π.ker) :
    (Y ⊔ (T : Subgroup H) : Subgroup H) ⧸ pCore 2 (Y ⊔ (T : Subgroup H) : Subgroup H) ≃*
      P ⧸ pCore 2 P := by
  let D := P.comap π
  have hD : D.map π = P := Subgroup.map_comap_eq_self hP
  have hs := congrArg (Subgroup.map D.subtype)
    (Subgroup.pResidual_sup_sylow_eq_top (T.subtype hT))
  rw [Subgroup.map_sup, Sylow.coe_subtype,
    Subgroup.map_subgroupOf_eq_of_le hT, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hs
  have hi : (Y ⊔ (T : Subgroup H)).map π = P := by
    have hh := congrArg (Subgroup.map π) hs
    rw [Subgroup.map_sup, map_embedded_pResidual, hD] at hh
    rwa [Subgroup.map_sup, hY]
  let L := Y ⊔ (T : Subgroup H)
  let a : L →* P := (π.comp L.subtype).codRestrict P (by
    intro l
    rw [← hi]
    exact Subgroup.mem_map_of_mem π l.property)
  have ha : Function.Surjective a := by
    intro p
    have hp : (p : Model (ZMod 2)) ∈ L.map π := hi.symm ▸ p.property
    obtain ⟨l,hl,he⟩ := hp
    exact ⟨⟨l,hl⟩,Subtype.ext he⟩
  have hka : a.ker = π.ker.comap L.subtype := by
    ext l
    change a l = 1 ↔ π l = 1
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  apply a.pCoreQuotientEquiv ha
  rw [hka]
  exact hk.comap_of_injective L.subtype L.subtype_injective


omit [Finite H] in
theorem quotientActor_point (f : SingularMap W)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant σ)
    (eQ : Multiplicative W ≃* Q) (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    ((transportGeometry f.geometry eQ).point p).map (quotientActor σ eQ g) =
      (transportGeometry f.geometry eQ).point (g • p) := by
  change ((f.point p).toAddSubgroup.toSubgroup.map eQ.toMonoidHom).map _ =
    (f.point (g • p)).toAddSubgroup.toSubgroup.map eQ.toMonoidHom
  rw [quotientActor_image, f.point_equivariant σ hf]


section SourceApplication
variable (U V₁ V₂ : Subgroup H) [U.Normal] [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 V₁] (h12 : V₁ ≤ V₂) (h2U : V₂ ≤ U)
    (hcentral : (⊤ : Subgroup H) ≤ centralizer (V₁ : Set H))
    (f : SingularMap W) (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant σ) (π : H →* Model (ZMod 2))
    (hJ : commutator (Model (ZMod 2)) ≤ π.range)
    (eQ : Multiplicative W ≃* U ⧸ V₁.subgroupOf U)
    (hact : ∀ (h : H) (u : U),
      σ (π h) (Multiplicative.toAdd (eQ.symm (QuotientGroup.mk' (V₁.subgroupOf U) u))) =
        Multiplicative.toAdd (eQ.symm (QuotientGroup.mk' (V₁.subgroupOf U)
          ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (transportGeometry f.geometry eQ).point p)

omit [Finite H] [IsElementaryAbelian 2 V₁] in
include hact in
/-- The transported operator is the actual quotient conjugation on every class. -/
theorem quotientActor_source_apply (h : H) (u : U) :
    quotientActor σ eQ (π h) (QuotientGroup.mk' (V₁.subgroupOf U) u) =
      QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩ := by
  change eQ (Multiplicative.ofAdd (σ (π h)
    (Multiplicative.toAdd (eQ.symm (QuotientGroup.mk' (V₁.subgroupOf U) u))))) = _
  rw [hact]
  exact eQ.apply_symm_apply _


omit [IsElementaryAbelian 2 V₁] in
include hf hact hmark in
/-- Source normalization of V₂ preserves its marked singular point. -/
theorem source_normalizer_point (h : H) (hn : h ∈ normalizer (V₂ : Set H)) :
    π h • p = p := by
  apply (transportGeometry f.geometry eQ).point.injective
  apply Subgroup.eq_of_le_of_card_ge
  · rw [← quotientActor_point f σ hf]
    rintro _ ⟨v,hv,rfl⟩
    rw [← hmark] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    rw [quotientActor_source_apply U V₁ σ π eQ hact]
    rw [← hmark]
    refine ⟨⟨h * (u : H) * h⁻¹, (inferInstance : U.Normal).conj_mem u u.property h⟩, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn u).mp hu
  · rw [(transportGeometry f.geometry eQ).point_card,
      (transportGeometry f.geometry eQ).point_card]

include h12 h2U hcentral hf hact hmark in
/-- Remove the actual two-group actor kernel and use the source Sylow
supplement; only the concrete point-parabolic core quotient remains. -/
def source_pointCoreEquiv (T : Sylow 2 H)
    (hT : (T : Subgroup H) ≤ normalizer (V₂ : Set H)) (hk : IsPGroup 2 π.ker) :
    (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ⧸
        pCore 2 (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ≃*
      (pointParabolic π.range p) ⧸ pCore 2 (pointParabolic π.range p) := by
  apply residualSylowCoreEquiv π _ inf_le_right (sourceResidual V₂)
    (sourceResidual_image U V₁ V₂ h12 h2U hcentral f σ hf π eQ hact p hmark) T
  · intro t ht
    exact ⟨source_normalizer_point U V₁ V₂ f σ hf π eQ hact p hmark t (hT ht), ⟨t,rfl⟩⟩
  · exact hk


include h12 h2U hcentral hf hJ hact hmark in
/-- The source quotient YT/O₂(YT) is the actual symmetric group on three letters. -/
def source_symmetricThreeEquiv (T : Sylow 2 H)
    (hT : (T : Subgroup H) ≤ normalizer (V₂ : Set H)) (hk : IsPGroup 2 π.ker) :
    (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ⧸
        pCore 2 (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ≃* Equiv.Perm (Fin 3) :=
  (source_pointCoreEquiv U V₁ V₂ h12 h2U hcentral f σ hf π eQ hact p hmark T hT hk).trans
    (pointParabolicCoreEquiv π.range hJ p)

include h12 h2U hcentral hf hJ hact hmark in
/-- The original Y acts transitively on the actual three-line quotient pencil. -/
theorem source_pencil_transitive
    (L M : Subgroup (U ⧸ V₁.subgroupOf U))
    (hL : L ∈ quotientPencil (transportGeometry f.geometry eQ)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))))
    (hM : M ∈ quotientPencil (transportGeometry f.geometry eQ)
      ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)))) :
    ∃ y ∈ sourceResidual V₂, L.map (quotientActor σ eQ (π y)) = M := by
  obtain ⟨⟨L,rfl⟩,hL⟩ := hL
  obtain ⟨⟨M,rfl⟩,hM⟩ := hM
  rw [hmark] at hL hM
  obtain ⟨g,hg,he⟩ := pencil_transitive π.range hJ p L M
    (((transportGeometry f.geometry eQ).incidence p L).mpr hL)
    (((transportGeometry f.geometry eQ).incidence p M).mpr hM)
  rw [← sourceResidual_image U V₁ V₂ h12 h2U hcentral f σ hf π eQ hact p hmark] at hg
  obtain ⟨y,hy,rfl⟩ := hg
  exact ⟨y,hy,by rw [quotientActor_line f σ hf, he]⟩

include h12 h2U hcentral hf hJ hact hmark in
/-- The source pencil's actual Y-action generates its entire module span. -/
theorem source_pencil_commutator :
    subspaceCommutator (σ.comp π) (pencilSpan f p) (sourceResidual V₂) = pencilSpan f p := by
  have hh := subspaceCommutator_map_embedding (σ.comp π) σ π (LinearMap.id : W →ₗ[ZMod 2] W)
    (fun _ _ => rfl) (sourceResidual V₂) (pencilSpan f p)
  rw [sourceResidual_image U V₁ V₂ h12 h2U hcentral f σ hf π eQ hact p hmark,
    pencilSpan_commutator f σ hf π.range hJ p] at hh
  simpa only [Submodule.map_id] using hh

include h12 h2U hcentral hf hJ hact hmark in
/-- In the literal quotient, the image of the commutator of the pencil preimage
with the original Y is exactly the pencil span. -/
theorem source_quotient_pencil_commutator :
    let q := QuotientGroup.mk' (V₁.subgroupOf U)
    let S := quotientPencilSpan (transportGeometry f.geometry eQ) ((V₂.subgroupOf U).map q)
    let P := (S.comap q).map U.subtype
    (⁅P,sourceResidual V₂⁆.subgroupOf U).map q = S := by
  intro q S P
  let : Module (ZMod 2) (Additive (Multiplicative W)) := inferInstanceAs (Module (ZMod 2) W)
  let qW := eQ.symm.toMonoidHom.comp q
  have hS : S = (pencilSpan f p).toAddSubgroup.toSubgroup.map eQ.toMonoidHom := by
    dsimp [S]
    rw [hmark, quotientPencilSpan_eq]
    rfl
  have hP : (P.subgroupOf U).map q = S := by
    change (((S.comap q).map U.subtype).comap U.subtype).map q = S
    rw [Subgroup.comap_map_eq_self_of_injective U.subtype_injective,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hPW : binarySubgroup (pencilSpan f p) = (P.subgroupOf U).map qW := by
    rw [← Subgroup.map_map, hP, hS, Subgroup.map_map]
    have he : eQ.symm.toMonoidHom.comp eQ.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [he, Subgroup.map_id]
    rfl
  have hn : sourceResidual V₂ ≤ normalizer (U : Set H) := by rw [Subgroup.normalizer_eq_top]; exact le_top
  let k : sourceResidual V₂ →* Model (ZMod 2) := π.comp (sourceResidual V₂).subtype
  have hk : k.range = pointResidual π.range p := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact sourceResidual_image U V₁ V₂ h12 h2U hcentral f σ hf π eQ hact p hmark
  have he := commutator_image_eq (Q := Multiplicative W) σ U P (sourceResidual V₂)
    hn (Subgroup.map_subtype_le _) k qW (fun y u => hact y u) (pencilSpan f p) hPW
  change (⁅P,sourceResidual V₂⁆.subgroupOf U).map qW =
    (subspaceCommutator σ (pencilSpan f p) k.range).toAddSubgroup.toSubgroup at he
  rw [hk, pencilSpan_commutator f σ hf π.range hJ p] at he
  have hh := congrArg (Subgroup.map eQ.toMonoidHom) he
  rw [Subgroup.map_map] at hh
  have heq : eQ.toMonoidHom.comp qW = q := by ext u; exact eQ.apply_symm_apply _
  rw [heq] at hh
  exact hh.trans hS.symm

include h12 h2U hcentral hf hJ hact hmark in
/-- All three assertions of 14.7.55(6), for the literal source quotient and
the actual residual of C_H(V₂). Natural and Weyl realizations instantiate f
and σ with their published equivariance proofs. -/
theorem source_residual_action (T : Sylow 2 H)
    (hT : (T : Subgroup H) ≤ normalizer (V₂ : Set H)) (hk : IsPGroup 2 π.ker) :
    let q := QuotientGroup.mk' (V₁.subgroupOf U)
    let geom := transportGeometry f.geometry eQ
    let markedPoint := (V₂.subgroupOf U).map q
    let S := quotientPencilSpan geom markedPoint
    let P := (S.comap q).map U.subtype
    Nonempty ((sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ⧸
      pCore 2 (sourceResidual V₂ ⊔ (T : Subgroup H) : Subgroup H) ≃* Equiv.Perm (Fin 3)) ∧
    (⁅P,sourceResidual V₂⁆.subgroupOf U).map q = S ∧
    ∀ L ∈ quotientPencil geom markedPoint, ∀ M ∈ quotientPencil geom markedPoint,
      ∃ y ∈ sourceResidual V₂, L.map (quotientActor σ eQ (π y)) = M := by
  refine ⟨⟨source_symmetricThreeEquiv U V₁ V₂ h12 h2U hcentral f σ hf π hJ eQ hact p hmark T hT hk⟩,
    source_quotient_pencil_commutator U V₁ V₂ h12 h2U hcentral f σ hf π hJ eQ hact p hmark, ?_⟩
  intro L hL M hM
  exact source_pencil_transitive U V₁ V₂ h12 h2U hcentral f σ hf π hJ eQ hact p hmark L M hL hM


end SourceApplication

end
end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction
