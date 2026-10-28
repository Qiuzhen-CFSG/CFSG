module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Duality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Pencils
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Model

/-!
# Coordinate transport for the literal MS93 dual pencil

Inverse transpose is the graph automorphism of SL₃(2). A dual factor is
therefore a natural factor with its marking composed with that automorphism.
The ambient-action theorem extends its conjugation equation from L to M;
no containment of the untilded local residual in L is needed.

Images of subgroups of U retain their actual carrier. Pulling an image
containment back adds exactly U ∩ C_M(W), which is the pairing kernel.
This gives literal subgroup spans, including spans of conjugate seeds.
The finite line and plane calculations remain separate.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of (1.7)(ii), printed p.848.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
open Subgroup
universe u v
variable {M : Type u} [Group M]

/-- A contragredient factor is natural for the graph-twisted marking. -/
def DualFactor.graphNatural {π : M →* SL} {L H N Z : Subgroup M}
    {z : NaturalFactor π L Z ⊥} (n : DualFactor π L H N Z z) :
    NaturalFactor π L H N where
  marking := z.marking.trans BinaryLinearThree.AutomorphismAction.graph
  coordinates := n.coordinates
  surjective := n.surjective
  kernel := n.kernel
  normalized := n.normalized
  action := n.action

/-- The same specified dual coordinates describe every ambient conjugation. -/
theorem DualFactor.action_all [Finite M] (e : Extension (M := M))
    (hL : (component e.projection e.flag).map e.projection = ⊤)
    {H N Z : Subgroup M} [H.Normal] [N.Normal]
    {z : NaturalFactor e.projection (component e.projection e.flag) Z ⊥}
    (n : DualFactor e.projection (component e.projection e.flag) H N Z z)
    (m : M) (x y : H) (hy : (y : M) = m * (x : M) * m⁻¹) :
    (n.coordinates y).toAdd =
      ((z.marking (e.projection m))⁻¹.val).transpose.mulVec (n.coordinates x).toAdd :=
  Duality.natural_action_all e hL n.graphNatural m x y hy

namespace Incidence.DualGeometry

open FixedGeometry.ValueConstruction

abbrev Space := VectorGroup

/-- The image of an ambient subgroup under coordinates on its carrier. -/
def imageIn {E : Type v} [Group E] (H : Subgroup M) (q : H →* E)
    (A : Subgroup M) : Subgroup E := (A.subgroupOf H).map q

theorem imageIn_mono {E : Type v} [Group E] (H : Subgroup M) (q : H →* E)
    {A B : Subgroup M} (h : A ≤ B) : imageIn H q A ≤ imageIn H q B :=
  map_mono (comap_mono h)

theorem imageIn_sup {E : Type v} [Group E] (H : Subgroup M) (q : H →* E)
    {A B : Subgroup M} (hA : A ≤ H) (hB : B ≤ H) :
    imageIn H q (A ⊔ B) = imageIn H q A ⊔ imageIn H q B := by
  unfold imageIn
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

/-- Coordinate images commute with spans inside their actual carrier. -/
theorem imageIn_iSup {E : Type v} [Group E] {ι : Sort*}
    (H : Subgroup M) (q : H →* E) (A : ι → Subgroup M) (hA : ∀ a, A a ≤ H) :
    imageIn H q (⨆ a, A a) = ⨆ a, imageIn H q (A a) := by
  have he : (⨆ a, A a).subgroupOf H = ⨆ a, (A a).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (iSup_le hA), Subgroup.map_iSup]
    simp_rw [map_subgroupOf_eq_of_le (hA _)]
  unfold imageIn
  rw [he, Subgroup.map_iSup]

/-- A local normal closure is the span of the literal local conjugates. -/
theorem localGenerated_eq_iSup (P A : Subgroup M) (hA : A ≤ P) :
    localGenerated P A = ⨆ p : P, conjugate (p : M) A := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨b, rfl⟩ := isConj_iff.mp hc
    exact (le_iSup (fun p : P => conjugate (p : M) A) b)
      (mem_map_of_mem (MulAut.conj (b : M)).toMonoidHom ha)
  · apply iSup_le
    intro p
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨p * ⟨a, hA ha⟩ * p⁻¹,
      (inferInstance : (normalClosure (A.subgroupOf P : Set P)).Normal).conj_mem
        ⟨a, hA ha⟩ (le_normalClosure ha) p, rfl⟩

/-- Image containment lifts to an ambient containment modulo the intrinsic kernel. -/
theorem lift_imageIn_le {E : Type v} [Group E] (H N A B : Subgroup M)
    (q : H →* E) (hk : q.ker = N.subgroupOf H) (hA : A ≤ H)
    (h : imageIn H q A ≤ imageIn H q B) : A ≤ B ⊔ (H ⊓ N) := by
  intro a ha
  obtain ⟨b, hb, he⟩ := h (mem_map_of_mem q
    (show (⟨a, hA ha⟩ : H) ∈ A.subgroupOf H from ha))
  have hc : b⁻¹ * ⟨a, hA ha⟩ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [hk] at hc
  have hm := (B ⊔ (H ⊓ N)).mul_mem (mem_sup_left hb)
    (mem_sup_right (show (b : M)⁻¹ * a ∈ H ⊓ N from
      ⟨H.mul_mem (H.inv_mem b.property) (hA ha), hc⟩))
  simpa only [subtype_apply, mul_inv_cancel_left] using hm

/-- A span of coordinate images lifts to the corresponding literal subgroup span. -/
theorem lift_imageIn_span {E : Type v} [Group E] (H N A B C : Subgroup M)
    (q : H →* E) (hk : q.ker = N.subgroupOf H)
    (hA : A ≤ H) (hB : B ≤ H) (hC : C ≤ H)
    (h : imageIn H q A ≤ imageIn H q B ⊔ imageIn H q C) :
    A ≤ (B ⊔ C) ⊔ (H ⊓ N) := by
  apply lift_imageIn_le H N A (B ⊔ C) q hk hA
  rwa [imageIn_sup H q hB hC]

/-- Ambient normality is required only for the coordinate carrier. -/
theorem conjugate_le_carrier (H A : Subgroup M) [H.Normal] (hA : A ≤ H) (g : M) :
    conjugate g A ≤ H := by
  rintro _ ⟨a, ha, rfl⟩
  exact (inferInstance : H.Normal).conj_mem a (hA ha) g

/-- An equivariant coordinate map transports literal conjugate subgroups. -/
theorem imageIn_conjugate {E : Type v} [Group E] (H : Subgroup M) [H.Normal]
    (q : H →* E) (A : Subgroup M) (hA : A ≤ H) (g : M) (a : E ≃* E)
    (hact : ∀ x : H, q (MulAut.conjNormal g x) = a (q x)) :
    imageIn H q (conjugate g A) = (imageIn H q A).map a.toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, he⟩ := hx
    let y : H := ⟨b, hA hb⟩
    have hxy : x = MulAut.conjNormal g y := Subtype.ext he.symm
    rw [hxy, hact]
    exact mem_map_of_mem a.toMonoidHom (mem_map_of_mem q (show y ∈ A.subgroupOf H from hb))
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change a (q x) ∈ _
    rw [← hact]
    exact mem_map_of_mem q (show MulAut.conjNormal g x ∈ (conjugate g A).subgroupOf H from
      ⟨x, hx, rfl⟩)

variable [Finite M] {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
    [Z.Normal] [W.Normal]

/-- Dual coordinates transport the conjugates used by the neighboring-plane pencil. -/
theorem dual_image_conjugate (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (A : Subgroup M) (hA : A ≤ generated X) (g : M) :
    imageIn (generated X) n.coordinates (conjugate g A) =
      (imageIn (generated X) n.coordinates A).map
        (vectorAction (BinaryLinearThree.AutomorphismAction.graph
          (d.natural.marking (e.projection g)))).toMonoidHom := by
  apply imageIn_conjugate _ _ _ hA
  intro x
  exact Multiplicative.toAdd.injective (n.action_all e f.component_image g x
    (MulAut.conjNormal g x) rfl)

/-- The lift has exactly the pairing kernel in the published pencil interface. -/
theorem dual_lift_span (d : SourceData e i Z W X)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (A B C : Subgroup M) (hA : A ≤ generated X) (hB : B ≤ generated X)
    (hC : C ≤ generated X)
    (h : imageIn (generated X) n.coordinates A ≤
      imageIn (generated X) n.coordinates B ⊔ imageIn (generated X) n.coordinates C) :
    A ≤ (B ⊔ C) ⊔ pairingKernel X W :=
  lift_imageIn_span _ _ _ _ _ n.coordinates n.kernel hA hB hC h

end Incidence.DualGeometry
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
