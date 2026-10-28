module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.HexacodeSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Residual
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.Representation.HexacodeAction.Cover

/-!
# Transporting the actual residual to the cubic hexacode scalar

Relative C-component membership supplies the canonical comparison
K/O₂(K) ≃ K*, including its formula on quotient representatives. Transporting
`coverResidual_map_center` through that map identifies Y* with the entire
embedded center of K*. A genuine cover-model equivalence therefore gives an
order-three generator of Y*, without recognizing any module.

After module recognition, the faithful actor map and its component image
give a compatible equivalence to the even hexacode group. Its cubic generator
comes from Y, so every local overgroup containing Y contains the actual scalar
in its hexacode image. Scalar placement is proved rather than added to the
recognition hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.21(2), printed p.956 (PDF p.973). The concrete center calculation is the
existing attributed hexacode port exposed by `HexacodeAction.Cover`.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition
variable {G : Type*} [Group G] [Finite G]

/-- The residual's actual star image is the embedded center of K*. -/
theorem residual_star_eq_center (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3) :
    Source.starImage H (coverResidualIn K) =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype := by
  let e := Components.componentStarEquiv H K hKH hK
  have he (k : K) : (e (QuotientGroup.mk' (pCore 2 K) k)).val =
      QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩ :=
    Components.componentStarEquiv_mk H K hKH hK k
  ext x
  constructor
  · rintro ⟨h, ⟨k, hk, hkh⟩, rfl⟩
    have hc : QuotientGroup.mk' (pCore 2 K) k ∈ center (K ⧸ pCore 2 K) :=
      coverResidual_map_center hcenter ▸ mem_map_of_mem _ hk
    refine ⟨e (QuotientGroup.mk' (pCore 2 K) k),
      (centerCongr e ⟨_, hc⟩).property, ?_⟩
    exact (he k).trans (congrArg (QuotientGroup.mk' (pCore 2 H)) (Subtype.ext hkh))
  · rintro ⟨c, hc, rfl⟩
    have hce : e.symm c ∈ center (K ⧸ pCore 2 K) :=
      (centerCongr e.symm ⟨c, hc⟩).property
    rw [← coverResidual_map_center hcenter] at hce
    obtain ⟨k, hk, hkq⟩ := hce
    refine ⟨⟨k, hKH k.property⟩, ⟨k, hk, rfl⟩, ?_⟩
    change QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩ = (c : Source.Hstar H)
    rw [← he, hkq, e.apply_symm_apply]

omit [Finite G] in
/-- Intrinsic hexacode coordinates identify the entire embedded cubic center. -/
theorem embedded_center_eq_zpowers (L : Subgroup G) (e : L ≃* HexEvenAutomorphisms) :
    (center L).map L.subtype = zpowers (e.symm hexEvenZ : G) := by
  have hc : (center HexEvenAutomorphisms).map e.symm.toMonoidHom = center L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e.symm ⟨y, hy⟩).property
    · intro hx
      exact ⟨e x, (centerCongr e ⟨x, hx⟩).property, e.symm_apply_apply x⟩
  rw [← hc, ← Hexacode.even_kernel_eq_center, hexEvenCoordinate_kernel,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

/-- Choose a cubic generator in the actual K* from the genuine cover model.
Its cyclic group is the image of the literal residual Y. -/
theorem exists_residual_generator (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (e : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms) :
    ∃ z ∈ Source.starImage H K, orderOf z = 3 ∧
      zpowers z = Source.starImage H (coverResidualIn K) := by
  let c := (Components.componentStarEquiv H K hKH hK).symm.trans e
  let z : Source.Hstar H := (c.symm hexEvenZ).val
  have hz : orderOf z = 3 := by
    rw [show orderOf z = orderOf (c.symm hexEvenZ) from
      orderOf_injective (Source.starImage H K).subtype
        (Source.starImage H K).subtype_injective _]
    rw [c.symm.orderOf_eq, hexEvenZ_order]
  refine ⟨z, (c.symm hexEvenZ).property, hz, ?_⟩
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  rw [residual_star_eq_center H K hKH hK hc]
  exact (embedded_center_eq_zpowers (Source.starImage H K) c).symm

variable (H K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (f : Source.Hstar H →* HexAutomorphisms) (hf : Function.Injective f)
  (himage : (Source.starImage H K).map f = hexSign.ker)

noncomputable def componentHexEquiv : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms :=
  (Components.componentStarEquiv H K hKH hK).trans
    (((Source.starImage H K).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr himage))

theorem componentHexEquiv_mk (k : K) :
    (componentHexEquiv H K hKH hK f hf himage (QuotientGroup.mk' (pCore 2 K) k)).val =
      f (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) := by
  rfl

include hKH hK hf himage in
theorem scalar_mem_residual_image :
    hexZ ∈ (Source.starImage H (coverResidualIn K)).map f := by
  let e := componentHexEquiv H K hKH hK f hf himage
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hz : hexEvenZ ∈ center HexEvenAutomorphisms := by
    rw [← Hexacode.even_kernel_eq_center, hexEvenCoordinate_kernel]
    exact mem_zpowers _
  have hez : e.symm hexEvenZ ∈ center (K ⧸ pCore 2 K) := by
    rw [mem_center_iff]
    intro g
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      (mem_center_iff.mp hz) (e g)
  rw [← coverResidual_map_center hc] at hez
  obtain ⟨k, hk, he⟩ := hez
  refine ⟨QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩, ?_, ?_⟩
  · refine ⟨⟨k, hKH k.property⟩, ?_, rfl⟩
    exact ⟨k, hk, rfl⟩
  · have hm := congrArg (fun x => (e x).val) he
    rw [e.apply_symm_apply] at hm
    exact (componentHexEquiv_mk H K hKH hK f hf himage k).symm.trans hm

include hKH hK hf himage in
theorem scalar_mem_of_residual_le (P : Subgroup G) (hYP : coverResidualIn K ≤ P) :
    hexZ ∈ (Source.starImage H P).map f := by
  have hm : Source.starImage H (coverResidualIn K) ≤ Source.starImage H P :=
    map_mono (fun x hx => hYP hx)
  exact map_mono hm (scalar_mem_residual_image H K hKH hK f hf himage)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition
