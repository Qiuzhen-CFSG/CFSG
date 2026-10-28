module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import Theory.Representation.BinaryPermutation.FiveCentralExtensionCommutative

/-!
# Commutativity from the marked quotient of the original core

The chosen original natural sixteen is the central kernel of the actual
two-core's quotient restriction. Its original marking and a quotient marking
aligned with the same component action give two copies of the literal
five-point core. Conjugation by the original component acts on the whole
two-core and is compatible with both markings. The alternating bilinear
commutator theorem therefore makes that whole two-core commutative.

No lift of an A₅ action to the extension and no core-order bound is assumed.
Source application: Aschbacher--Smith 13.2.8(1), printed p.880, with the
original chosen-module and five-point action of 13.2.1--4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- A quotient marking aligned with the original chosen module makes the
entire actual local two-core commutative. -/
theorem core_commutative_of_marked_quotient
    (d : Context T L V V₁ V₂ V₃)
    (hV : (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal) :
    letI := hV
    let J := L ⊔ (T : Subgroup G)
    let π := QuotientGroup.mk' (V.subgroupOf J)
    let A := (pCore 2 J).map π
    ∀ (ρ : L →* MulAut A),
      (∀ (l : L) (a : A),
        (ρ l a : J ⧸ V.subgroupOf J) =
          π (inclusion le_sup_left l) * a.val * (π (inclusion le_sup_left l))⁻¹) →
      ∀ (c : Multiplicative (BinaryPermutation.core (Fin 5)) ≃* A),
        (∀ l v, c (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
            (d.flag.module.action l).val v.toAdd)) = ρ l (c v)) →
        IsMulCommutative (pCore 2 J) := by
  let := hV
  let J := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf J
  let π := QuotientGroup.mk' U
  let D := pCore 2 J
  let A := D.map π
  dsimp only
  intro ρ hρ c hc
  have hVJ : V ≤ J := d.chosen.le_sylow.trans le_sup_right
  have hUD : U ≤ D := by
    intro v hv
    obtain ⟨x,hx,he⟩ := d.chosen.le_core hv
    exact (show x=v from Subtype.ext he) ▸ hx
  let m : Multiplicative (BinaryPermutation.core (Fin 5)) →* J :=
    d.flag.module.map.codRestrict J (fun v => hVJ (d.flag.module.range_eq.le ⟨v,rfl⟩))
  let i : Multiplicative (BinaryPermutation.core (Fin 5)) →* D :=
    m.codRestrict D (fun v => hUD (d.flag.module.range_eq.le ⟨v,rfl⟩))
  have hi : Function.Injective i := by
    intro v w he
    exact d.flag.module.injective (congrArg (fun x : D => ((x:J):G)) he)
  let q₀ : D →* A := (π.comp D.subtype).codRestrict A
    (fun x => mem_map_of_mem π x.property)
  have hq₀ : Function.Surjective q₀ := by
    rintro ⟨a,⟨x,hx,he⟩⟩
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let q := c.symm.toMonoidHom.comp q₀
  have hq : Function.Surjective q := c.symm.surjective.comp hq₀
  have hqmem (x : D) : x ∈ q.ker ↔ (x:J) ∈ U := by
    change c.symm (q₀ x) = 1 ↔ (x:J) ∈ U
    rw [c.symm.map_eq_one_iff]
    constructor
    · intro he
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val he)
    · intro hx
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
  have hir : i.range = q.ker := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact (hqmem _).mpr (d.flag.module.range_eq.le ⟨v,rfl⟩)
    · intro hx
      obtain ⟨v,hv⟩ := d.flag.module.range_eq.ge ((hqmem x).mp hx)
      exact ⟨v,Subtype.ext (Subtype.ext hv)⟩
  have hcentral : q.ker ≤ center D := by
    intro x hx
    rw [mem_center_iff]
    intro y
    have hy : ((y:J):G) ∈ J.pCoreIn 2 := ⟨y,y.property,rfl⟩
    exact Subtype.ext (Subtype.ext
      ((d.chosen.core_centralizes hy) ((x:J):G) ((hqmem x).mp hx)).symm)
  let f : L →* J := inclusion le_sup_left
  let τ : L →* MulAut D := (MulAut.conjNormal : J →* MulAut D).comp f
  have hqact (l : L) (x : D) : q₀ (τ l x) = ρ l (q₀ x) := by
    apply Subtype.ext
    rw [hρ]
    change π (f l * x.val * (f l)⁻¹) = π (f l) * π x.val * (π (f l))⁻¹
    rw [map_mul,map_mul,map_inv]
  apply BinaryPermutation.FiveCentralExtension.isMulCommutative_of_marked_kernel_and_quotient
    q hq i hi hir hcentral τ d.flag.module.action d.flag.module.onto
  · intro l x
    apply c.injective
    change c (c.symm (q₀ (τ l x))) = _
    rw [c.apply_symm_apply,hqact,hc]
    change ρ l (q₀ x) = ρ l (c (c.symm (q₀ x)))
    rw [c.apply_symm_apply]
  · intro l v
    apply Subtype.ext
    apply Subtype.ext
    exact d.flag.module.equivariant l v.toAdd

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
