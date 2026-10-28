module
public import Theory.SpecificGroups.SymplecticFour.SmallMoverKernel

/-!
# The unique maximum small mover in an ambient symplectic Sylow subgroup

In Sp4(4), the plane radical has order64 and moving index16. Every other
small offender outside it has order at most16. Small offenders in a faithful
ambient natural action lie in the symplectic component, so Sylow conjugacy
transports this comparison without discarding possible outer automorphisms.
Lifting through the full action kernel gives a unique maximum family with
relative order64 and moving index16.

Source: MS93 (5.0)--(5.4), pp.912--915, specialized to a full Sylow subgroup.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace Representation
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [CharP F 2] [Algebra (ZMod 2) F]
omit [CharP F 2] in
private theorem full_sylow_coordinates
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal] (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (T : Sylow 2 G) :
    ∃ i : unipotent (F := F) →* G, Function.Injective i ∧
      i.range = (T : Subgroup G) ⊓ B ∧
      ∀ D : Subgroup (unipotent (F := F)),
        Nat.card (Vector F ⧸ fixedSpace ρ (D.map i)) =
          CentralRootGeometry.SmallMovers.movingIndex D := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal B
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow (n := 2) hF (by decide))
  have hs : ((P : Subgroup B).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun P : Sylow 2 (Sp F) => (P : Subgroup (Sp F))) hg
  let i := B.subtype.comp (e.symm.toMonoidHom.comp
    ((MulAut.conj g⁻¹).toMonoidHom.comp (unipotent (F := F)).subtype))
  have hi : Function.Injective i := Subtype.val_injective.comp
    (e.symm.injective.comp ((MulAut.conj g⁻¹).injective.comp Subtype.val_injective))
  refine ⟨i,hi,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨u,rfl⟩
      have hu : g⁻¹*u.val*(g⁻¹)⁻¹ ∈ (P : Subgroup B).map e.toMonoidHom := by
        obtain ⟨v,hv,hvu⟩ := (show u.val ∈ ((P : Subgroup B).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom from hs.symm ▸ u.property)
        change g*v*g⁻¹=u.val at hvu
        rw [←hvu,show g⁻¹*(g*v*g⁻¹)*(g⁻¹)⁻¹ = v by group]
        exact hv
      obtain ⟨v,hv,hvu⟩ := hu
      have hev : e.symm (g⁻¹*u.val*(g⁻¹)⁻¹)=v := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact hvu.symm
      change (e.symm (g⁻¹*u.val*(g⁻¹)⁻¹)).val ∈ (T : Subgroup G) ⊓ B
      rw [hev]
      exact ⟨show v.val ∈ (T : Subgroup G) from (show v ∈ (T : Subgroup G).subgroupOf B from hP ▸ hv),v.property⟩
    · rintro ⟨hx,hxB⟩
      let y := e ⟨x,hxB⟩
      have hy : y ∈ (P : Subgroup B).map e.toMonoidHom :=
        mem_map_of_mem e.toMonoidHom (hP.symm ▸ hx)
      have hyU : g*y*g⁻¹ ∈ unipotent := hs ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hy
      refine ⟨⟨g*y*g⁻¹,hyU⟩,?_⟩
      change (e.symm (g⁻¹ * (g*y*g⁻¹) * (g⁻¹)⁻¹)).val = x
      rw [show g⁻¹ * (g*y*g⁻¹) * (g⁻¹)⁻¹ = y by group]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hxB⟩)
  · intro D
    let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
    let τ := σ.comp (unipotent (F := F)).subtype
    let E := SymplecticConjugatePair.Ambient.linearAction σ g⁻¹
    have he (u : unipotent (F := F)) (v : Vector F) : E (τ u v) = ρ (i u) (E v) := by
      change σ g⁻¹ (σ u.val v) = ρ (e.symm (g⁻¹*u.val*(g⁻¹)⁻¹)).val (σ g⁻¹ v)
      rw [hB,e.apply_symm_apply]
      change σ g⁻¹ (σ u.val v) = σ (g⁻¹*u.val*(g⁻¹)⁻¹) (σ g⁻¹ v)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
    have hdim := fixedCodim_map_equivariant τ ρ i E he D
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 2 ^ fixedCodim ρ (D.map i) = _
    rw [←hdim]
    exact CentralRootGeometry.SmallMovers.binary_movingIndex D

/-- The transported plane radical dominates every small offender of order greater than16. -/
theorem exists_sylow_dominating_small_offender
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (T : Sylow 2 G) :
    ∃ A : Subgroup G, A ≤ T ∧ Nat.card A = 64 ∧
      Nat.card (Vector F ⧸ fixedSpace ρ A) = 16 ∧
      ∀ E : Subgroup G, E ≤ T →
        Nat.card (Vector F ⧸ fixedSpace ρ E) ≤ 16 →
        Nat.card (Vector F ⧸ fixedSpace ρ E) ≤ Nat.card E →
        E ≤ A ∨ Nat.card E ≤ 16 := by
  obtain ⟨i,hi,hir,hindex⟩ := full_sylow_coordinates hF B e ρ hB T
  let A := (CentralRootGeometry.wing (F := F) true).map i
  have hc : Nat.card A = 64 := by
    rw [card_map_of_injective hi,CentralRootGeometry.card_wing,hF]
    norm_num
  refine ⟨A,(map_le_range i _).trans (hir ▸ inf_le_left),hc,?_,?_⟩
  · rw [hindex,CentralRootGeometry.SmallMovers.movingIndex_eq_field_sq_of_large_wing]
    · rw [hF]; norm_num
    · exact le_rfl
    · rw [CentralRootGeometry.card_wing,hF]; decide
  · intro E hET hsmall hoff
    have hEB := small_offender_le_symplectic_component hF B hcent e ρ hfaith hB E hsmall hoff
    have hEi : E ≤ i.range := hir.symm ▸ le_inf hET hEB
    have hEm : (E.comap i).map i = E := map_comap_eq_self hEi
    have hEc : Nat.card (E.comap i) = Nat.card E := by
      exact (card_map_of_injective (K := E.comap i) hi).symm.trans
        (congrArg (fun C : Subgroup G => Nat.card C) hEm)
    have hs : CentralRootGeometry.SmallMovers.Small (E.comap i) := by
      constructor
      · rw [←hindex,hEm,hEc]; exact hoff
      · rw [←hindex,hEm]; exact hsmall
    rcases CentralRootGeometry.SmallMovers.small_classification_nonstandard hF (E.comap i) hs with hw | ⟨l,hl⟩
    · exact Or.inl (hEm ▸ map_mono hw)
    · right
      rw [←hEc,hl,CentralRootGeometry.SmallMovers.card_finitePlane,hF]
      decide
end Representation

namespace Representation
variable {G D F : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
/-- The unique maximum lifts with the whole action kernel and its exact indices. -/
theorem sylow_smallMover_unique
    (hF : Nat.card F = 4) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:G) v = symplecticNatural 2 (e b) v)
    (V : Subgroup D) (T : Sylow 2 D) (q : D →* G) (hq : Function.Surjective q)
    (hkT : q.ker ≤ T) (hk : q.ker ≤ centralizer (V : Set D))
    (hindex : ∀ E : Subgroup D, (centralizer (E : Set D)).relIndex V =
      Nat.card (Vector F ⧸ fixedSpace ρ (E.map q))) :
    ∃ E : Subgroup D, Subgroup.SmallMover.Maximal V q.ker T 16 = {E} ∧
      q.ker.relIndex E = 64 ∧ (centralizer (E : Set D)).relIndex V = 16 := by
  obtain ⟨A,hAT,hAc,hAi,hbound⟩ := exists_sylow_dominating_small_offender hF B hcent e ρ hfaith hB
    (T.mapSurjective (f := q) hq)
  let E := A.comap q
  have hEm : E.map q = A := map_comap_eq_self
    (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  have hE : Subgroup.SmallMover.Admissible V q.ker T 16 E := by
    refine ⟨(comap_mono hAT).trans_eq (comap_map_eq_self hkT),?_,?_⟩
    · rw [hindex,relIndex_ker,hEm,hAc,hAi]; decide
    · rw [hindex,hEm,hAi]
  have hmax (C : Subgroup D) (hC : C ∈ Subgroup.SmallMover.Maximal V q.ker T 16) : C = E := by
    obtain ⟨_,hKC,hCM⟩ := (Subgroup.SmallMover.maximal_iff_image_maximal q V T 16
      hkT (le_centralizer_iff.mp hk) C).mp hC
    have hlarge := hCM E hE
    rw [hEm,hAc] at hlarge
    have hcb := hbound (C.map q) (map_mono hC.1.1)
      (by rw [←hindex]; exact hC.1.2.2)
      (by rw [←hindex,←relIndex_ker]; exact hC.1.2.1)
    have hCA : C.map q = A := by
      rcases hcb with hle | hsmall
      · exact eq_of_le_of_card_ge hle (by rwa [hAc])
      · omega
    dsimp only [E]
    rw [←hCA,comap_map_eq_self hKC]
  obtain ⟨C,hC⟩ := Subgroup.SmallMover.maximal_nonempty V q.ker T 16 (by decide)
  have hCE := hmax C hC
  refine ⟨E,?_,?_,?_⟩
  · ext C
    constructor
    · intro hC
      exact Set.mem_singleton_iff.mpr (hmax C hC)
    · rintro rfl
      exact hCE ▸ hC
  · rw [relIndex_ker,hEm,hAc]
  · rw [hindex,hEm,hAi]
end Representation
