module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry

/-!
# An inverter in the selected root component

Sylow conjugacy carries the rotation subgroup of the checked pentagon
embedding to the prescribed order-five subgroup. Its reflection inverts
that whole subgroup. Transport through the marked E₄ × A₅ centralizer
puts the involution in the actual root component; the model's fusion
marking then identifies its ambient class with the class of the seed z.

This proves the inverter clause independently of the normalizer and of
the different component E(C_G(E)).

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem model_inverter (P : Subgroup (alternatingGroup (Fin 5)))
    (hP : Nat.card P = 5) :
    ∃ j : alternatingGroup (Fin 5), orderOf j = 2 ∧
      ∀ x ∈ P, j * x * j⁻¹ = x⁻¹ := by
  let f := alternatingGroup.FiveLocalGeometry.dihedralHom
  let c := f (DihedralGroup.r 1)
  let d := f (DihedralGroup.sr 0)
  have hc : orderOf c = 5 := by
    rw [orderOf_injective f alternatingGroup.FiveLocalGeometry.dihedralHom_injective]
    exact DihedralGroup.orderOf_r_one
  have hd : orderOf d = 2 := by
    rw [orderOf_injective f alternatingGroup.FiveLocalGeometry.dihedralHom_injective]
    exact DihedralGroup.orderOf_sr _
  have hdc : d * c * d⁻¹ = c⁻¹ := by
    change f _ * f _ * (f _)⁻¹ = (f _)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
  let Q := zpowers c
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    alternatingGroup.FiveLocalGeometry.card
  let SP : Sylow 5 (alternatingGroup (Fin 5)) := Sylow.ofCard P (by
    rw [hP, hcard]
    decide +kernel)
  let SQ : Sylow 5 (alternatingGroup (Fin 5)) := Sylow.ofCard Q (by
    rw [Nat.card_zpowers, hc, hcard]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) SP SQ
  have hPQ : P.map (MulAut.conj g).toMonoidHom = Q := by
    have h := congrArg (fun R : Sylow 5 (alternatingGroup (Fin 5)) =>
      (R : Subgroup (alternatingGroup (Fin 5)))) hg
    exact h
  let a := MulAut.conj g
  refine ⟨a.symm d, (a.symm.orderOf_eq d).trans hd, ?_⟩
  intro x hx
  apply a.injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hax : a x ∈ Q := hPQ ▸ mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := hax
  rw [← hk]
  have hdck : d * c ^ k * d⁻¹ = (c⁻¹) ^ k := by
    calc
      _ = (MulAut.conj d) (c ^ k) := rfl
      _ = ((MulAut.conj d) c) ^ k := map_zpow _ _ _
      _ = (c⁻¹) ^ k := by rw [show (MulAut.conj d) c = c⁻¹ from hdc]
  simpa only [inv_zpow] using hdck

variable {G : Type*} [Group G] [Finite G]

/-- The chosen root component contains an involution inverting E, with the
ambient fusion marking prescribed by the second-centralizer model. -/
theorem selected_inverter {D : Seed G} (S : InvolutionGeometry.SelectedGeometry D)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t) :
    ∃ j ∈ InvolutionGeometry.rootComponent S.t, IsConj D.z j ∧
      orderOf j = 2 ∧ ∀ x ∈ E, j * x * j⁻¹ = x⁻¹ := by
  let f : alternatingGroup (Fin 5) →* G :=
    S.model.embedding.comp (MonoidHom.inr InvolutionGeometry.E4 (alternatingGroup (Fin 5)))
  have hf : Function.Injective f := S.model.embedding_injective.comp (by
    intro x y h
    exact congrArg Prod.snd h)
  have hr : f.range = S.model.fiveFactor := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(1, a), ⟨rfl, mem_top _⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      have h1 : a.1 = 1 := ha.1
      change S.model.embedding (1, a.2) = S.model.embedding a
      rw [← h1]
  have hEr : E ≤ f.range := by
    rw [hr]
    exact five_le_fiveFactor S.model E hE hEt
  let P := E.comap f
  have hmap : P.map f = E := map_comap_eq_self hEr
  have hP : Nat.card P = 5 := by
    rw [← card_map_of_injective hf, hmap, hE]
  obtain ⟨j, hj, hinv⟩ := model_inverter P hP
  have hjt : f j ∈ involutionCentralizer S.t := (S.model.equiv.symm (1, j)).property
  have hj2 : orderOf (f j) = 2 := (orderOf_injective f hf j).trans hj
  refine ⟨f j, ?_, ?_, hj2, ?_⟩
  · rw [S.component_eq, ← hr]
    exact ⟨j, rfl⟩
  · apply (S.model.fusion ⟨f j, hjt⟩ ?_).mpr
    · change (S.model.equiv (S.model.equiv.symm (1, j))).1 = 1
      simp only [S.model.equiv.apply_symm_apply]
    · exact (orderOf_injective (involutionCentralizer S.t).subtype
        (involutionCentralizer S.t).subtype_injective _).symm.trans hj2
  · intro x hx
    have hx' : x ∈ P.map f := hmap ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    simpa only [map_mul, map_inv] using congrArg f (hinv y hy)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
