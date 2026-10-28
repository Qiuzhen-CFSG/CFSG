module
public import CFSG.Quasithin.ChapterG.Section09.ConstituentActionDual
public import Theory.Representation.NormalComponentConstituents.Exchanged

/-!
# Comparing conjugate components through an exchanged constituent

An equal conjugate constituent gives an ordinary quasiequivalence. When the
conjugate complements an isotropic constituent, the invariant nondegenerate
form gives the contragredient comparison. The conjugation and dual actions
use their literal inverse conventions throughout.

Source: Aschbacher--Smith G.11.6, printed p.366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
 [FiniteDimensional (ZMod 2) V]
 (ρ : Representation (ZMod 2) G V) (H : Subgroup G) [H.Normal]
 (I : Submodule (ZMod 2) V) (hI : H ≤ subspaceStabilizer ρ I)

/-- A conjugate equal to I gives ordinary comparison; a spanning isotropic
pair gives comparison with the dual. Conjugation uses the inverse convention. -/
theorem constituent_quasiequivalent_or_dual_conjugate
 (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
 (hpres : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
 (hi : IsIrreducible (invariantSubspace ρ H I hI).toRepresentation)
 (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0)
 (L : Subgroup G) (hLH : L ≤ H) (g : G)
 (hpair : I.map (ρ g⁻¹) = I ∨ I ⊔ I.map (ρ g⁻¹) = ⊤)
 (hL : L ≤ subspaceStabilizer ρ I)
 (hLg : L.map (MulAut.conj g).toMonoidHom ≤ subspaceStabilizer ρ I) :
 Quasiequivalent (invariantSubspace ρ L I hL).toRepresentation
   (invariantSubspace ρ (L.map (MulAut.conj g).toMonoidHom) I hLg).toRepresentation ∨
 Quasiequivalent (invariantSubspace ρ L I hL).toRepresentation
   (invariantSubspace ρ (L.map (MulAut.conj g).toMonoidHom) I hLg).toRepresentation.dual := by
  let R := invariantSubspace ρ H I hI
  let J := conjugateSubrepresentation ρ H R g
  let c := conjugateSubrepresentationEquiv ρ H R g
  rcases hpair with he | hspan
  · have hj : J = R := Subrepresentation.toSubmodule_injective he
    have c' := c
    change J.toRepresentation ≃ₗ conjugateRep R.toRepresentation g at c'
    rw [hj] at c'
    exact Or.inl ⟨(MulAut.conj g).subgroupMap L,c'.toLinearEquiv,
      fun l w => Representation.RepEquiv.isIntertwining c' ⟨l,hLH l.2⟩ w⟩
  · obtain ⟨e⟩ := isotropic_spanning_conjugate_dual ρ B hnd hpres H I hI hi hiso g hspan
    refine Or.inr ⟨(MulAut.conj g).subgroupMap L,
      e.toLinearEquiv.trans c.toLinearEquiv.symm.dualMap,?_⟩
    intro l w
    ext z
    have he := congrArg (fun f => f (c.symm z))
      (LinearMap.congr_fun (e.isIntertwining' ⟨l,hLH l.2⟩) w)
    have hc := Representation.RepEquiv.isIntertwining c.symm ⟨l⁻¹,hLH (L.inv_mem l.2)⟩ z
    change e ((invariantSubspace ρ L I hL).toRepresentation l w) (c.symm z) =
      e w (c.symm ((invariantSubspace ρ (L.map (MulAut.conj g).toMonoidHom) I hLg).toRepresentation
        (((MulAut.conj g).subgroupMap L) l)⁻¹ z))
    have hcg : (conjugateRep R.toRepresentation g) ⟨l⁻¹,hLH (L.inv_mem l.2)⟩ z =
        (invariantSubspace ρ (L.map (MulAut.conj g).toMonoidHom) I hLg).toRepresentation
          (((MulAut.conj g).subgroupMap L) l)⁻¹ z := by
      apply Subtype.ext
      change ρ (g * (l : G)⁻¹ * g⁻¹) (z : V) =
        ρ ((g * (l : G) * g⁻¹)⁻¹) (z : V)
      simp only [mul_inv_rev,inv_inv,mul_assoc]
    rw [hcg] at hc
    exact he.trans (congrArg (e w) hc.symm)
end CFSG.Quasithin.ChapterG.Section09
