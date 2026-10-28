module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Action

/-!
# Assembly of the noncommuting symplectic terminal branch

The two geometric inputs below concern the original natural-action planes:
placing the fixed/displacement plane using L₁, and identifying that same
plane in the conjugate module. From these inputs we construct the escaping
conjugate, prove V₂=V∩Vᵍ, rechoose its transporter in N_G(V₂), and use the
genuine unique noncentral component to transport V=[V,L₂]. The contradiction
then uses the original R₂ displacement in Aut(V).

Construction of CrossingPlanes and RadicalDisplacement from the supplied
marked symplectic module remains explicit. This is a conditional assembly,
not a claim that those geometric calculations have already been proved.
Source: Aschbacher--Smith 11.5.7, printed pp.783--784.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The two natural-action plane calculations, before any normalizer rechoice
or component argument. In `reverse_plane`, the equation is the pulled-back
form of V₂ being an Lᵍ-conjugate of V₂ᵍ. -/
structure CrossingPlanes : Prop where
  align : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ E.R₁ →
    ⁅V,A⁆ ≤ V ⊓ A → ¬ A ≤ centralizer (E.V₃ : Set G) →
    ∃ l ∈ E.L₁,
      V ⊓ centralizer (A.map (MulAut.conj l).toMonoidHom : Set G) ≤ E.V₂ ∧
      E.V₂ ≤ ⁅V,A.map (MulAut.conj l).toMonoidHom⁆
  reverse_plane : ∀ g ∈ E.G₁,
    V ⊓ V.map (MulAut.conj g).toMonoidHom = E.V₂ →
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₂ →
    ∃ l ∈ L,
      (E.V₂.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom = E.V₂

/-- Choose and place an escaping seed, then prove the source's exact
intersection and displacement equalities using mutual normalization. -/
theorem exists_crossing_plane (m : MarkedFlag E) (p : CrossingPlanes E)
    (hcore : E.W ≤ E.G₁.pCoreIn 2) (hc : ⁅V,E.U⁆ ≠ ⊥) :
    ∃ g ∈ E.G₁, V ⊓ V.map (MulAut.conj g).toMonoidHom = E.V₂ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₂ := by
  obtain ⟨g,hg,hm⟩ := exists_conjugate_moving_threeSpace E hc
  have hn := closure_normalizes_seed E m hcore
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ E.W := by
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨g,hg,v,hv,rfl⟩
  let := D.elementary
  have helem : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  obtain ⟨l,hl,hf,hd⟩ := p.align _ helem (hA.trans (closure_le_R₁ E m hcore))
    (commutator_le_intersection E hn hg) hm
  have he : V.map (MulAut.conj (l*g)).toMonoidHom =
      (V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev, mul_assoc]
  have hlg : l*g ∈ E.G₁ := E.G₁.mul_mem
    (((residualIn_le _).trans inf_le_right) hl) hg
  refine ⟨l*g,hlg,intersection_eq_plane E hn hlg ?_ ?_⟩
  · rwa [he]
  · rwa [he]

/-- The noncommuting branch uses the original V₂ normalizer and L₂,
retaining the original R₁ action bound through the transporter rechoice. -/
theorem noncommuting_impossible (m : MarkedFlag E)
    (p : CrossingPlanes E) (r : RadicalDisplacement E)
    (hcore : E.W ≤ E.G₁.pCoreIn 2)
    (hu : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved : ⁅V,E.L₂⁆ = V) (hc : ⁅V,E.U⁆ ≠ ⊥) : False := by
  obtain ⟨g,hg,hi,hd⟩ := exists_crossing_plane E m p hcore hc
  obtain ⟨n,_,he,hn⟩ := plane_rechoice_moved E hu hmoved g
    (p.reverse_plane g hg hi hd)
  rw [he] at hn
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ E.W := by
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨g,hg,v,hv,rfl⟩
  have hne : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
    intro hz
    have hb := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hz)
    have hp : E.V₂ ≠ ⊥ := by
      rw [m.plane_preimage]
      exact m.flag.V_ne_bot 1
    exact hp (hd.symm.trans hb)
  exact false_of_moved_seed E m r _ (hA.trans (closure_le_R₁ E m hcore))
    (hA.trans (closure_normalizes_seed E m hcore)) hn hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
