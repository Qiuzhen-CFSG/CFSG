module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Subtori
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.ChevalleyAction
/-!
# Characters of fixed points on centralizer orbits

A torus-fixed projective point gives an actual regular weight on its
representing line. If two such points lie in the same orbit of a subtorus
centralizer, their weights agree on that subtorus: the orbit transporter
commutes with its action. Hence the ratio character is trivial there.
For a codimension-one subtorus and distinct weights, the connected kernel
of the ratio is exactly that original subtorus.

This supplies the literal character-kernel step for the two fixed points of
the rank-one centralizer orbit in Borel, *Linear Algebraic Groups*, IV,
13.11(3) and 13.12, `refs/KGroup/Bor1/Chapter4.tex`.
-/

public section
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type*} [AddCommGroup V] [Module k V]

theorem fixed_projective_point_weight
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (p : ℙ k V)
    (hfix : ∀ t : Variety.Point T.carrierVariety,
      Projectivization.map (ρ.action (T.includePoint t)).1
        (ρ.action (T.includePoint t)).toLinearEquiv.injective p = p) :
    ∃! χ : TorusWeight T, IsWeightVector ρ T p.rep χ := by
  apply invariantLine_torusWeight_existsUnique_public ρ hρ T p.rep
  refine ⟨p.rep_nonzero, ?_⟩
  intro g hg
  let t := T.pointEquiv.symm ⟨g,hg⟩
  have he := hfix t
  have ht : T.includePoint t = g := rfl
  rw [ht, ← Projectivization.mk_rep p] at he
  change Projectivization.mk k ((ρ.action g).1 p.rep) _ = Projectivization.mk k p.rep _ at he
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp he
  exact ⟨a,ha.symm⟩

omit [IsAlgClosed k] in
theorem weight_values_eq_on_central_subtorus_orbit
    (ρ : RationalRepresentation G V) (T S : ClosedSubgroup G)
    (v w : V) (χ ψ : TorusWeight T)
    (hv : IsWeightVector ρ T v χ) (hw : IsWeightVector ρ T w ψ)
    (g : Variety.Point G) (hg : g ∈ S.centralizer)
    (hp : Projectivization.mk k w hw.1 =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (Projectivization.mk k v hv.1)) :
    ∀ t : Variety.Point T.carrierVariety, T.includePoint t ∈ S →
      χ.pointCharacter t = ψ.pointCharacter t := by
  change Projectivization.mk k w _ = Projectivization.mk k ((ρ.action g).1 v) _ at hp
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp hp
  intro t ht
  have hcomm : T.includePoint t * g = g * T.includePoint t :=
    Subgroup.mem_centralizer_iff.mp hg _ ht
  have he : (ρ.action (T.includePoint t)).1 ((ρ.action g).1 v) =
      χ.pointCharacter t • (ρ.action g).1 v := by
    calc
      _ = (ρ.action (T.includePoint t * g)).1 v := by rw [map_mul]; rfl
      _ = (ρ.action (g * T.includePoint t)).1 v := by rw [hcomm]
      _ = (ρ.action g).1 ((ρ.action (T.includePoint t)).1 v) := by rw [map_mul]; rfl
      _ = _ := by rw [hv.2 t, map_smul]
  have hwχ : (ρ.action (T.includePoint t)).1 w = χ.pointCharacter t • w := by
    rw [← ha, map_smul, he, smul_comm]
  exact smul_left_injective k hw.1 (hwχ.symm.trans (hw.2 t))

omit [IsAlgClosed k] in
theorem ratio_character_trivial_on_central_subtorus_orbit
    (ρ : RationalRepresentation G V) (T S : ClosedSubgroup G)
    (v w : V) (χ ψ : TorusWeight T)
    (hv : IsWeightVector ρ T v χ) (hw : IsWeightVector ρ T w ψ)
    (g : Variety.Point G) (hg : g ∈ S.centralizer)
    (hp : Projectivization.mk k w hw.1 =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (Projectivization.mk k v hv.1)) :
    ∀ t : Variety.Point T.carrierVariety, T.inclusion.onPoints t ∈ S →
      (χ * ψ⁻¹).onPoints t = 1 := by
  intro t ht
  have he := weight_values_eq_on_central_subtorus_orbit ρ T S v w χ ψ hv hw g hg hp t ht
  have he' : χ.onPoints t = ψ.onPoints t := by
    apply (dPointEquiv 1).injective
    funext i
    fin_cases i
    exact Units.ext he
  change χ.onPoints t * (ψ.onPoints t)⁻¹ = 1
  rw [he', mul_inv_cancel]

/-- In the actual centralizer orbit, distinct endpoint weights recover the
source's literal codimension-one subtorus as the connected character kernel. -/
theorem orbit_weight_ratio_ambientConnectedKernel
    (ρ : RationalRepresentation G V) (T S : ClosedSubgroup G)
    (hT : IsSubtorus T) (hS : IsSubtorus S) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (v w : V) (χ ψ : TorusWeight T) (hne : χ ≠ ψ)
    (hv : IsWeightVector ρ T v χ) (hw : IsWeightVector ρ T w ψ)
    (g : Variety.Point G) (hg : g ∈ S.centralizer)
    (hp : Projectivization.mk k w hw.1 =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (Projectivization.mk k v hv.1)) :
    (χ * ψ⁻¹).ambientConnectedKernel T = S := by
  exact ambientConnectedKernel_eq_of_codimension_one T S hT hS hST hcodim
    (χ * ψ⁻¹) (fun he => hne (mul_inv_eq_one.mp he))
    (ratio_character_trivial_on_central_subtorus_orbit ρ T S v w χ ψ hv hw g hg hp)

end Theory.AlgebraicGroup.Bor1.SeparatingBorel
