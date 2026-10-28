module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Algebra
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs

/-!
# The original plane normalizer in the symplectic terminal argument

Uniqueness of the noncentral C-component implies its invariance under the
whole plane normalizer. This uses relative C-component membership and
conjugates the noncentrality assertion, rather than using the legacy
11.1.3 label. Generation by commutators then transports to the original
conjugate of V.

The elementary rechoice lemma preserves Vᵍ while replacing g by an element
normalizing V₂. Its input is the geometric statement that the intersection
plane is an Lᵍ-conjugate of V₂ᵍ; it does not assume the desired normalizer
membership.
Source: Aschbacher--Smith 11.1.3 and 11.5.7, printed pp.765,783--784.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G]

private theorem component_conjugate {H J : Subgroup G}
    (hc : Source.ComponentIn H J) {g : G} (hg : g ∈ H) :
    Source.ComponentIn H (J.map (MulAut.conj g).toMonoidHom) := by
  have he : (J.subgroupOf H).map (MulAut.conj (⟨g,hg⟩ : H)).toMonoidHom =
      (J.map (MulAut.conj g).toMonoidHom).subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,rfl⟩
    · rintro ⟨y,hy,hxy⟩
      exact ⟨⟨y,hc.1 hy⟩,hy,Subtype.ext hxy⟩
  refine ⟨?_, he ▸ hc.2.map_equiv (MulAut.conj (⟨g,hg⟩ : H))⟩
  rintro _ ⟨x,hx,rfl⟩
  exact H.mul_mem (H.mul_mem hg (hc.1 hx)) (H.inv_mem hg)

/-- The genuine uniqueness assertion gives normalization of the noncentral
component by N_G(P); P need not be normal in the ambient group. -/
theorem normalizes_unique_noncentral (P J : Subgroup G)
    (hu : Source.UniqueNoncentralComponent (normalizer (P : Set G)) P J) :
    normalizer (P : Set G) ≤ normalizer (J : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply hu.2
  refine ⟨component_conjugate hu.1.1 hg, ?_⟩
  intro hc
  apply hu.1.2
  have hb : ⁅J.map (MulAut.conj g).toMonoidHom,
      P.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    have hp : P.map (MulAut.conj g).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp hg
    rw [hp]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  rw [← map_commutator] at hb
  exact commutator_eq_bot_iff_le_centralizer.mp
    ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hb)

private theorem conjugate_mul (A : Subgroup G) (g l : G) :
    A.map (MulAut.conj (g*l)).toMonoidHom =
      (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev, mul_assoc]

/-- Rechoose the transporter, keeping its seed conjugate literally unchanged.
The equation is the pulled-back form of P ∈ (Pᵍ)^(Lᵍ). -/
theorem adjust_to_plane_normalizer (L V P : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (g : G)
    (horbit : ∃ l ∈ L,
      (P.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom = P) :
    ∃ n ∈ normalizer (P : Set G),
      V.map (MulAut.conj n).toMonoidHom = V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨l,hl,hP⟩ := horbit
  refine ⟨g*l, mem_normalizer_iff_map_conj_eq.mpr ?_, ?_⟩
  · exact (conjugate_mul P g l).trans hP
  · have hv : V.map (MulAut.conj l).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (hLV hl)
    rw [conjugate_mul, hv]

/-- Perfect movement by the actual L₂ survives the plane-normalizer rechoice. -/
theorem conjugate_moved_by_unique_component (P J V : Subgroup G)
    (hu : Source.UniqueNoncentralComponent (normalizer (P : Set G)) P J)
    (hmoved : ⁅V,J⁆ = V) {g : G} (hg : g ∈ normalizer (P : Set G)) :
    ⁅V.map (MulAut.conj g).toMonoidHom,J⁆ = V.map (MulAut.conj g).toMonoidHom := by
  have he := congrArg (map (MulAut.conj g).toMonoidHom) hmoved
  have hj : J.map (MulAut.conj g).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (normalizes_unique_noncentral P J hu hg)
  rwa [map_commutator, hj] at he

variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Application to the literal V₂ and L₂ of the chosen source geometry. -/
theorem plane_rechoice_moved
    (hu : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved : ⁅V,E.L₂⁆ = V) (g : G)
    (horbit : ∃ l ∈ L,
      (E.V₂.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom = E.V₂) :
    ∃ n ∈ normalizer (E.V₂ : Set G),
      V.map (MulAut.conj n).toMonoidHom = V.map (MulAut.conj g).toMonoidHom ∧
      ⁅V.map (MulAut.conj n).toMonoidHom,E.L₂⁆ = V.map (MulAut.conj n).toMonoidHom := by
  obtain ⟨n,hn,he⟩ := adjust_to_plane_normalizer L V E.V₂ D.normalizes g horbit
  exact ⟨n,hn,he,conjugate_moved_by_unique_component E.V₂ E.L₂ V hu hmoved hn⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
