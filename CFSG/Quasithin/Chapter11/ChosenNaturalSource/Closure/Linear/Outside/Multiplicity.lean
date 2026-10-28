module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.RadicalImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Solvable
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Sylow

/-!
# Multiplicity structure for the original selected outside subgroup

The original SL₃ marking and field-line point prove R₁≤W O₂(LT). The
marked two-copy natural module then constructs the compatible faithful GL₂
action. The actual quotient-centralizer identity makes R₁ Sylow in C, and
the source block splitting makes R₁ act trivially. Odd order and
commutativity of the multiplicity image follow.

This proves solvability of the original H and supplies the odd-prime
complement in O²(H), its Frattini intersection and its literal cyclic
action image of order dividing q+1. The new source entry points discharge
the radical-image, solvability and multiplicity-action premises of the
conditional APIs. The original geometry through 11.5.6, the block outputs
and the independent X₀ identities remain with the source assembly owner.
The final application feeds the constructed action to the actual outside-H
contradiction consumer, without changing H, the field or the quotient maps.

Source: Aschbacher--Smith, 11.5.7, printed pp.781--782, and B.6.8(2),
printed pp.113--114.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The actual multiplicity image, including its Sylow-kernel and odd-order proofs. -/
theorem multiplicity_structure (m : NaturalPair E)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hpoint : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWK : E.W = E.K.pCoreIn 2) (hWL : E.W ≤ L) (hLV : L.pCoreIn 2 = V)
    (himage : E.R₁ ≤ E.W ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    let hCG := C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG
    ∃ S : Sylow 2 (C E), (S : Subgroup (C E)) = E.R₁.subgroupOf (C E) ∧
      (S : Subgroup (C E)) ≤ actionCentralizer E (C E) hCG ∧
      Odd (Nat.card ((C E) ⧸ actionCentralizer E (C E) hCG)) ∧
      (∃ ι : ((C E) ⧸ actionCentralizer E (C E) hCG) →* GL (Fin 2) E.input.field.Carrier,
        Function.Injective ι) ∧ IsMulCommutative (quotientAction E (C E) hCG).range := by
  dsimp only
  have hTG := hH.1.1.2.trans hHG
  have hres := residual_le_Y E hH hHG hKL hpoint hselect
  let hCG := C_le_point_normalizer E hTG hHG hXG
  obtain ⟨S,hS⟩ := exists_radical_sylow E m hTG hKL hHG hXG hres
  have hker : (S : Subgroup (C E)) ≤ actionCentralizer E (C E) hCG := by
    rw [hS]
    exact radical_le_actionCentralizer E m hCG hWK hWL hLV himage hsplit
  have ho := action_quotient_odd_of_sylow_kernel E (C E) hCG S hker
  obtain ⟨ι,hι⟩ := m.exists_plane_embedding (C E) hCG
    (C_le_coreCentralizer E m hTG hKL hres)
  exact ⟨S,hS,hker,ho,⟨ι,hι⟩,image_commutative_of_odd_linear_action E (C E) hCG
    ((Representation.generalLinearNatural 2).comp ι)
    ((Representation.generalLinearNatural_injective 2).comp hι) ho⟩

/-- The constructed multiplicity action discharges the plane-embedding endpoint;
the independent source X₀ and moved-seed identities remain explicit. -/
theorem contradiction_of_natural_pair (m : NaturalPair E)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hpoint : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWK : E.W = E.K.pCoreIn 2) (hWL : E.W ≤ L) (hLV : L.pCoreIn 2 = V)
    (himage : E.R₁ ≤ E.W ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (X₀ : Subgroup G) (hX : X₀ ≤ X₁ E) (hmove : ⁅E.W,X₀⁆ = V) : False := by
  obtain ⟨S,_,hS,_,⟨ι,hι⟩,_⟩ := multiplicity_structure E m hH hHG hXG hKL
    hpoint hselect hWK hWL hLV himage hsplit
  exact contradiction_of_plane_embedding E hH hHG hXG S hS ι hι X₀ hX hmove

/-- Solvability is derived for the original H before applying the solvable
branch of B.6.8; it is not an additional source hypothesis. -/
theorem H_solvable_of_natural_pair (m : NaturalPair E)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hpoint : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWK : E.W = E.K.pCoreIn 2) (hWL : E.W ≤ L) (hLV : L.pCoreIn 2 = V)
    (himage : E.R₁ ≤ E.W ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hNT : normalizer (T : Set G) ≤ E.M) : Group.IsSolvable E.H := by
  obtain ⟨_,_,_,_,_,hab⟩ := multiplicity_structure E m hH hHG hXG hKL
    hpoint hselect hWK hWL hLV himage hsplit
  exact H_solvable_of_image_commutative E hH hHG hXG hNT hab

/-- The source SL₃ marking discharges the radical-image premise. The resulting
faithful multiplicity embedding retains its equation on the two natural copies,
and its odd order follows from the actual Sylow subgroup in the action kernel. -/
theorem multiplicity_structure_of_source
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (n : NaturalPair E)
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (LocalGeometry.Coordinates.sl3 m).binarySubspace P)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hcentral : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWK : E.W = E.K.pCoreIn 2) (hLV : L.pCoreIn 2 = V)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    let hCG := C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG
    ∃ S : Sylow 2 (C E), (S : Subgroup (C E)) = E.R₁.subgroupOf (C E) ∧
      (S : Subgroup (C E)) ≤ actionCentralizer E (C E) hCG ∧
      Odd (Nat.card ((C E) ⧸ actionCentralizer E (C E) hCG)) ∧
      (∃ ι : ((C E) ⧸ actionCentralizer E (C E) hCG) →* GL (Fin 2) E.input.field.Carrier,
        Function.Injective ι ∧ ∀ (a : C E) (c v : Fin 2 → E.input.field.Carrier),
          n.action (C E) hCG a (fun i => c i • v) =
            fun i => generalLinearNatural 2
              (ι (QuotientGroup.mk' (actionCentralizer E (C E) hCG) a)) c i • v) ∧
      IsMulCommutative (quotientAction E (C E) hCG).range := by
  dsimp only
  have hTG := hH.1.1.2.trans hHG
  have hWL : E.W ≤ L := by rw [hWK, hKL]; exact (pCoreIn_le 2 E.L₁).trans E.L₁_le
  have himage := RadicalImage.radical_le_closure_join_core E m n P hdim hpoint hTG hKL hWK
  obtain ⟨S, hS, hker, ho, _, hab⟩ := multiplicity_structure E n hH hHG hXG hKL
    hcentral hselect hWK hWL hLV himage hsplit
  obtain ⟨ι, hι, hcompat⟩ := n.exists_compatible_plane_embedding (C E)
    (C_le_point_normalizer E hTG hHG hXG)
    (C_le_coreCentralizer E n hTG hKL (residual_le_Y E hH hHG hKL hcentral hselect))
  exact ⟨S, hS, hker, ho, ⟨ι, hι, hcompat⟩, hab⟩

/-- Solvability of the original selected H, with the radical-image input
discharged by the actual source marking and field line. -/
theorem H_solvable_of_source_natural_pair
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (n : NaturalPair E)
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (LocalGeometry.Coordinates.sl3 m).binarySubspace P)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hcentral : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWK : E.W = E.K.pCoreIn 2) (hLV : L.pCoreIn 2 = V)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hNT : normalizer (T : Set G) ≤ E.M) : Group.IsSolvable E.H := by
  have hWL : E.W ≤ L := by rw [hWK, hKL]; exact (pCoreIn_le 2 E.L₁).trans E.L₁_le
  exact H_solvable_of_natural_pair E n hH hHG hXG hKL hcentral hselect hWK hWL hLV
    (RadicalImage.radical_le_closure_join_core E m n P hdim hpoint
      (hH.1.1.2.trans hHG) hKL hWK) hsplit hNT

/-- The original residual complement and its literal cyclic action image.
The only order input is the preceding 11.5.6(1) coprimality of Y; solvability,
residual placement, the compatible embedding and the odd abelian image are
all derived from the original selection and the authorized block outputs. -/
theorem residual_structure_of_source
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (n : NaturalPair E)
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (LocalGeometry.Coordinates.sl3 m).binarySubspace P)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hcentral : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWK : E.W = E.K.pCoreIn 2) (hLV : L.pCoreIn 2 = V)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hNT : normalizer (T : Set G) ≤ E.M)
    (hY : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1)) :
    let hCG := C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG
    ∃ (p : ℕ) (Q : Subgroup G), p.Prime ∧ Odd p ∧ IsPGroup p Q ∧
      Q ≤ outsideResidual E ∧ Q ≠ ⊥ ∧
      outsideResidual E = (outsideResidual E).pCoreIn 2 ⊔ Q ∧
      Disjoint ((outsideResidual E).pCoreIn 2) Q ∧
      Q ⊔ (T : Subgroup G) = E.H ∧
      Q ⊓ E.M = (frattini Q).map Q.subtype ∧
      Nat.Coprime p (2 ^ E.input.field.degree - 1) ∧
      IsCyclic ((Q.subgroupOf (C E)).map (quotientAction E (C E) hCG)) ∧
      Nat.card ((Q.subgroupOf (C E)).map (quotientAction E (C E) hCG)) ∣
        2 ^ E.input.field.degree + 1 ∧
      (Q.subgroupOf (C E)).map (quotientAction E (C E) hCG) ≤
        centralizer (((X₁ E).subgroupOf (C E)).map (quotientAction E (C E) hCG) :
          Set (MulAut (E.W ⧸ E.V₁.subgroupOf E.W))) := by
  have hs := H_solvable_of_source_natural_pair E m n P hdim hpoint hH hHG hXG hKL
    hcentral hselect hWK hLV hsplit hNT
  have hRY := residual_le_Y E hH hHG hKL hcentral hselect
  obtain ⟨_, _, _, ho, hemb, hab⟩ := multiplicity_structure_of_source E m n P hdim hpoint
    hH hHG hXG hKL hcentral hselect hWK hLV hsplit
  exact residual_structure E n hH hHG hXG hNT hs hRY hY hemb ⟨ho, hab⟩

/-- Apply the constructed source multiplicity action to the actual outside-H
consumer. Only the independent torus identities X₀≤X₁ and [W,X₀]=V remain
beyond the preceding geometry and block outputs; no image or kernel premise
is supplied by the caller. -/
theorem contradiction_of_source_natural_pair
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (n : NaturalPair E)
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (LocalGeometry.Coordinates.sl3 m).binarySubspace P)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁) (hKL : E.K = E.L₁)
    (hcentral : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hWK : E.W = E.K.pCoreIn 2) (hLV : L.pCoreIn 2 = V)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (X₀ : Subgroup G) (hX : X₀ ≤ X₁ E) (hmove : ⁅E.W,X₀⁆ = V) : False := by
  obtain ⟨S, _, hS, _, ⟨ι, hι, _⟩, _⟩ := multiplicity_structure_of_source E m n P hdim hpoint
    hH hHG hXG hKL hcentral hselect hWK hLV hsplit
  exact contradiction_of_plane_embedding E hH hHG hXG S hS ι hι X₀ hX hmove

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
