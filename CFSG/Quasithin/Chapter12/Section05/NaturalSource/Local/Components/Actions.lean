module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Quotients
public import Theory.Representation.BinaryNaturalAutomorphisms

/-!
# Full natural actions of the exterior local residuals

The original quotient map and wedge marking identify the literal conjugation
of L₃ on V₃ and L₄ on V₄ with the natural binary linear actions. The first
uses inverse transpose on its SL₃ actor, as required by complementary wedges.
Surjectivity then factors every element of Gᵢ as an element of Lᵢ times an
element centralizing Vᵢ. These ambient factorizations feed the containing
component rigidity argument; no component equality is assumed here.

Source: Aschbacher--Smith, 12.5.2(2--3), 12.5.3 and the first reduction
of 12.5.4, printed pp.817--819.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)
open Representation.SL5ExteriorSquare

def subspaceCoordinates (W : Submodule (ZMod 2) Representation.SL5ExteriorSquare.V) :
    a.subspace W ≃* Multiplicative W where
  toFun v := Multiplicative.ofAdd
    ⟨(a.coordinates ⟨v, a.subspace_le W v.property⟩).toAdd,
      (a.mem_subspace W _).mp v.property⟩
  invFun w := ⟨(a.coordinates.symm (Multiplicative.ofAdd w.toAdd.val) : G), by
    apply (a.mem_subspace W _).mpr
    rw [MulEquiv.apply_symm_apply]
    exact w.toAdd.property⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg (fun x : V => (x : G))
      (a.coordinates.symm_apply_apply ⟨v, a.subspace_le W v.property⟩)
  right_inv w := by
    change _ = Multiplicative.ofAdd _
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (a.coordinates.apply_symm_apply _)
  map_mul' v w := by
    change _ = Multiplicative.ofAdd _
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    change (a.coordinates (⟨v, a.subspace_le W v.property⟩ *
      ⟨w, a.subspace_le W w.property⟩)).toAdd =
      (a.coordinates ⟨v, a.subspace_le W v.property⟩).toAdd +
      (a.coordinates ⟨w, a.subspace_le W w.property⟩).toAdd
    exact congrArg Multiplicative.toAdd (a.coordinates.map_mul _ _)

def V₃Coordinates : a.Vi 3 ≃* Multiplicative (Fin 3 → ZMod 2) :=
  (a.subspaceCoordinates V₃).trans V₃Equiv.toAddEquiv.toMultiplicative

def V₄Coordinates : a.Vi 4 ≃* Multiplicative (Fin 4 → ZMod 2) :=
  (a.subspaceCoordinates V₄).trans V₄Equiv.toAddEquiv.toMultiplicative

/-- Conjugation by the original embedded local residual. -/
def LiAction (i : ℕ) : a.Li i →* MulAut (a.Vi i) :=
  (a.Vi i).normalizerMonoidHom.comp (inclusion (a.Li_le_Gi i))

/-- The V₃ marking includes the contragredient twist of the upper block. -/
def Li₃NaturalActor : a.Li 3 →* SL(3, ZMod 2) :=
  threeInverseTranspose.toMonoidHom.comp (a.LiLinearHom 3 (Or.inr (Or.inl rfl)))

theorem Li₃NaturalActor_surjective : Function.Surjective a.Li₃NaturalActor :=
  threeInverseTranspose.surjective.comp (a.LiLinearHom_surjective 3 (Or.inr (Or.inl rfl)))

omit [Finite G] in
theorem V₃Coordinates_action (l : a.Li 3) (v : a.Vi 3) :
    a.V₃Coordinates (a.LiAction 3 l v) =
      Representation.binaryNaturalAut 3 (a.Li₃NaturalActor l) (a.V₃Coordinates v) := by
  dsimp only [Vi] at v ⊢
  let r : parabolicResidual 3 := a.residualActor 3 (Or.inr (Or.inl rfl)) l
  let w : V₃ := (a.subspaceCoordinates V₃ v).toAdd
  have he : (a.subspaceCoordinates V₃ (a.LiAction 3 l v)).toAdd =
      V₃Action (inclusion (parabolicResidual_le 3) r) w := by
    apply Subtype.ext
    have h := a.equivariant ⟨l, a.Li_le_L 3 l.property⟩
      ⟨v, a.subspace_le V₃ v.property⟩
    change (a.coordinates ⟨(l : G) * (v : G) * (l : G)⁻¹, _⟩).toAdd = _
    rw [h]
    change _ = Representation.SL5TenDimensional.exteriorAction 2 r.val _
    have hr := a.residualActor_apply 3 (Or.inr (Or.inl rfl)) l
    change (r : Representation.SL5TenDimensional.Group) = _ at hr
    rw [hr]
    rfl
  have hactor : a.Li₃NaturalActor l =
      threeNaturalProjection (inclusion (parabolicResidual_le 3) r) :=
    parabolicThreeResidualNaturalEquiv_mk r
  change Multiplicative.ofAdd (V₃Equiv (a.subspaceCoordinates V₃ (a.LiAction 3 l v)).toAdd) = Multiplicative.ofAdd
    (Representation.specialLinearNatural 3 (a.Li₃NaturalActor l) (V₃Equiv w))
  rw [he, V₃Equiv_intertwines, hactor]

omit [Finite G] in
theorem V₄Coordinates_action (l : a.Li 4) (v : a.Vi 4) :
    a.V₄Coordinates (a.LiAction 4 l v) =
      Representation.binaryNaturalAut 4
        (a.LiLinearHom 4 (Or.inr (Or.inr (Or.inl rfl))) l) (a.V₄Coordinates v) := by
  dsimp only [Vi] at v ⊢
  let r : parabolicResidual 1 := a.residualActor 4 (Or.inr (Or.inr (Or.inl rfl))) l
  let w : V₄ := (a.subspaceCoordinates V₄ v).toAdd
  have he : (a.subspaceCoordinates V₄ (a.LiAction 4 l v)).toAdd =
      V₄ResidualQuotientAction (QuotientGroup.mk' _ r) w := by
    apply Subtype.ext
    rw [V₄ResidualQuotientAction_mk]
    have h := a.equivariant ⟨l, a.Li_le_L 4 l.property⟩
      ⟨v, a.subspace_le V₄ v.property⟩
    change (a.coordinates ⟨(l : G) * (v : G) * (l : G)⁻¹, _⟩).toAdd = _
    rw [h]
    have hr := a.residualActor_apply 4 (Or.inr (Or.inr (Or.inl rfl))) l
    change (r : Representation.SL5TenDimensional.Group) = _ at hr
    rw [hr]
    rfl
  change Multiplicative.ofAdd (V₄Equiv (a.subspaceCoordinates V₄ (a.LiAction 4 l v)).toAdd) = Multiplicative.ofAdd
    (Representation.specialLinearNatural 4
      (a.LiLinearHom 4 (Or.inr (Or.inr (Or.inl rfl))) l) (V₄Equiv w))
  rw [he]
  exact congrArg Multiplicative.ofAdd (V₄Equiv.apply_symm_apply _)

private theorem full_action_of_natural {B A : Type*} [Group B] [Group A]
    (n : ℕ) (e : A ≃* Multiplicative (Fin n → ZMod 2))
    (f : B →* MulAut A) (r : B →* SL(n, ZMod 2)) (hr : Function.Surjective r)
    (he : ∀ b v, e (f b v) = Representation.binaryNaturalAut n (r b) (e v)) :
    Function.Surjective f := by
  intro α
  obtain ⟨g, hg⟩ := (Representation.binaryNaturalAut_bijective n).2 (MulAut.congr e α)
  obtain ⟨b, hb⟩ := hr g
  refine ⟨b, MulEquiv.ext (fun v => e.injective ?_)⟩
  rw [he, hb, hg]
  change e (α (e.symm (e v))) = e (α v)
  rw [e.symm_apply_apply]

theorem Li₃Action_surjective : Function.Surjective (a.LiAction 3) :=
  full_action_of_natural 3 a.V₃Coordinates (a.LiAction 3) a.Li₃NaturalActor
    a.Li₃NaturalActor_surjective a.V₃Coordinates_action

theorem Li₄Action_surjective : Function.Surjective (a.LiAction 4) :=
  full_action_of_natural 4 a.V₄Coordinates (a.LiAction 4)
    (a.LiLinearHom 4 (Or.inr (Or.inr (Or.inl rfl))))
    (a.LiLinearHom_surjective 4 (Or.inr (Or.inr (Or.inl rfl)))) a.V₄Coordinates_action

/-- The two natural local actions are the full automorphism groups. -/
theorem LiAction_surjective (i : ℕ) (hi : i = 3 ∨ i = 4) :
    Function.Surjective (a.LiAction i) := by
  rcases hi with rfl | rfl
  · exact a.Li₃Action_surjective
  · exact a.Li₄Action_surjective

omit [Finite G] in
theorem localAut_nontrivial (i : ℕ) (hi : i = 3 ∨ i = 4) :
    Nontrivial (MulAut (a.Vi i)) := by
  rcases hi with rfl | rfl
  · let : IsSimpleGroup (SL(3, ZMod 2) ⧸ center SL(3, ZMod 2)) :=
      Atlas.psl_simple_high_rank 3 (by omega)
    let : Nontrivial SL(3, ZMod 2) :=
      (QuotientGroup.mk'_surjective (center SL(3, ZMod 2))).nontrivial
    exact Function.Injective.nontrivial
      ((MulAut.congr a.V₃Coordinates).symm.injective.comp
        (Representation.binaryNaturalAut_bijective 3).1)
  · let : IsSimpleGroup (SL(4, ZMod 2) ⧸ center SL(4, ZMod 2)) :=
      Atlas.psl_simple_high_rank 4 (by omega)
    let : Nontrivial SL(4, ZMod 2) :=
      (QuotientGroup.mk'_surjective (center SL(4, ZMod 2))).nontrivial
    exact Function.Injective.nontrivial
      ((MulAut.congr a.V₄Coordinates).symm.injective.comp
        (Representation.binaryNaturalAut_bijective 4).1)

/-- Actual element factorization in the full ambient normalizer. -/
theorem Gi_factorization (i : ℕ) (hi : i = 3 ∨ i = 4)
    (g : G) (hg : g ∈ a.Gi i) :
    ∃ l ∈ a.Li i, ∃ c ∈ centralizer (a.Vi i : Set G), l * c = g := by
  let gN : normalizer (a.Vi i : Set G) := ⟨g, hg⟩
  obtain ⟨l, hl⟩ := a.LiAction_surjective i hi ((a.Vi i).normalizerMonoidHom gN)
  let lN : normalizer (a.Vi i : Set G) := inclusion (a.Li_le_Gi i) l
  have hc : lN⁻¹ * gN ∈ (a.Vi i).normalizerMonoidHom.ker := by
    change (a.Vi i).normalizerMonoidHom (lN⁻¹ * gN) = 1
    rw [map_mul, map_inv]
    change (a.LiAction i l)⁻¹ * (a.Vi i).normalizerMonoidHom gN = 1
    rw [hl, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hc
  exact ⟨l, l.property, (l : G)⁻¹ * g, hc, mul_inv_cancel_left _ _⟩

/-- The normalizer reduction used in the natural-action part of 12.5.3--4. -/
theorem Gi_eq_Li_sup_centralizer (i : ℕ) (hi : i = 3 ∨ i = 4) :
    a.Gi i = a.Li i ⊔ centralizer (a.Vi i : Set G) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨l, hl, c, hc, rfl⟩ := a.Gi_factorization i hi g hg
    exact mul_mem (mem_sup_left hl) (mem_sup_right hc)
  · exact sup_le (a.Li_le_Gi i) (Subgroup.centralizer_le_normalizer _)

/-- The actual source reduction of the G₃ containment to its centralizer. -/
theorem G₃_le_M_iff : a.Gi 3 ≤ a.M ↔ centralizer (a.Vi 3 : Set G) ≤ a.M := by
  rw [a.Gi_eq_Li_sup_centralizer 3 (Or.inl rfl), sup_le_iff]
  exact and_iff_right ((a.Li_le_L 3).trans L.le_normalizer)

end ExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
