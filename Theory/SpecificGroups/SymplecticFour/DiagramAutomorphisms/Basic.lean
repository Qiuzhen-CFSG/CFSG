module

public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Diagram preservation and faithful symplectic extensions

An automorphism preserves a parabolic type when it maps the actual standard
parabolic to a conjugate of itself. Diagram preservation requires this for
both the point and plane types. Inner and entrywise field automorphisms have
this property. No classification of all such automorphisms is assumed here.

Conjugation in a normal overgroup is transported through a specified
isomorphism from the matrix group onto the normal subgroup. Its kernel is
controlled by the ambient centralizer; when that centralizer is trivial and
every induced automorphism is inner, the overgroup equals the normal subgroup.
The assertion that binary diagram-preserving automorphisms are inner remains
a separate model theorem.

Source: Aschbacher--Smith, F.1.12, printed pp.263--264 of the combined
manuscript of 1 March 2004, `refs/quasithin.pdf`.
-/

@[expose] public section

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour
namespace DiagramAutomorphisms
variable {F : Type*} [Field F]

/-- Preservation of the conjugacy class of an actual parabolic subgroup. -/
def PreservesParabolicClass (a : MulAut (Sp F)) (P : Subgroup (Sp F)) : Prop :=
  ∃ g : Sp F, P.map a.toMonoidHom = P.map (MulAut.conj g).toMonoidHom

/-- Each of the two parabolic types is preserved, without interchanging them. -/
def PreservesDiagram (a : MulAut (Sp F)) : Prop :=
  PreservesParabolicClass a pointParabolic ∧ PreservesParabolicClass a planeParabolic

theorem inner_preservesDiagram (g : Sp F) : PreservesDiagram (MulAut.conj g) :=
  ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩

/-- Apply a field automorphism to every entry of a symplectic matrix. -/
def fieldAutomorphism (σ : F ≃+* F) : MulAut (Sp F) := Binary.fieldEquivSp σ

@[simp] theorem field_map_pointParabolic (σ : F ≃+* F) :
    pointParabolic.map (fieldAutomorphism σ).toMonoidHom = pointParabolic :=
  Binary.map_pointParabolic σ

@[simp] theorem field_map_planeParabolic (σ : F ≃+* F) :
    planeParabolic.map (fieldAutomorphism σ).toMonoidHom = planeParabolic :=
  Binary.map_planeParabolic σ

theorem field_preservesDiagram (σ : F ≃+* F) : PreservesDiagram (fieldAutomorphism σ) := by
  constructor
  · refine ⟨1, ?_⟩
    rw [map_one]
    change pointParabolic.map (fieldAutomorphism σ).toMonoidHom =
      pointParabolic.map (MonoidHom.id (Sp F))
    simpa [fieldAutomorphism] using Binary.map_pointParabolic σ
  · refine ⟨1, ?_⟩
    rw [map_one]
    change planeParabolic.map (fieldAutomorphism σ).toMonoidHom =
      planeParabolic.map (MonoidHom.id (Sp F))
    simpa [fieldAutomorphism] using Binary.map_planeParabolic σ

/-- An explicit inner correction fixes the chosen representative of its parabolic class. -/
theorem correct_parabolic (a : MulAut (Sp F)) (P : Subgroup (Sp F)) (g : Sp F)
    (h : P.map a.toMonoidHom = P.map (MulAut.conj g).toMonoidHom) :
    P.map ((MulAut.conj g⁻¹) * a).toMonoidHom = P := by
  calc
    _ = (P.map a.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    _ = (P.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom := by rw [h]
    _ = P := by
      rw [Subgroup.map_map]
      have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id (Sp F) := by
        ext x : 1
        simp [mul_assoc]
      rw [hi, Subgroup.map_id]

/-- Restrict an automorphism along the literal equality of its subgroup image. -/
def restrict (a : MulAut (Sp F)) (L : Subgroup (Sp F))
    (h : L.map a.toMonoidHom = L) : MulAut L :=
  (a.subgroupMap L).trans (MulEquiv.subgroupCongr h)

@[simp] theorem restrict_apply (a : MulAut (Sp F)) (L : Subgroup (Sp F))
    (h : L.map a.toMonoidHom = L) (l : L) : (restrict a L h l).val = a l.val := rfl

/-- Conjugation on a normal subgroup, expressed in a specified model. -/
def extensionAction {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (e : Sp F ≃* N) : G →* MulAut (Sp F) :=
  (MulAut.congr e.symm).toMonoidHom.comp
    (N.normalizerMonoidHom.comp
      ((MonoidHom.id G).codRestrict (Subgroup.normalizer (N : Set G))
        (fun g => Subgroup.normalizer_eq_top (H := N) ▸ Subgroup.mem_top g)))

@[simp] theorem extensionAction_apply {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N) (g : G) (x : Sp F) :
    (e (extensionAction N e g x)).val = g * (e x).val * g⁻¹ := by
  change (e (e.symm _)).val = _
  simp only [e.apply_symm_apply]
  rfl

/-- Faithfulness follows from the stipulated trivial ambient centralizer. -/
theorem extensionAction_injective {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (extensionAction N e) := by
  apply (extensionAction N e).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have ha : extensionAction N e g = 1 := hg
  have hc : g ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    have he := extensionAction_apply N e g y
    rw [ha] at he
    change (e y).val = g * (e y).val * g⁻¹ at he
    have hv : (e y).val = x := congrArg Subtype.val hy
    rw [hv] at he
    exact eq_mul_inv_iff_mul_eq.mp he
  simpa only [hC, Subgroup.mem_bot] using hc

/-- If all induced automorphisms are inner, a faithful normal extension collapses.
The model-specific assertion that diagram preservation implies innerness is
an additional theorem, not part of this elementary reduction. -/
theorem extension_eq_top_of_inner {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N)
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (hinner : ∀ g : G, ∃ x : Sp F, extensionAction N e g = MulAut.conj x) :
    N = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨x, hx⟩ := hinner g
  have he : extensionAction N e (e x).val = MulAut.conj x := by
    apply MulEquiv.ext
    intro y
    apply e.injective
    apply Subtype.ext
    rw [extensionAction_apply]
    simp
  have hg : g = (e x).val := extensionAction_injective N e hC (hx.trans he.symm)
  exact hg ▸ (e x).property
end DiagramAutomorphisms
end Theory.SpecificGroups.SymplecticFour
