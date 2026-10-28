module

public import Theory.Representation.G2OrthogonalCover.SylowFlag.Marked
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Uniqueness of the derived-Sylow invariant line and plane

A nonzero invariant space for a two-group in characteristic two contains a
nonzero fixed vector. The marked fixed-line calculation therefore places N1
inside every invariant plane. Its one-dimensional quotient is fixed by the
same fixed-vector theorem, and the displacement calculation identifies the
plane with the original naturalPlane. This applies uniformly over every
finite characteristic-two field, including F₂.

Source: Aschbacher–Smith, I.2.3, printed p.413 / PDF p.424.
-/

@[expose] public section
noncomputable section

open Atlas.SplitOctonion Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover.SylowFlag
variable (F : Type*) [Field F] [CharP F 2]

private theorem pGroup_fixed_vector
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V]
    (hp : IsPGroup 2 G) (ρ : Representation F G V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  exact pGroup_fix_nonzero_vector (by rw [ringChar.eq F 2]; decide)
    (by simpa only [ringChar.eq F 2] using hp) ρ

private theorem pGroup_line_trivial
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hp : IsPGroup 2 G) (ρ : Representation F G V)
    (hdim : Module.finrank F V = 1) : ∀ g v, ρ g v = v := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F V)
  obtain ⟨x, hx, hfix⟩ := pGroup_fixed_vector F hp ρ
  intro g v
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim v
  rw [map_smul, hfix]

theorem U_isTwoGroup [Finite F] : IsPGroup 2 (U F) := by
  rw [← sylow_coe]
  exact (sylow F).isPGroup'

/-- The unique fixed line is contained in every nonzero invariant subspace. -/
theorem N1_le_of_invariant [Finite F] (W : Submodule F (Space F))
    (hW : ∀ g : U F, W ≤ W.comap (derivedAction F g.val)) (hne : W ≠ ⊥) :
    N1 F ≤ W := by
  let σ := Representation.subrepresentation ((derivedAction F).comp (U F).subtype) W hW
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨x, hx, hfix⟩ := pGroup_fixed_vector F (U_isTwoGroup F) σ
  have hxf : x.val ∈ N1 F := by
    rw [← natural_fixed]
    intro g
    exact congrArg Subtype.val (hfix g)
  have hx0 : x.val ≠ 0 := fun h => hx (Subtype.ext h)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one (N1_finrank F) hxf hx0]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr x.property

/-- Every invariant one-space is the marked first natural line. -/
theorem invariant_line_unique [Finite F] (W : Submodule F (Space F))
    (hW : ∀ g : U F, W ≤ W.comap (derivedAction F g.val))
    (hdim : Module.finrank F W = 1) : W = N1 F := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply N1_le_of_invariant F W hW
    intro h
    have hz : Module.finrank F W = 0 := by rw [h, finrank_bot]
    omega
  · rw [N1_finrank, hdim]

/-- Every invariant two-space is the actual long-root plane image. -/
theorem invariant_plane_unique [Finite F] (W : Submodule F (Space F))
    (hW : ∀ g : U F, W ≤ W.comap (derivedAction F g.val))
    (hdim : Module.finrank F W = 2) : W = naturalPlane F := by
  have hle : N1 F ≤ W := N1_le_of_invariant F W hW (by
    intro h
    have hz : Module.finrank F W = 0 := by rw [h, finrank_bot]
    omega)
  let σ := Representation.subrepresentation ((derivedAction F).comp (U F).subtype) W hW
  let L : Submodule F W := (N1 F).comap W.subtype
  have hL (g : U F) : L ≤ L.comap (σ g) := by
    intro x hx
    exact N1_invariant F g hx
  have hLdim : Module.finrank F L = 1 :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans (N1_finrank F)
  have hquot : Module.finrank F (W ⧸ L) = 1 := by
    have h := L.finrank_quotient_add_finrank
    rw [hLdim, hdim] at h
    omega
  have htriv := pGroup_line_trivial F (U_isTwoGroup F) (Representation.quotient σ L hL) hquot
  apply Submodule.eq_of_le_of_finrank_eq _ (hdim.trans (naturalPlane_finrank F).symm)
  intro x hx
  apply (displacement_mem_N1_iff F x).mp
  intro g
  have he := htriv g (L.mkQ ⟨x,hx⟩)
  change L.mkQ (σ g ⟨x,hx⟩) = L.mkQ ⟨x,hx⟩ at he
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at he
  exact he


end Atlas.G2.Natural.OrthogonalCover.SylowFlag
