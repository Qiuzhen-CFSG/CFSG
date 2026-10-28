module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.Normalizers
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.FivePointQuotients

/-!
# The actual local S₅ quotients and flag intersection

The normalizer identifications transport the geometric five-point actions to
`local₁` and `local₂`. Their kernels are the respective relative root planes,
and the first isomorphism theorem gives equivalences from the existing
`LocalQuotient₁` and `LocalQuotient₂` types to S₅. Formulas on representatives
and on the embedded coordinate Sylow retain the actual geometric maps.
Together with the relative normality instances from `Basic`, these discharge
the concrete local-quotient input in the exceptional case of §5.3.7.

The common local subgroup is the full standard flag stabilizer. The first
parabolic acts transitively on its five incident lines, so orbit–stabilizer
gives intersection order 1920 / 5 = 384. In particular this is the whole
overlap used by the source amalgam, whose Sylow subgroup has order 128.
The independent odd-torus witness is exported by the umbrella module.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and §5.3.7, printed pp. 659--661 (PDF pp. 676--678). Constructing the source
amalgam isomorphism from the ambient hypotheses remains with its assembly
owner; no such recognition is asserted here.
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel.MatrixRealization

/-- The first normalizer identified with the point stabilizer, preserving ambient elements. -/
def localParabolicEquiv₁ : local₁ ≃* parabolic₁ :=
  MulEquiv.subgroupCongr local₁_eq_parabolic₁

/-- The second normalizer identified with the plane stabilizer, preserving ambient elements. -/
def localParabolicEquiv₂ : local₂ ≃* parabolic₂ :=
  MulEquiv.subgroupCongr local₂_eq_parabolic₂

@[simp] theorem localParabolicEquiv₁_val (g : local₁) :
    (localParabolicEquiv₁ g : FieldExtension) = g := rfl

@[simp] theorem localParabolicEquiv₂_val (g : local₂) :
    (localParabolicEquiv₂ g : FieldExtension) = g := rfl

/-- The first actual local group acts on the five lines through the standard point. -/
def localFivePointAction₁ : local₁ →* Equiv.Perm (Fin 5) :=
  fivePointAction₁.comp localParabolicEquiv₁.toMonoidHom

/-- The second actual local group acts on the five points on the standard plane. -/
def localFivePointAction₂ : local₂ →* Equiv.Perm (Fin 5) :=
  fivePointAction₂.comp localParabolicEquiv₂.toMonoidHom

theorem localFivePointAction₁_surjective : Function.Surjective localFivePointAction₁ :=
  fivePointAction₁_surjective.comp localParabolicEquiv₁.surjective

theorem localFivePointAction₂_surjective : Function.Surjective localFivePointAction₂ :=
  fivePointAction₂_surjective.comp localParabolicEquiv₂.surjective

theorem ker_localFivePointAction₁ :
    localFivePointAction₁.ker = rootPlane₁.subgroupOf local₁ := by
  ext g
  change localParabolicEquiv₁ g ∈ fivePointAction₁.ker ↔ _
  rw [ker_fivePointAction₁]
  rfl

theorem ker_localFivePointAction₂ :
    localFivePointAction₂.ker = rootPlane₂.subgroupOf local₂ := by
  ext g
  change localParabolicEquiv₂ g ∈ fivePointAction₂.ker ↔ _
  rw [ker_fivePointAction₂]
  rfl

/-- The quotient of the first normalizer by its relative root plane, identified with S₅. -/
def localQuotientEquiv₁ : LocalQuotient₁ ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq ker_localFivePointAction₁.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective localFivePointAction₁
      localFivePointAction₁_surjective)

/-- The quotient of the second normalizer by its relative root plane, identified with S₅. -/
def localQuotientEquiv₂ : LocalQuotient₂ ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq ker_localFivePointAction₂.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective localFivePointAction₂
      localFivePointAction₂_surjective)

@[simp] theorem localQuotientEquiv₁_mk (g : local₁) :
    localQuotientEquiv₁ (QuotientGroup.mk' (rootPlane₁.subgroupOf local₁) g) =
      localFivePointAction₁ g := rfl

@[simp] theorem localQuotientEquiv₂_mk (g : local₂) :
    localQuotientEquiv₂ (QuotientGroup.mk' (rootPlane₂.subgroupOf local₂) g) =
      localFivePointAction₂ g := rfl

@[simp] theorem localFivePointAction₁_apply (g : local₁) (l : Pencil₁) :
    (localFivePointAction₁ g) (pencilEquiv₁ l) =
      pencilEquiv₁ (pencilAction₁ (localParabolicEquiv₁ g) l) := by
  simp [localFivePointAction₁, fivePointAction₁]

@[simp] theorem localFivePointAction₂_apply (g : local₂) (p : Pencil₂) :
    (localFivePointAction₂ g) (pencilEquiv₂ p) =
      pencilEquiv₂ (pencilAction₂ (localParabolicEquiv₂ g) p) := by
  simp [localFivePointAction₂, fivePointAction₂]

/-- Compatibility with the given coordinate embedding into the first local group. -/
theorem localFivePointAction₁_localEmbedding (a : T) :
    localFivePointAction₁ (localEmbedding₁ a) =
      fivePointAction₁ ⟨embedding a, sylow_le_parabolic₁ ⟨a, rfl⟩⟩ := rfl

/-- Compatibility with the given coordinate embedding into the second local group. -/
theorem localFivePointAction₂_localEmbedding (a : T) :
    localFivePointAction₂ (localEmbedding₂ a) =
      fivePointAction₂ ⟨embedding a, sylow_le_parabolic₂ ⟨a, rfl⟩⟩ := rfl

/-- The first local is precisely the field extension of the projective point stabilizer. -/
theorem mem_local₁_iff_left (g : FieldExtension) :
    g ∈ local₁ ↔ g.left ∈ projectiveParabolic₁ := by
  rw [local₁_eq_parabolic₁, mem_parabolic₁_iff_left]

/-- The second local is precisely the field extension of the projective plane stabilizer. -/
theorem mem_local₂_iff_left (g : FieldExtension) :
    g ∈ local₂ ↔ g.left ∈ projectiveParabolic₂ := by
  rw [local₂_eq_parabolic₂, mem_parabolic₂_iff_left]

theorem card_local₁ : Nat.card local₁ = 1920 := by
  rw [local₁_eq_parabolic₁, card_parabolic₁]

theorem card_local₂ : Nat.card local₂ = 1920 := by
  rw [local₂_eq_parabolic₂, card_parabolic₂]

/-- The entire local overlap is the geometric flag stabilizer. -/
theorem localIntersection_eq_flagIntersection : local₁ ⊓ local₂ = flagIntersection := by
  rw [local₁_eq_parabolic₁, local₂_eq_parabolic₂]
  rfl

/-- There are five incident lines, so the flag stabilizer has order 384. -/
theorem card_flagIntersection : Nat.card flagIntersection = 384 := by
  classical
  let b : Pencil₁ := ⟨standardPlane, standardPoint_incident_standardPlane⟩
  let : MulAction parabolic₁ Pencil₁ := MulAction.compHom _ pencilAction₁
  have ho : MulAction.orbit parabolic₁ b = Set.univ := by
    apply Set.eq_univ_of_forall
    intro l
    obtain ⟨g, hg⟩ := (fivePointAction₁_surjective_iff.mp fivePointAction₁_surjective)
      (Equiv.swap b l)
    exact ⟨g, by change pencilAction₁ g b = l; rw [hg, Equiv.swap_apply_left]⟩
  have hc : Nat.card (MulAction.orbit parabolic₁ b) = Nat.card Pencil₁ := by
    rw [ho]
    exact Nat.card_congr (Equiv.Set.univ _)
  have hs : MulAction.stabilizer parabolic₁ b = flagIntersection.subgroupOf parabolic₁ := by
    ext g
    change pencilAction₁ g b = b ↔ (g : FieldExtension) ∈ flagIntersection
    rw [mem_flagIntersection]
    constructor
    · intro h
      exact ⟨g.property, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup parabolic₁ b)
  rw [Nat.card_prod, hc, hs, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (show flagIntersection ≤ parabolic₁ from inf_le_left)).toEquiv,
    card_pencil₁, card_parabolic₁] at h
  omega

theorem card_localIntersection : Nat.card (local₁ ⊓ local₂ : Subgroup FieldExtension) = 384 := by
  rw [localIntersection_eq_flagIntersection, card_flagIntersection]

end Matrix.PSL3Four.SylowModel.MatrixRealization
