module
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Sylow

/-!
# Cartan fixed points on left cosets

A surjective group homomorphism identifies the cosets of a subgroup with those
of its inverse image. The equivalence below keeps the representative formula
and intertwines the left actions. Thus a two-fixed-point calculation on a
natural transitive action descends to stabilizer cosets and lifts through a
normal quotient. The supplied-complement contract also transports through
isomorphisms and Sylow conjugacy.

These are elementary action lemmas used for the rank-one matrix groups; the
matrix fixed-point calculations are supplied by their respective model modules.
-/

@[expose] public section
open scoped Pointwise
namespace Theory.CartanPanel
variable {G H X : Type*} [Group G] [Group H]

/-- Map left cosets through a surjective homomorphism with the stated inverse image. -/
def cosetMap (f : G →* H) (B : Subgroup G) (C : Subgroup H)
    (hBC : C.comap f = B) : G ⧸ B → H ⧸ C :=
  Quotient.map' f (by
    intro x y h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    change x⁻¹ * y ∈ C.comap f
    rwa [hBC])

@[simp] theorem cosetMap_mk (f : G →* H) (B : Subgroup G) (C : Subgroup H)
    (hBC : C.comap f = B) (g : G) :
    cosetMap f B C hBC (QuotientGroup.mk g) = QuotientGroup.mk (f g) := rfl

theorem cosetMap_injective (f : G →* H) (B : Subgroup G) (C : Subgroup H)
    (hBC : C.comap f = B) : Function.Injective (cosetMap f B C hBC) := by
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      intro h
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      have h' : (f x)⁻¹ * f y ∈ C := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
      rw [← hBC]
      simpa only [Subgroup.mem_comap, map_mul, map_inv] using h'

noncomputable def cosetEquiv (f : G →* H) (hf : Function.Surjective f)
    (B : Subgroup G) (C : Subgroup H) (hBC : C.comap f = B) : G ⧸ B ≃ H ⧸ C :=
  Equiv.ofBijective (cosetMap f B C hBC) ⟨cosetMap_injective f B C hBC, by
    intro y
    induction y using Quotient.inductionOn with | h y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨QuotientGroup.mk x, rfl⟩⟩

@[simp] theorem cosetEquiv_mk (f : G →* H) (hf : Function.Surjective f)
    (B : Subgroup G) (C : Subgroup H) (hBC : C.comap f = B) (g : G) :
    cosetEquiv f hf B C hBC (QuotientGroup.mk g) = QuotientGroup.mk (f g) := rfl

theorem cosetEquiv_smul (f : G →* H) (hf : Function.Surjective f)
    (B : Subgroup G) (C : Subgroup H) (hBC : C.comap f = B)
    (g : G) (x : G ⧸ B) :
    cosetEquiv f hf B C hBC (g • x) = f g • cosetEquiv f hf B C hBC x := by
  induction x using Quotient.inductionOn with | h x =>
    change QuotientGroup.mk (f (g * x)) = QuotientGroup.mk (f g * f x)
    rw [map_mul]

/-- Pull a sharp fixed pair back along the literal coset map. -/
theorem two_fixed_pullback (f : G →* H) (hf : Function.Surjective f)
    (B : Subgroup G) (C : Subgroup H) (hBC : C.comap f = B) (D : Subgroup G)
    (h : ∃ d ∈ D.map f, ∃ β : H ⧸ C, β ≠ QuotientGroup.mk 1 ∧
      ∀ ω : H ⧸ C, d • ω = ω ↔ ω = QuotientGroup.mk 1 ∨ ω = β) :
    ∃ d ∈ D, ∃ β : G ⧸ B, β ≠ QuotientGroup.mk 1 ∧
      ∀ ω : G ⧸ B, d • ω = ω ↔ ω = QuotientGroup.mk 1 ∨ ω = β := by
  obtain ⟨_, ⟨d, hd, rfl⟩, β, hβ, hfix⟩ := h
  let e := cosetEquiv f hf B C hBC
  have hone : e (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by simp [e]
  refine ⟨d, hd, e.symm β, ?_, ?_⟩
  · intro he
    apply hβ
    rw [← e.apply_symm_apply β, he, hone]
  · intro ω
    rw [← e.injective.eq_iff, cosetEquiv_smul, hfix]
    constructor
    · rintro (hω | hω)
      · exact Or.inl (e.injective (hω.trans hone.symm))
      · exact Or.inr (e.eq_symm_apply.mpr hω)
    · rintro (rfl | rfl)
      · exact Or.inl hone
      · exact Or.inr (e.apply_symm_apply β)

/-- A subgroup contains an element fixing exactly the base coset and one other coset. -/
def HasTwoFixedCosets (B D : Subgroup G) : Prop :=
  ∃ d ∈ D, ∃ β : G ⧸ B, β ≠ QuotientGroup.mk 1 ∧
    ∀ ω : G ⧸ B, d • ω = ω ↔ ω = QuotientGroup.mk 1 ∨ ω = β

/-- The fixed-pair property for every supplied odd complement in a Sylow normalizer. -/
def SylowHasTwoFixedCosets (T : Sylow 2 G) : Prop :=
  ∀ D : Subgroup G, D ≤ Subgroup.normalizer (T : Set G) →
    Nat.Coprime 2 (Nat.card D) → Disjoint (T : Subgroup G) D →
    (T : Subgroup G) ⊔ D = Subgroup.normalizer (T : Set G) →
      HasTwoFixedCosets (Subgroup.normalizer (T : Set G)) D

/-- Transport the whole supplied-complement contract through an actual group isomorphism. -/
theorem sylow_transport (e : G ≃* H) (P : Sylow 2 G) (T : Sylow 2 H)
    (hT : (P : Subgroup G).map e.toMonoidHom = (T : Subgroup H))
    (h : SylowHasTwoFixedCosets P) : SylowHasTwoFixedCosets T := by
  have hN : (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
      Subgroup.normalizer (T : Set H) := by
    simpa only [Sylow.coe_coe, hT] using
      Subgroup.map_equiv_normalizer_eq (P : Subgroup G) e
  have hP : (T : Subgroup H).map e.symm.toMonoidHom = (P : Subgroup G) :=
    (Subgroup.map_symm_eq_iff_map_eq _).mpr hT
  have hN' : (Subgroup.normalizer (T : Set H)).map e.symm.toMonoidHom =
      Subgroup.normalizer (P : Set G) := (Subgroup.map_symm_eq_iff_map_eq _).mpr hN
  intro D hD hodd hdis hsup
  apply two_fixed_pullback e.symm.toMonoidHom e.symm.surjective
    (Subgroup.normalizer (T : Set H)) (Subgroup.normalizer (P : Set G))
    (by rwa [Subgroup.comap_equiv_eq_map_symm']) D
  apply h (D.map e.symm.toMonoidHom)
  · rw [← hN']
    exact Subgroup.map_mono hD
  · rwa [← Nat.card_congr (D.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).toEquiv]
  · rw [← hP]
    exact Subgroup.disjoint_map e.symm.injective hdis
  · rw [← hP, ← Subgroup.map_sup, hsup, hN']

/-- A standard Sylow calculation supplies the assertion for every Sylow. -/
theorem all_sylows [Finite G] (P : Sylow 2 G)
    (h : SylowHasTwoFixedCosets P) (T : Sylow 2 G) : SylowHasTwoFixedCosets T := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
  apply sylow_transport (MulAut.conj g) P T _ h
  exact congrArg Sylow.toSubgroup hg

variable [MulAction G X]
/-- Use the actual orbit map to pass from a natural action to left cosets. -/
theorem two_fixed_cosets (B D : Subgroup G) (α : X)
    (hB : B = MulAction.stabilizer G α)
    (htrans : ∀ x : X, ∃ g : G, g • α = x)
    (h : ∃ d ∈ D, ∃ β : X, β ≠ α ∧
      ∀ ω : X, d • ω = ω ↔ ω = α ∨ ω = β) :
    ∃ d ∈ D, ∃ β : G ⧸ B, β ≠ QuotientGroup.mk 1 ∧
      ∀ ω : G ⧸ B, d • ω = ω ↔ ω = QuotientGroup.mk 1 ∨ ω = β := by
  subst B
  obtain ⟨d, hd, β, hβ, hfix⟩ := h
  obtain ⟨b, hb⟩ := htrans β
  let e := MulAction.ofQuotientStabilizer G α
  have hi := MulAction.injective_ofQuotientStabilizer G α
  have hone : e (QuotientGroup.mk 1) = α := one_smul G α
  have hbase : e (QuotientGroup.mk b) = β := hb
  refine ⟨d, hd, QuotientGroup.mk b, ?_, ?_⟩
  · intro he
    exact hβ (hbase.symm.trans ((congrArg e he).trans hone))
  · intro ω
    rw [← hi.eq_iff, MulAction.ofQuotientStabilizer_smul, hfix]
    exact or_congr
      ⟨fun h => hi (h.trans hone.symm), fun h => (congrArg e h).trans hone⟩
      ⟨fun h => hi (h.trans hbase.symm), fun h => (congrArg e h).trans hbase⟩
end Theory.CartanPanel
