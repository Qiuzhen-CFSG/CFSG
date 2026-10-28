module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.FixedSubfield

/-!
# Marked field centralizers in the full quadratic semilinear group

Projective descent identifies the centralizer of the pure field involution
with PGL₂ of its fixed field times the field-automorphism group of order two.
The product map retains the exact linear and field coordinates. Its restriction
computes the centralizer of B⟨σ⟩ for every fixed-field subgroup B; cyclic B of
order two gives the mixed rank-two actors. Triviality of the ambient two-core
then computes their literal tau intersection.

The fixed-field PGL₂ embeds in the ambient PSL₂ layer for every odd prime,
including three and five. `SmallField` consumes these marked maps to verify
an intrinsic E1 section. Selecting members of an arbitrary invariant family
and placing their local witnesses outside a proper overgroup remain with the
escape assembly.

Source: Aschbacher–Smith, A.2.3(2), E.1.2 and E.1.14(6),
printed pp.33, 209–210 and 214.
-/

public section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
variable {F : Type*} [Field F] [finF : Finite F]

/-- The marked inclusion of the fixed-field projective group. -/
@[expose] def subfieldEmbedding (σ : F ≃+* F) :
    PGL2 (FixedPoints.subfield (zpowers σ) F) →* PGammaL2 F :=
  SemidirectProduct.inl.comp
    (ProjGenLinGroup.map (FixedPoints.subfield (zpowers σ) F).subtype)

omit [Finite F] in
theorem subfieldEmbedding_injective (σ : F ≃+* F) :
    Function.Injective (subfieldEmbedding σ) :=
  SemidirectProduct.inl_injective.comp
    (pgl2_map_injective_of_injective _ (Subfield.subtype_injective _))

/-- Every element of the quadratic field factor fixes this embedded subgroup. -/
theorem all_fieldAut_fixed {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (σ : F ≃+* F) (hne : σ ≠ 1) (τ : F ≃+* F)
    (x : PGL2 (FixedPoints.subfield (zpowers σ) F)) :
    pgl2FieldAut F τ (ProjGenLinGroup.map
      (FixedPoints.subfield (zpowers σ) F).subtype x) =
    ProjGenLinGroup.map (FixedPoints.subfield (zpowers σ) F).subtype x := by
  rcases fieldAut_eq_one_or hp hF σ hne τ with h | h
  · rw [h, map_one, MulAut.one_apply]
  · rw [h]; exact fixed_image σ x

/-- In quadratic coordinates, centralizing σ means that the linear
coordinate is defined over the fixed field. -/
theorem mem_fieldCentralizer_iff {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1)
    (x : PGammaL2 F) :
    x ∈ centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) ↔
      x.left ∈ (ProjGenLinGroup.map
        (FixedPoints.subfield (zpowers σ) F).subtype).range := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply projective_descent σ
    have hl := congrArg SemidirectProduct.left h
    simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, map_one, mul_one, one_mul] using hl.symm
  · rintro ⟨y, hy⟩
    apply SemidirectProduct.ext
    · simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, map_one, mul_one, one_mul, ← hy] using
        (fixed_image σ y).symm
    · change x.right * σ = σ * x.right
      rcases fieldAut_eq_one_or hp hF σ hne x.right with h | h <;> simp [h]

/-- A product map with its literal linear and field coordinates. -/
@[expose] def fieldCentralizerMap {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1) :
    PGL2 (FixedPoints.subfield (zpowers σ) F) × (F ≃+* F) →* PGammaL2 F where
  toFun x := ⟨ProjGenLinGroup.map
    (FixedPoints.subfield (zpowers σ) F).subtype x.1, x.2⟩
  map_one' := by apply SemidirectProduct.ext <;> simp
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change ProjGenLinGroup.map _ (x.1 * y.1) = _
      change ProjGenLinGroup.map _ (x.1 * y.1) =
        ProjGenLinGroup.map _ x.1 * pgl2FieldAut F x.2 (ProjGenLinGroup.map _ y.1)
      rw [map_mul, all_fieldAut_fixed hp hF σ hne]
    · rfl

include finF in
theorem fieldCentralizerMap_injective {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1) :
    Function.Injective (fieldCentralizerMap hp hF σ hne) := by
  intro x y h
  apply Prod.ext
  · exact pgl2_map_injective_of_injective _ (Subfield.subtype_injective _)
      (congrArg SemidirectProduct.left h)
  · exact congrArg SemidirectProduct.right h

/-- The image is the whole centralizer, not merely a subgroup of it. -/
theorem fieldCentralizerMap_range {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1) :
    (fieldCentralizerMap hp hF σ hne).range =
      centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) := by
  ext x
  rw [mem_fieldCentralizer_iff hp hF σ hne]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y.1, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨(y, x.right), SemidirectProduct.ext hy rfl⟩

/-- The actual pure-field centralizer is PGL₂ of the fixed field times
the field-automorphism group, whose order is two. -/
noncomputable def fieldCentralizerEquiv {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1) :
    PGL2 (FixedPoints.subfield (zpowers σ) F) × (F ≃+* F) ≃*
      centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) :=
  (MonoidHom.ofInjective (fieldCentralizerMap_injective hp hF σ hne)).trans
    (MulEquiv.subgroupCongr (fieldCentralizerMap_range hp hF σ hne))

/-- The subfield's full diagonal group lies in the ambient PSL₂ layer. -/
theorem subfieldEmbedding_range_le_psl {p : ℕ} (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) :
    (subfieldEmbedding σ).range ≤ pGammaL2PSLRange F := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := image_mem_psl hodd hF σ
    ((orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩) x
  exact (mem_pGammaL2PSLRange_iff F _).mpr ⟨y, congrArg SemidirectProduct.inl hy⟩

/-- The centralizer of an actor generated by a fixed-field subgroup and σ
is the image of the fixed-field centralizer times the full field factor.
This also computes the centralizer of every marked mixed four-group. -/
theorem centralizer_subfield_sup_pure {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1)
    (B : Subgroup (PGL2 (FixedPoints.subfield (zpowers σ) F))) :
    centralizer ((B.map (subfieldEmbedding σ) ⊔
      zpowers (SemidirectProduct.inr σ) : Subgroup (PGammaL2 F)) : Set (PGammaL2 F)) =
      ((centralizer (B : Set _) ).prod ⊤).map (fieldCentralizerMap hp hF σ hne) := by
  let f := fieldCentralizerMap hp hF σ hne
  have hb (b : PGL2 (FixedPoints.subfield (zpowers σ) F)) :
      subfieldEmbedding σ b = f (b, 1) := rfl
  have hs : (SemidirectProduct.inr σ : PGammaL2 F) = f (1, σ) := by
    apply SemidirectProduct.ext <;> simp [f, fieldCentralizerMap]
  ext x
  constructor
  · intro hx
    have hxs : x ∈ centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) := by
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_centralizer_iff.mp hx _ ((le_sup_right : zpowers (SemidirectProduct.inr σ) ≤
        B.map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ)) (mem_zpowers _))).symm
    rw [← fieldCentralizerMap_range hp hF σ hne] at hxs
    obtain ⟨y, rfl⟩ := hxs
    refine ⟨y, ⟨?_, mem_top _⟩, rfl⟩
    apply mem_centralizer_iff.mpr
    intro b hbB
    have hcomm := mem_centralizer_iff.mp hx (subfieldEmbedding σ b)
      ((le_sup_left : B.map (subfieldEmbedding σ) ≤
        B.map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ)) (mem_map_of_mem _ hbB))
    rw [hb, ← map_mul, ← map_mul] at hcomm
    have he := fieldCentralizerMap_injective hp hF σ hne hcomm
    exact congrArg Prod.fst he
  · rintro ⟨y, hy, rfl⟩
    have hle : B.map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ) ≤
        centralizer ({f y} : Set (PGammaL2 F)) := by
      apply sup_le
      · rintro _ ⟨b, hbB, rfl⟩
        rw [mem_centralizer_singleton_iff, hb, ← map_mul, ← map_mul]
        apply congrArg f
        apply Prod.ext
        · exact mem_centralizer_iff.mp hy.1 b hbB
        · simp
      · apply zpowers_le.mpr
        rw [mem_centralizer_singleton_iff, hs, ← map_mul, ← map_mul]
        apply congrArg f
        apply Prod.ext
        · simp
        · change σ * y.2 = y.2 * σ
          rcases fieldAut_eq_one_or hp hF σ hne y.2 with h | h <;> simp [h]
    exact mem_centralizer_iff.mpr (fun a ha => mem_centralizer_singleton_iff.mp (hle ha))

/-- The full quadratic semilinear group has trivial two-core. The proof
uses the actual top subgroup and its canonical equivalence. -/
theorem full_twoCore_eq_bot {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    [Finite (PGammaL2 F)] : pCore 2 (PGammaL2 F) = ⊥ := by
  have ht := FieldWitnesses.twoCore_eq_bot hp hodd hF hlarge
    (⊤ : Subgroup (PGammaL2 F)) le_top
  rw [← pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup (PGammaL2 F)) ≃* PGammaL2 F),
    ht, Subgroup.map_bot]

/-- Ambient tau is the literal centralizer intersection in the full model. -/
theorem full_tau_eq_inf_centralizer {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    [Finite (PGammaL2 F)] (T A : Subgroup (PGammaL2 F)) :
    tau T A = T ⊓ centralizer (A : Set (PGammaL2 F)) := by
  ext x
  rw [tau, mem_centralizerModulo_iff, mem_inf, mem_centralizer_iff]
  simp only [full_twoCore_eq_bot hp hodd hF hlarge, mem_bot,
    commutatorElement_eq_one_iff_mul_comm]
  rfl

/-- A local candidate containing the displayed fixed-field centralizer
intersection contains the ambient tau of the corresponding marked actor.
For cyclic B of order two this is the mixed rank-two E0 calculation. -/
theorem tau_subfield_sup_pure {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    [Finite (PGammaL2 F)] (σ : F ≃+* F) (hne : σ ≠ 1)
    (T : Subgroup (PGammaL2 F))
    (B : Subgroup (PGL2 (FixedPoints.subfield (zpowers σ) F))) :
    tau T (B.map (subfieldEmbedding σ) ⊔ zpowers (SemidirectProduct.inr σ)) =
      T ⊓ ((centralizer (B : Set _)).prod ⊤).map (fieldCentralizerMap hp hF σ hne) := by
  rw [full_tau_eq_inf_centralizer hp hodd hF hlarge,
    centralizer_subfield_sup_pure hp hF σ hne]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
