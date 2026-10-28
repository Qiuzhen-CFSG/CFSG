module

public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.CentralCommutatorQuotient

/-!
# The intrinsic commutator pairing used in MS93 (1.7)

The values are literal ambient commutators, and the radicals are actual
centralizers. Normal closure extends the initial commutator bound. Evaluating
at an element gives a homomorphism, and simultaneous evaluation embeds the
quotient by the full centralizer in a function group. Equivariance only needs
the actor to fix the evaluation element modulo the centralizer of the domain.

This is the group-theoretic pairing construction for Meierfrankenfeld--
Stellmacher (1993), (1.7), printed pp.847--848. The local incidence argument
and the natural/dual module recognition are separate obligations.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing

open Subgroup
open scoped commutatorElement

universe u
variable {M : Type u} [Group M]

/-- The source U is the ambient normal closure, not X itself. -/
def generated (X : Subgroup M) : Subgroup M := normalClosure (X : Set M)

/-- Source C_U(W), intrinsically a subgroup of U. -/
def leftRadical (U W : Subgroup M) : Subgroup U :=
  (centralizer (W : Set M)).subgroupOf U

/-- Normality in M is only required for W and Z, never for X. -/
theorem generated_commutator_le (X W Z : Subgroup M) [W.Normal] [Z.Normal]
    (h : ⁅X, W⁆ ≤ Z) : ⁅generated X, W⁆ ≤ Z := by
  rw [commutator_comm]
  exact commutator_normalClosure_le_of_normal W X Z (by rwa [commutator_comm])

/-- Normal closure stays in a normal overgroup. -/
theorem generated_le (X Q : Subgroup M) [Q.Normal] (h : X ≤ Q) : generated X ≤ Q :=
  normalClosure_le_normal h

instance generated_normal (X : Subgroup M) : (generated X).Normal :=
  inferInstanceAs (normalClosure (X : Set M)).Normal

instance leftRadical_normal (U W : Subgroup M) [W.Normal] : (leftRadical U W).Normal :=
  inferInstanceAs ((centralizer (W : Set M)).subgroupOf U).Normal

variable (U W Z : Subgroup M) (hUW : ⁅U, W⁆ ≤ Z)
  (hZU : Z ≤ centralizer (U : Set M))

/-- Evaluation of the pairing at w, with ambient value [w,u]. -/
def evaluation (w : W) : U →* Z :=
  centralCommutatorHom U Z hZU w (fun x hx => hUW (by
    rw [commutator_comm]
    exact commutator_mem_commutator w.property hx))

@[simp] theorem evaluation_apply (w : W) (x : U) :
    (evaluation U W Z hUW hZU w x : M) = ⁅(w : M), (x : M)⁆ := rfl

/-- Simultaneous evaluation at every element of W. -/
def pairingHom : U →* (W → Z) where
  toFun x w := evaluation U W Z hUW hZU w x
  map_one' := by funext w; exact (evaluation U W Z hUW hZU w).map_one
  map_mul' x y := by funext w; exact (evaluation U W Z hUW hZU w).map_mul x y

/-- The simultaneous kernel is exactly the intrinsic centralizer. -/
theorem pairingHom_ker : (pairingHom U W Z hUW hZU).ker = leftRadical U W := by
  ext x
  change (fun w : W => evaluation U W Z hUW hZU w x) = 1 ↔
    (x : M) ∈ centralizer (W : Set M)
  constructor
  · intro h
    apply mem_centralizer_iff_commutator_eq_one.mpr
    intro w hw
    exact congrArg (fun f : W → Z => (f ⟨w, hw⟩ : M)) h
  · intro h
    funext w
    apply Subtype.ext
    exact mem_centralizer_iff_commutator_eq_one.mp h w w.property

/-- The actual quotient by C_U(W), identified with the image of the pairing. -/
noncomputable def pairingQuotientEquiv [W.Normal] :
    U ⧸ leftRadical U W ≃* (pairingHom U W Z hUW hZU).range :=
  (QuotientGroup.quotientMulEquivOfEq (pairingHom_ker U W Z hUW hZU).symm).trans
    (QuotientGroup.quotientKerEquivRange (pairingHom U W Z hUW hZU))

/-- A quotient class is sent to its literal commutator function. -/
theorem pairingQuotientEquiv_apply [W.Normal] (x : U) (w : W) :
    (((pairingQuotientEquiv U W Z hUW hZU
      (QuotientGroup.mk' (leftRadical U W) x) :
        (pairingHom U W Z hUW hZU).range) : W → Z) w : M) =
      ⁅(w : M), (x : M)⁆ := rfl

/-- The first variable is also multiplicative if Z centralizes W. -/
theorem evaluation_mul (hZW : Z ≤ centralizer (W : Set M)) (a b : W) (x : U) :
    evaluation U W Z hUW hZU (a * b) x =
      evaluation U W Z hUW hZU b x * evaluation U W Z hUW hZU a x := by
  apply Subtype.ext
  change ⁅(a : M) * (b : M), (x : M)⁆ = ⁅(b : M), (x : M)⁆ * ⁅(a : M), (x : M)⁆
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc := hZW (evaluation U W Z hUW hZU b x).property a a.property
  change (a : M) * ⁅(b : M), (x : M)⁆ = ⁅(b : M), (x : M)⁆ * (a : M) at hc
  rw [hc, mul_inv_cancel_right]

/-- Surjective evaluation gives the literal elementwise commutator identity. -/
theorem commutator_eq_of_evaluation_surjective (w : W)
    (hs : Function.Surjective (evaluation U W Z hUW hZU w)) :
    ⁅U, zpowers (w : M)⁆ = Z := by
  apply le_antisymm
  · exact (commutator_mono le_rfl (zpowers_le.mpr w.property)).trans hUW
  · intro z hz
    obtain ⟨x, hx⟩ := hs ⟨z, hz⟩
    have hv := congrArg Subtype.val hx
    change ⁅(w : M), (x : M)⁆ = z at hv
    rw [← hv, commutator_comm]
    exact commutator_mem_commutator (mem_zpowers _) x.property

/-- If W/C_W(U) is generated by w, evaluation has the full pairing radical. -/
theorem evaluation_ker_of_cyclic (w : W)
    (hgen : W ≤ zpowers (w : M) ⊔ centralizer (U : Set M)) :
    (evaluation U W Z hUW hZU w).ker = leftRadical U W := by
  rw [evaluation, centralCommutatorHom_ker]
  ext x
  change (x : M) ∈ centralizer ({(w : M)} : Set M) ↔
    (x : M) ∈ centralizer (W : Set M)
  constructor
  · intro hx
    apply mem_centralizer_iff.mpr
    have hW : W ≤ centralizer ({(x : M)} : Set M) := hgen.trans (sup_le ?_ ?_)
    · intro a ha
      exact mem_centralizer_singleton_iff.mp (hW ha)
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hx).symm
    · intro a ha
      exact mem_centralizer_singleton_iff.mpr (ha x x.property).symm
  · intro hx
    exact mem_centralizer_singleton_iff.mpr (hx w w.property).symm

/-- The quotient by C_U(W) is identified by evaluation, without choosing an
unrelated action or an abstract isomorphic carrier. -/
noncomputable def evaluationQuotientEquiv [W.Normal] (w : W)
    (hgen : W ≤ zpowers (w : M) ⊔ centralizer (U : Set M))
    (hs : Function.Surjective (evaluation U W Z hUW hZU w)) :
    U ⧸ leftRadical U W ≃* Z :=
  (QuotientGroup.quotientMulEquivOfEq
    (evaluation_ker_of_cyclic U W Z hUW hZU w hgen).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hs)

@[simp] theorem evaluationQuotientEquiv_apply [W.Normal] (w : W)
    (hgen : W ≤ zpowers (w : M) ⊔ centralizer (U : Set M))
    (hs : Function.Surjective (evaluation U W Z hUW hZU w)) (x : U) :
    (evaluationQuotientEquiv U W Z hUW hZU w hgen hs
      (QuotientGroup.mk' (leftRadical U W) x) : M) = ⁅(w : M), (x : M)⁆ := rfl

/-- Equivariance needs trivial action on W/C_W(U), not on W itself. -/
theorem evaluation_conj [U.Normal] (L : Subgroup M)
    (htriple : ⁅⁅W, L⁆, U⁆ = ⊥) (l : M) (hl : l ∈ L) (w : W) (x y : U)
    (hy : (y : M) = l * (x : M) * l⁻¹) :
    (evaluation U W Z hUW hZU w y : M) =
      l * (evaluation U W Z hUW hZU w x : M) * l⁻¹ := by
  have hk : ⁅(w : M), l⁆ ∈ centralizer (U : Set M) :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple)
      (commutator_mem_commutator w.property hl)
  have ht : (l * (w : M)) * (x : M) * (l * (w : M))⁻¹ ∈ U :=
    (inferInstance : U.Normal).conj_mem _ x.property _
  have hc := hk _ ht
  change ⁅(w : M), (y : M)⁆ = l * ⁅(w : M), (x : M)⁆ * l⁻¹
  rw [hy]
  have ha : (w : M) * l * (x : M) * l⁻¹ * (w : M)⁻¹ =
      (l * (w : M)) * (x : M) * (l * (w : M))⁻¹ := by
    calc
      _ = ⁅(w : M), l⁆ *
          ((l * (w : M)) * (x : M) * (l * (w : M))⁻¹) * ⁅(w : M), l⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      _ = _ := by rw [← hc]; group
  simp only [commutatorElement_def]
  calc
    _ = ((w : M) * l * (x : M) * l⁻¹ * (w : M)⁻¹) *
        (l * (x : M) * l⁻¹)⁻¹ := by group
    _ = _ := by rw [ha]; group

/-- Irreducibility of the target makes every nonzero equivariant evaluation
surjective. All commutators and invariance assertions are intrinsic. -/
theorem evaluation_surjective [U.Normal] (L : Subgroup M)
    (htriple : ⁅⁅W, L⁆, U⁆ = ⊥)
    (hirr : ∀ D : Subgroup M, D ≤ Z → L ≤ normalizer (D : Set M) → D = ⊥ ∨ D = Z)
    (w : W) (hw : (w : M) ∉ centralizer (U : Set M)) :
    Function.Surjective (evaluation U W Z hUW hZU w) := by
  let f := evaluation U W Z hUW hZU w
  let D := f.range.map Z.subtype
  have hDZ : D ≤ Z := map_subtype_le f.range
  have hLD : L ≤ normalizer (D : Set M) := by
    apply le_normalizer_iff.mpr
    intro l hl d hd
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hd
    let y : U := ⟨l * (x : M) * l⁻¹, (inferInstance : U.Normal).conj_mem _ x.property l⟩
    refine ⟨f y, ⟨y, rfl⟩, ?_⟩
    exact evaluation_conj U W Z hUW hZU L htriple l hl w x y rfl
  have hDne : D ≠ ⊥ := by
    intro hD
    apply hw
    apply mem_centralizer_iff_commutator_eq_one'.mpr
    intro x hx
    have hd : ⁅(w : M), x⁆ ∈ D := ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    simpa only [hD, mem_bot] using hd
  have he := (hirr D hDZ hLD).resolve_left hDne
  intro z
  have hz : (z : M) ∈ D := he.symm ▸ z.property
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hz
  exact ⟨x, Subtype.ext hx⟩

/-- The explicit quotient isomorphism intertwines the actual conjugation
on representatives. For binary elementary groups this is GF(2)-linearity. -/
theorem evaluationQuotientEquiv_conj [U.Normal] [W.Normal]
    (L : Subgroup M) (htriple : ⁅⁅W, L⁆, U⁆ = ⊥) (w : W)
    (hgen : W ≤ zpowers (w : M) ⊔ centralizer (U : Set M))
    (hs : Function.Surjective (evaluation U W Z hUW hZU w))
    (l : M) (hl : l ∈ L) (x y : U) (hy : (y : M) = l * (x : M) * l⁻¹) :
    (evaluationQuotientEquiv U W Z hUW hZU w hgen hs
      (QuotientGroup.mk' (leftRadical U W) y) : M) =
      l * (evaluationQuotientEquiv U W Z hUW hZU w hgen hs
        (QuotientGroup.mk' (leftRadical U W) x) : M) * l⁻¹ :=
  evaluation_conj U W Z hUW hZU L htriple l hl w x y hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
