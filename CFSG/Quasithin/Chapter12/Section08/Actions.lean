module

public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The literal quotient actions in Section 12.8

Conjugation by a subgroup of G₁ on a normalized subgroup descends to its
actual image in G₁/V₁. We construct that action, its evaluation on the
quotient map, and its kernel. The central quotient U/Z(U) carries the
corresponding conjugation action of H = G₁.

The kernel criteria use ambient commutators and the actual denominator;
they do not assume the two-core equality of 12.8.4(4).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 12.8.2 and Lemmas 12.8.4, 12.8.8, printed pp.849–852.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The quotient map used by all tilded subgroups. -/
def tildeProjection (F : InvariantFlag T V n) : F.H →* F.G₁tilde :=
  QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H)

/-- The quotient map restricted to a subgroup of the point normalizer. -/
def tildeMap (F : InvariantFlag T V n) (A : Subgroup G) (hAH : A ≤ F.H) :
    A →* F.tilde A :=
  ((F.tildeProjection).comp (inclusion hAH)).codRestrict (F.tilde A)
    (fun a => mem_map.mpr ⟨⟨a, hAH a.property⟩, a.property, rfl⟩)

@[simp] theorem tildeMap_coe (F : InvariantFlag T V n) (A : Subgroup G)
    (hAH : A ≤ F.H) (a : A) :
    (F.tildeMap A hAH a : F.G₁tilde) = F.tildeProjection ⟨a, hAH a.property⟩ := rfl

theorem tildeMap_surjective (F : InvariantFlag T V n) (A : Subgroup G)
    (hAH : A ≤ F.H) : Function.Surjective (F.tildeMap A hAH) := by
  intro q
  obtain ⟨a, ha, he⟩ := q.property
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem tilde_normalizes (F : InvariantFlag T V n) (J A : Subgroup G)
    (hJA : J ≤ normalizer (A : Set G)) :
    F.tilde J ≤ normalizer (F.tilde A : Set F.G₁tilde) := by
  have h : J.subgroupOf F.H ≤ normalizer (A.subgroupOf F.H : Set F.H) := by
    intro j hj
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hJA hj) a
  exact (map_mono h).trans ((A.subgroupOf F.H).le_normalizer_map F.tildeProjection)

/-- The actor's image in the normalizer of the literal tilded subgroup. -/
def tildeActor (F : InvariantFlag T V n) (J A : Subgroup G)
    (hJH : J ≤ F.H) (hJA : J ≤ normalizer (A : Set G)) :
    J →* normalizer (F.tilde A : Set F.G₁tilde) :=
  ((F.tildeProjection).comp (inclusion hJH)).codRestrict _ (fun j =>
    tilde_normalizes F J A hJA (mem_map.mpr ⟨⟨j, hJH j.property⟩, j.property, rfl⟩))

/-- Conjugation on the image of A in G₁/V₁, with J as actual actor. -/
def tildeAction (F : InvariantFlag T V n) (J A : Subgroup G)
    (hJH : J ≤ F.H) (hJA : J ≤ normalizer (A : Set G)) :
    J →* MulAut (F.tilde A) :=
  (F.tilde A).normalizerMonoidHom.comp (F.tildeActor J A hJH hJA)

@[simp] theorem tildeAction_apply_coe (F : InvariantFlag T V n)
    (J A : Subgroup G) (hJH : J ≤ F.H) (hJA : J ≤ normalizer (A : Set G))
    (j : J) (a : F.tilde A) :
    (F.tildeAction J A hJH hJA j a : F.G₁tilde) =
      F.tildeProjection ⟨j, hJH j.property⟩ * a *
        (F.tildeProjection ⟨j, hJH j.property⟩)⁻¹ := rfl

/-- Evaluation agrees with ambient conjugation before taking the quotient. -/
theorem tildeAction_apply_map (F : InvariantFlag T V n)
    (J A : Subgroup G) (hJH : J ≤ F.H) (hAH : A ≤ F.H)
    (hJA : J ≤ normalizer (A : Set G)) (j : J) (a : A) :
    F.tildeAction J A hJH hJA j (F.tildeMap A hAH a) =
      F.tildeMap A hAH ⟨(j : G) * a * (j : G)⁻¹,
        (mem_normalizer_iff.mp (hJA j.property) a).mp a.property⟩ := by
  apply Subtype.ext
  simp only [tildeAction_apply_coe, tildeMap_coe]
  exact (map_mul F.tildeProjection _ _).symm.trans
    (congrArg F.tildeProjection (by ext; rfl))

/-- The actual action kernel, expressed by commutators in the ambient group. -/
theorem mem_tildeAction_ker_iff (F : InvariantFlag T V n)
    (J A : Subgroup G) (hJH : J ≤ F.H) (hAH : A ≤ F.H)
    (hJA : J ≤ normalizer (A : Set G)) (j : J) :
    j ∈ (F.tildeAction J A hJH hJA).ker ↔
      ∀ a ∈ A, ⁅(j : G), a⁆ ∈ F.Vi 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hj a ha
    have he := congrArg (fun e : MulAut (F.tilde A) =>
      (e (F.tildeMap A hAH ⟨a, ha⟩) : F.G₁tilde)) hj
    rw [tildeAction_apply_map] at he
    change F.tildeProjection _ = F.tildeProjection _ at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    change (j : G) * a * (j : G)⁻¹ / a ∈ F.Vi 1 at hm
    simpa only [commutatorElement_def, div_eq_mul_inv] using hm
  · intro hj
    ext q
    obtain ⟨a, rfl⟩ := F.tildeMap_surjective A hAH q
    rw [tildeAction_apply_map]
    change F.tildeProjection _ = F.tildeProjection _
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (j : G) * a * (j : G)⁻¹ / a ∈ F.Vi 1
    simpa only [commutatorElement_def, div_eq_mul_inv] using hj a a.property

/-- The kernel is the pullback of the centralizer in the actual quotient. -/
theorem tildeAction_ker (F : InvariantFlag T V n)
    (J A : Subgroup G) (hJH : J ≤ F.H) (hJA : J ≤ normalizer (A : Set G)) :
    (F.tildeAction J A hJH hJA).ker =
      (centralizer (F.tilde A : Set F.G₁tilde)).comap
        (F.tildeProjection.comp (inclusion hJH)) := by
  ext j
  rw [MonoidHom.mem_ker]
  constructor
  · intro hj q hq
    have he := congrArg (fun e : MulAut (F.tilde A) => (e ⟨q, hq⟩ : F.G₁tilde)) hj
    rw [tildeAction_apply_coe] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hj
    ext q
    rw [tildeAction_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr (hj q q.property).symm

/-- Local spans remain inside the point normalizer. -/
theorem UH_le_H (F : InvariantFlag T V n) [IsMulCommutative V]
    (J : Subgroup G) (hJH : J ≤ F.H) : F.UH J ≤ F.H :=
  (conjugateSpanBy_mono le_rfl hJH).trans F.U_le_H

/-- The action on the actual tilded conjugate span for every local H. -/
def localTildeAction (F : InvariantFlag T V n) (J : Subgroup G) (hJH : J ≤ F.H) :
    J →* MulAut (F.tilde (F.UH J)) :=
  F.tildeAction J (F.UH J) hJH (le_normalizer_conjugateSpanBy V J)

/-- Kernel evaluation for precisely the span U_H used in 12.8.4. -/
theorem mem_localTildeAction_ker_iff (F : InvariantFlag T V n) [IsMulCommutative V]
    (J : Subgroup G) (hJH : J ≤ F.H) (j : J) :
    j ∈ (F.localTildeAction J hJH).ker ↔
      ∀ a ∈ F.UH J, ⁅(j : G), a⁆ ∈ F.Vi 1 :=
  F.mem_tildeAction_ker_iff J (F.UH J) hJH (F.UH_le_H J hJH)
    (le_normalizer_conjugateSpanBy V J) j

/-- H acts on U itself, with no assumption about its centralizer. -/
def uAction (F : InvariantFlag T V n) : F.H →* MulAut F.U :=
  F.U.normalizerMonoidHom.comp
    (F.H.subtype.codRestrict _ (fun h => le_normalizer_conjugateSpanBy V F.H h.property))

@[simp] theorem uAction_apply (F : InvariantFlag T V n) (h : F.H) (a : F.U) :
    (F.uAction h a : G) = (h : G) * a * (h : G)⁻¹ := rfl

/-- The literal action on U/Z(U). -/
def uhatAction (F : InvariantFlag T V n) : F.H →* MulAut F.Uhat :=
  (quotientAut (center F.U)).comp F.uAction

@[simp] theorem uhatAction_apply_mk (F : InvariantFlag T V n)
    (h : F.H) (a : F.U) :
    F.uhatAction h (QuotientGroup.mk' (center F.U) a) =
      QuotientGroup.mk' (center F.U) (F.uAction h a) :=
  quotientAut_apply_mk _ _ _

/-- Its kernel consists exactly of elements whose commutators with U lie in Z(U). -/
theorem mem_uhatAction_ker_iff (F : InvariantFlag T V n) (h : F.H) :
    h ∈ F.uhatAction.ker ↔ ∀ a ∈ F.U, ⁅(h : G), a⁆ ∈ F.ZU := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hh a ha
    have he := congrArg (fun e : MulAut F.Uhat =>
      e (QuotientGroup.mk' (center F.U) ⟨a, ha⟩)) hh
    rw [uhatAction_apply_mk] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    refine mem_map.mpr ⟨_, hm, ?_⟩
    change ((h : G) * a * (h : G)⁻¹) / a = ⁅(h : G), a⁆
    simp only [commutatorElement_def, div_eq_mul_inv]
  · intro hh
    ext q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center F.U) q
    rw [uhatAction_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨b, hb, he⟩ := hh a a.property
    have he' : b = F.uAction h a / a := by
      apply Subtype.ext
      change F.U.subtype b = ((h : G) * a * (h : G)⁻¹) / a
      simpa only [commutatorElement_def, div_eq_mul_inv] using he
    exact he' ▸ hb

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
