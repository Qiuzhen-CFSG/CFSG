module

public import Theory.GroupTheory.SuzukiTI
import Mathlib.Tactic.Group

/-!
# Elementary TI-subgroup criteria (Aschbacher--Smith, I.6)

This file records the elementary TI-set interface used throughout the first
chapter.  A TI-subgroup has trivial intersection with each of its distinct
conjugates; the identity is therefore retained in the intersection.  The
fusion/centralizer criterion in Lemma I.6.1(1) is proved here in full.  The normalizer and centralizer consequences below also support the tightly
embedded subgroup arguments of I.7 and the fusion criterion of I.8.4.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp. 424--430.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section06To08

universe u

variable {G : Type u} [Group G]

/-- A subgroup is a TI-subgroup when every conjugate outside its normalizer
meets it only in the identity.  We use a set-valued formulation so that the
definition is independent of finiteness assumptions. -/
def IsTISubgroup (X : Subgroup G) : Prop :=
  ∀ g : G, g ∉ Subgroup.normalizer (X : Set G) →
    (X : Set G) ∩ (fun x : G => g * x * g⁻¹) '' (X : Set G) ⊆ ({1} : Set G)

/-- The intersection criterion can be read pointwise. -/
theorem isTISubgroup_iff
    (X : Subgroup G) :
    IsTISubgroup X ↔
      ∀ g : G, g ∉ Subgroup.normalizer (X : Set G) →
        ∀ x : G, x ∈ X → g * x * g⁻¹ ∈ X → x = 1 := by
  constructor
  · intro h g hg x hx hgx
    have hx' : g * x * g⁻¹ ∈
        (X : Set G) ∩ (fun y : G => g * y * g⁻¹) '' (X : Set G) :=
      ⟨hgx, ⟨x, hx, rfl⟩⟩
    have hone : g * x * g⁻¹ = 1 := by simpa using h g hg hx'
    have := congrArg (fun z : G => g⁻¹ * z * g) hone
    simpa [mul_assoc] using this
  · intro h g hg x hx
    rcases hx with ⟨hxX, ⟨y, hyX, hxy⟩⟩
    have hy1 : y = 1 := h g hg y hyX (by simpa [hxy] using hxX)
    have : g * 1 * g⁻¹ = x := by simpa [hy1] using hxy
    simpa using this.symm

/-! ### Lemma I.6.1(1) -/

/--
Lemma I.6.1(1).  Let `M = N_G(X)`.  If centralizers of nonidentity
elements of `X` lie in `M`, and `M` controls fusion in `X`, then `X` is a
TI-subgroup of `G`.

The fusion assumption is stated using the subgroup `M` itself, so the result
is useful without choosing representatives or invoking a Sylow theorem.
-/
public theorem lemma_I_6_1_1 (X M : Subgroup G)
    (hM : M = Subgroup.normalizer (X : Set G))
    (hcentral : ∀ x : G, x ∈ X → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ M)
    (hfusion : ∀ x y : G, x ∈ X → y ∈ X →
      (∃ g : G, g * x * g⁻¹ = y) →
      ∃ m : M, (m : G) * x * (m : G)⁻¹ = y) :
    IsTISubgroup X := by
  intro g hg
  have hgM : g ∉ M := by simpa [hM] using hg
  intro z hz
  rw [Set.mem_singleton_iff]
  rcases hz with ⟨hzX, ⟨x, hxX, hzx⟩⟩
  by_cases hx1 : x = 1
  · subst x
    simp at hzx
    exact hzx.symm
  obtain ⟨m, hm⟩ := hfusion x z hxX hzX ⟨g, hzx⟩
  have hc : (m : G)⁻¹ * g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha_eq : a = x := by simpa using ha
    subst a
    calc
      x * ((m : G)⁻¹ * g) =
          (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * g := by group
      _ = (m : G)⁻¹ * (g * x * g⁻¹) * g := by rw [hm, ← hzx]
      _ = ((m : G)⁻¹ * g) * x := by group
  have hcm : (m : G)⁻¹ * g ∈ M := hcentral x hxX hx1 hc
  exfalso
  apply hgM
  have hmg : (m : G) * ((m : G)⁻¹ * g) ∈ M := M.mul_mem m.property hcm
  simpa using hmg

/-- A convenient specialization of I.6.1(1) when fusion is equality inside
the normalizer. -/
public theorem lemma_I_6_1_1_of_mem_normalizer
    (X : Subgroup G)
    (hcentral : ∀ x : G, x ∈ X → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hfusion : ∀ x y : G, x ∈ X → y ∈ X →
      (∃ g : G, g * x * g⁻¹ = y) →
      ∃ m : Subgroup.normalizer (X : Set G),
        (m : G) * x * (m : G)⁻¹ = y) :
    IsTISubgroup X :=
  lemma_I_6_1_1 X (Subgroup.normalizer (X : Set G)) rfl hcentral hfusion

/-- The TI condition is invariant under replacing a subgroup by an equal one. -/
public theorem isTISubgroup_congr {X Y : Subgroup G} (hXY : X = Y) :
    IsTISubgroup X ↔ IsTISubgroup Y := by
  subst Y
  rfl

/-- A conjugator taking a nonidentity element of a TI-subgroup back into that
subgroup normalizes the whole subgroup. -/
theorem IsTISubgroup.mem_normalizer_of_conj_mem {X : Subgroup G}
    (hX : IsTISubgroup X) {g x : G} (hx : x ∈ X) (hne : x ≠ 1)
    (hconj : g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  by_contra hg
  exact hne ((isTISubgroup_iff X).mp hX g hg x hx hconj)

/-- Centralizers of nonidentity elements of a TI-subgroup normalize it. This
is the necessary direction of the criterion used in Remark I.8.4. -/
theorem IsTISubgroup.centralizer_le_normalizer {X : Subgroup G}
    (hX : IsTISubgroup X) {x : G} (hx : x ∈ X) (hne : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  apply hX.mem_normalizer_of_conj_mem hx hne
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hx

/-- The normalizer of a TI-subgroup controls fusion of its elements. -/
theorem IsTISubgroup.controls_fusion {X : Subgroup G} (hX : IsTISubgroup X)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (hconj : ∃ g : G, g * x * g⁻¹ = y) :
    ∃ m : Subgroup.normalizer (X : Set G), (m : G) * x * (m : G)⁻¹ = y := by
  obtain ⟨g, hg⟩ := hconj
  by_cases hx1 : x = 1
  · subst x
    refine ⟨1, ?_⟩
    simpa using hg
  · exact ⟨⟨g, hX.mem_normalizer_of_conj_mem hx hx1 (hg.symm ▸ hy)⟩, hg⟩

/-- Every nontrivial subgroup of a TI-subgroup has its normalizer contained in
the normalizer of the TI-subgroup. -/
theorem IsTISubgroup.normalizer_le_of_ne_bot {X A : Subgroup G}
    (hX : IsTISubgroup X) (hA : A ≠ ⊥) (hAX : A ≤ X) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  intro g hg
  apply hX.mem_normalizer_of_conj_mem (hAX ha) (fun heq => ha1 (Subtype.ext heq))
  exact hAX ((Subgroup.mem_normalizer_iff.mp hg a).mp ha)

/-- I.6.1(1) is an equivalence once the necessary TI consequences are included. -/
theorem isTISubgroup_iff_centralizer_and_fusion (X : Subgroup G) :
    IsTISubgroup X ↔
      (∀ x ∈ X, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.normalizer (X : Set G)) ∧
      (∀ x y : G, x ∈ X → y ∈ X → (∃ g : G, g * x * g⁻¹ = y) →
        ∃ m : Subgroup.normalizer (X : Set G),
          (m : G) * x * (m : G)⁻¹ = y) := by
  constructor
  · intro hX
    exact ⟨fun _ hx hne => hX.centralizer_le_normalizer hx hne,
      fun _ _ hx hy hg => hX.controls_fusion hx hy hg⟩
  · rintro ⟨hc, hf⟩
    exact lemma_I_6_1_1_of_mem_normalizer X hc hf

end CFSG.Quasithin.ChapterI.Section06To08
