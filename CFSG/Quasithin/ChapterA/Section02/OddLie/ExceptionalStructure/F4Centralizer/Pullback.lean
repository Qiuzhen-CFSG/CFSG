module

public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer.OddCover
public import Theory.SpecificGroups.LieType.ExceptionalSplitModels
public import Theory.SpecificGroups.LieType.TwistedE6Model

/-!
# Pulling back an embedded F₄ through an odd central cover

The inverse image of an actual F₄ subgroup under the original central
surjection maps onto that same F₄ carrier, with an odd central kernel.
The proved F₄ cover exclusion contradicts quasithinness of this inverse
image, inherited as a subgroup of the original group. No identification
of the restricted kernel with the entire preimage center is needed.

The four higher-exceptional applications use the actual quotient-level
maps of the existing F4InE6, F4InE7, F4InE8 and F4InTwistedE6 conventions.
Injectivity suffices; their stronger proper-section APIs are preserved.
The source identification G/Z(G) and the twisted field GF(p^(m+1)) remain
literal. The realization owners supply these genuine model embeddings,
and the A.2 assembly supplies the original odd-center reduction.

Source: Aschbacher--Smith A.2.17, printed p.39, the higher exceptional
families following the F₄ exclusion. This direct local obstruction avoids
the strict-cardinality induction step for this particular application.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.F4OddCover.Pullback
open Subgroup Theory.GroupTheory
open ExceptionalSplit

universe u v w
variable {G : Type u} {Q : Type v} {F : Type w}
  [Group G] [Finite G] [Group Q] [Field F] [Finite F]

/-- The literal preimage of an embedded F₄ is an odd central cover of F₄.
Quasithinness of the original group would pass to this preimage. -/
theorem not_quasithin_of_central_cover_embedding
    {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (π : G →* Q) (hπ : Function.Surjective π)
    (hc : π.ker ≤ center G) (ho : Odd (Nat.card π.ker))
    (f : F4 F →* Q) (hf : Function.Injective f) : ¬ IsQuasithin G := by
  intro hG
  let P := f.range.comap π
  let e : F4 F ≃* f.range := MonoidHom.ofInjective hf
  let q₀ : P →* f.range := π.subgroupComap f.range
  let q : P →* F4 F := e.symm.toMonoidHom.comp q₀
  have hq (x : P) : f (q x) = π x :=
    congrArg Subtype.val (e.apply_symm_apply (q₀ x))
  have hqs : Function.Surjective q :=
    e.symm.surjective.comp (π.subgroupComap_surjective_of_surjective f.range hπ)
  have hker {x : P} (hx : x ∈ q.ker) : (x : G) ∈ π.ker := by
    change π x = 1
    rw [← hq, MonoidHom.mem_ker.mp hx, map_one]
  have hqc : q.ker ≤ center P := by
    intro x hx
    exact mem_center_iff.mpr (fun y =>
      Subtype.ext (mem_center_iff.mp (hc (hker hx)) y))
  let k : q.ker →* π.ker := (P.subtype.comp q.ker.subtype).codRestrict _
    (fun x => hker x.property)
  have hki : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : π.ker => (z : G)) h))
  have hqo : Odd (Nat.card q.ker) := ho.of_dvd_nat (card_dvd_of_injective k hki)
  exact F4OddCover.not_quasithin_of_central_cover hp hcard q hqs hqc hqo
    (hG.subgroup P)

/-- The original G/Z(G) marking supplies the central surjection. Only an
actual injective F₄ map into the marked quotient model is required. -/
theorem not_quasithin_of_odd_center_embedding
    {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (e : G ⧸ center G ≃* Q) (ho : Odd (Nat.card (center G)))
    (f : F4 F →* Q) (hf : Function.Injective f) : ¬ IsQuasithin G := by
  let π : G →* Q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center G := by
    dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact not_quasithin_of_central_cover_embedding hp hcard π hπ
    (by rw [hker]) (by simpa only [hker] using ho) f hf

/-- Actual split-E₆ source application, with the quotient-level F₄ map. -/
theorem not_quasithin_e6_of_embedding
    {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (e : G ⧸ center G ≃* E6 F) (ho : Odd (Nat.card (center G)))
    (f : F4 F →* E6 F) (hf : Function.Injective f) : ¬ IsQuasithin G :=
  not_quasithin_of_odd_center_embedding hp hcard e ho f hf

/-- Actual split-E₇ source application, without a map on the E₆ quotient. -/
theorem not_quasithin_e7_of_embedding
    {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (e : G ⧸ center G ≃* E7 F) (ho : Odd (Nat.card (center G)))
    (f : F4 F →* E7 F) (hf : Function.Injective f) : ¬ IsQuasithin G :=
  not_quasithin_of_odd_center_embedding hp hcard e ho f hf

/-- Actual split-E₈ source application, with its original central quotient. -/
theorem not_quasithin_e8_of_embedding
    {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (e : G ⧸ center G ≃* E8 F) (ho : Odd (Nat.card (center G)))
    (f : F4 F →* E8 F) (hf : Function.Injective f) : ¬ IsQuasithin G :=
  not_quasithin_of_odd_center_embedding hp hcard e ho f hf

/-- The twisted-E₆ convention uses GF(p^(m+1)) and the literal Model p m
carrier, as in F4InTwistedE6; no proper-range premise is used. -/
theorem not_quasithin_twistedE6_of_embedding
    {p m : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (e : G ⧸ center G ≃* TwistedE6.Model p m) (ho : Odd (Nat.card (center G)))
    (f : F4 (GaloisField p (m + 1)) →* TwistedE6.Model p m)
    (hf : Function.Injective f) : ¬ IsQuasithin G :=
  not_quasithin_of_odd_center_embedding hp
    (GaloisField.card p (m + 1) (Nat.succ_ne_zero m)) e ho f hf

end CFSG.Quasithin.ChapterA.Section02.F4OddCover.Pullback
