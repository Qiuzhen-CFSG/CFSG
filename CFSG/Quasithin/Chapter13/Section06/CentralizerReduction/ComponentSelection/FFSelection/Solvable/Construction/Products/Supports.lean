module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Supports.Linear

/-!
# The original order-four supports in the two-S₃ branch

The native Chapter B quotient planes lift by averaging over A₃ × A₃.
Transport through the original inclusion U_v → G identifies them with the
literal double commutators. Multiplication of those inclusions gives the
support product equivalence; its application theorem records the value in G.

For a single S₃ factor with an arbitrary other source factor, and for the
hyperplane branch, the final adapters still require fixed-kernel disjointness.
Their hypotheses identify exactly the remaining offender-generation step;
no splitting of the original module is silently inferred from a quotient.
Normality, Thompson equality, and final NormalS3Decomposition assembly are
independent of these module calculations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3),(5), printed p.105, and the first construction of 13.6.13, p.929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

private theorem commutator_comp_map {D E W : Type*} [Group D] [Group E]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (f : E →* D) (U : Submodule (ZMod 2) W) (A : Subgroup E) :
    subspaceCommutator (ρ.comp f) U A = subspaceCommutator ρ U (A.map f) := by
  unfold subspaceCommutator
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, u, hu, rfl⟩
    exact ⟨f a, mem_map_of_mem f ha, u, hu, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩
    exact ⟨a, ha, u, hu, rfl⟩

variable {G : Type*} [Group G] (z v : G) [IsElementaryAbelian 2 (Uv z v)]

private theorem ambient_moved (A : Subgroup (FFFactors.offenderActor (starRepresentation z v))) :
    ambientSpace z v (moved (FFFactors.offenderRepresentation (starRepresentation z v)) A) =
      movedSubgroup z v (A.map (FFFactors.offenderActor (starRepresentation z v)).subtype) := by
  unfold moved FFFactors.offenderRepresentation
  rw [commutator_comp_map, moved_ambientSpace]

private theorem ambient_support
    (H A : Subgroup (FFFactors.offenderActor (starRepresentation z v))) :
    ambientSpace z v (subspaceCommutator (FFFactors.offenderRepresentation (starRepresentation z v))
      (moved (FFFactors.offenderRepresentation (starRepresentation z v)) H) A) =
      factorSupport z v (H.map (FFFactors.offenderActor (starRepresentation z v)).subtype)
        (A.map (FFFactors.offenderActor (starRepresentation z v)).subtype) := by
  unfold moved FFFactors.offenderRepresentation
  rw [commutator_comp_map, commutator_comp_map, support_ambientSpace]

omit [IsElementaryAbelian 2 (Uv z v)] in
private theorem top_map (I : Subgroup (Gstar z v)) :
    (⊤ : Subgroup I).map I.subtype = I := by
  rw [← MonoidHom.range_eq_map, range_subtype]

private theorem between_support {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W) (A : Subgroup D)
    (hs : subspaceCommutator ρ (moved ρ A) A = moved ρ A) :
    subspaceCommutator ρ (moved ρ ⊤) A = moved ρ A := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨a, ha, u, _, rfl⟩
    exact ⟨a, ha, u, Submodule.mem_top, rfl⟩
  · rw [← hs]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, u, hu, rfl⟩
    refine ⟨a, ha, u, ?_, rfl⟩
    apply (show moved ρ A ≤ moved ρ ⊤ from ?_) hu
    apply Submodule.span_mono
    rintro _ ⟨b, _, w, hw, rfl⟩
    exact ⟨b, mem_top b, w, hw, rfl⟩

private theorem support_of_linear [Finite G]
    (A : Subgroup (FFFactors.offenderActor (starRepresentation z v)))
    (h : subspaceCommutator (FFFactors.offenderRepresentation (starRepresentation z v))
        (moved (FFFactors.offenderRepresentation (starRepresentation z v)) A) A =
        moved (FFFactors.offenderRepresentation (starRepresentation z v)) A ∧
      Module.finrank (ZMod 2)
        (moved (FFFactors.offenderRepresentation (starRepresentation z v)) A) = 2) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := A.map I.subtype
    factorSupport z v H H = movedSubgroup z v H ∧ Nat.card (movedSubgroup z v H) = 4 := by
  dsimp only
  constructor
  · rw [← ambient_support, h.1, ambient_moved]
  · rw [← ambient_moved, ambientSpace_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h.2]
    rfl

/-- The actual singleton-factor conclusion from the native quotient clause
and an explicit proof that its moved space misses the global fixed kernel.
Eliminating that kernel remains a separate offender-generation obligation. -/
theorem twoFactor_singleton_support_of_disjoint [Finite G]
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (A : Subgroup (FFFactors.offenderActor (starRepresentation z v)))
    (hA : A = c.first ∨ A = c.second) (e : A ≃* Equiv.Perm (Fin 3))
    (hd : Disjoint (moved (FFFactors.offenderRepresentation (starRepresentation z v)) A)
      (FFFactors.offenderRepresentation (starRepresentation z v)).invariants) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := A.map I.subtype
    factorSupport z v H H = movedSubgroup z v H ∧ Nat.card (movedSubgroup z v H) = 4 := by
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  obtain ⟨U, hU⟩ : ∃ U, SourceFactorCase
      (FFFactors.offenderRepresentation (starRepresentation z v)) A U := by
    rcases hA with rfl | rfl
    · exact ⟨c.firstSpace, c.firstCase⟩
    · exact ⟨c.secondSpace, c.secondCase⟩
  exact support_of_linear z v A (factor_plane_of_disjoint _ hU e hd)

/-- The hyperplane singleton support, retaining the second factor's own
fixed kernel as an explicit lifting obligation. No whole-space splitting,
ambient normality, or irreducibility is assumed. -/
theorem hyperplane_support_of_disjoint [Finite G]
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Disjoint (moved (FFFactors.offenderRepresentation (starRepresentation z v)) c.second)
      (fixedSpace (FFFactors.offenderRepresentation (starRepresentation z v)) c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    factorSupport z v H H = movedSubgroup z v H ∧ Nat.card (movedSubgroup z v H) = 4 := by
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  exact support_of_linear z v c.second
    (hyperplane_plane_of_disjoint _ c.secondSpace_eq c.secondCase e hd)

/-- Both singleton supports and the support inside the full offender actor
are the original plane, when both native factors are S₃. -/
theorem twoFactor_factor_support [Finite G]
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (A : Subgroup (FFFactors.offenderActor (starRepresentation z v)))
    (hA : A = c.first ∨ A = c.second) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := A.map I.subtype
    factorSupport z v H H = movedSubgroup z v H ∧
      Nat.card (movedSubgroup z v H) = 4 ∧
      factorSupport z v I H = movedSubgroup z v H := by
  dsimp only
  let σ := FFFactors.offenderRepresentation (starRepresentation z v)
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  obtain ⟨_, _, hs₁, hs₂⟩ := twoFactor_spaces σ c e₁ e₂
  obtain ⟨_, hd₁, hd₂⟩ := twoFactor_lift σ c e₁ e₂
  have hs : subspaceCommutator σ (moved σ A) A = moved σ A := by
    rcases hA with rfl | rfl <;> assumption
  have hd : Module.finrank (ZMod 2) (moved σ A) = 2 := by
    rcases hA with rfl | rfl <;> assumption
  refine ⟨?_, ?_, ?_⟩
  · rw [← ambient_support, hs, ambient_moved]
  · rw [← ambient_moved, ambientSpace_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    rfl
  · have h := congrArg (ambientSpace z v) (between_support σ A hs)
    rw [ambient_support, ambient_moved, top_map] at h
    exact h

/-- Each literal support inside the full two-S₃ actor has order four. -/
theorem twoFactor_support_card [Finite G]
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (A : Subgroup (FFFactors.offenderActor (starRepresentation z v)))
    (hA : A = c.first ∨ A = c.second) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    Nat.card (factorSupport z v I (A.map I.subtype)) = 4 := by
  dsimp only
  have h := twoFactor_factor_support z v c e₁ e₂ A hA
  rw [h.2.2]
  exact h.2.1

private def ambientSumMap
    (W₁ W₂ W : Submodule (ZMod 2) (Additive (Uv z v)))
    (hs : W = W₁ ⊔ W₂) :
    (ambientSpace z v W₁ × ambientSpace z v W₂) →* ambientSpace z v W where
  toFun x := ⟨(x.1 : G) * (x.2 : G), by
    obtain ⟨a, ha, he⟩ := x.1.property
    obtain ⟨b, hb, hf⟩ := x.2.property
    refine ⟨a * b, ?_, ?_⟩
    · change Additive.ofMul (a * b) ∈ W
      rw [hs]
      exact Submodule.add_mem_sup ha hb
    · simp only [map_mul, he, hf]⟩
  map_one' := Subtype.ext (one_mul _)
  map_mul' x y := by
    apply Subtype.ext
    obtain ⟨a, _, ha⟩ := x.1.property
    obtain ⟨b, _, hb⟩ := x.2.property
    obtain ⟨c, _, hc⟩ := y.1.property
    obtain ⟨d, _, hd⟩ := y.2.property
    change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
      ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
    rw [← ha, ← hb, ← hc, ← hd]
    exact congrArg (fun u : Uv z v => (u : G)) (mul_mul_mul_comm a c b d)

private theorem ambientSumMap_bijective
    (W₁ W₂ W : Submodule (ZMod 2) (Additive (Uv z v)))
    (hd : Disjoint W₁ W₂) (hs : W = W₁ ⊔ W₂) :
    Function.Bijective (ambientSumMap z v W₁ W₂ W hs) := by
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    rintro ⟨a, b⟩ hab
    obtain ⟨x, hx, he⟩ := a.property
    obtain ⟨y, hy, hf⟩ := b.property
    have heq : x * y = 1 := by
      apply Subtype.ext
      have h := congrArg Subtype.val hab
      change (a : G) * (b : G) = 1 at h
      change (x : G) * (y : G) = 1
      simpa only [← he, ← hf, Subgroup.subtype_apply] using h
    have heq' : Additive.ofMul x = -Additive.ofMul y := by
      exact mul_eq_one_iff_eq_inv.mp heq
    have hx0 : Additive.ofMul x = 0 :=
      Submodule.disjoint_def.mp hd _ hx (heq' ▸ W₂.neg_mem hy)
    have hx1 : x = 1 := hx0
    have hy1 : y = 1 := by simpa only [hx1, one_mul] using heq
    apply Prod.ext <;> apply Subtype.ext
    · change (a : G) = 1
      simpa only [hx1, OneMemClass.coe_one, map_one] using he.symm
    · change (b : G) = 1
      simpa only [hy1, OneMemClass.coe_one, map_one] using hf.symm
  · intro u
    obtain ⟨w, hw, he⟩ := u.property
    change Additive.ofMul w ∈ W at hw
    rw [hs] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
    refine ⟨(⟨a.toMul, ⟨a.toMul, ha, rfl⟩⟩, ⟨b.toMul, ⟨b.toMul, hb, rfl⟩⟩), ?_⟩
    apply Subtype.ext
    change (a.toMul : G) * (b.toMul : G) = u
    calc
      (a.toMul : G) * (b.toMul : G) = (w : G) :=
        congrArg (fun t : Additive (Uv z v) => (t.toMul : G)) hab
      _ = u := he

/-- The multiplication equivalence for the literal two order-four supports.
No coordinate is replaced by an abstractly isomorphic subgroup. -/
noncomputable def twoFactor_supportProduct [Finite G]
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    (factorSupport z v I (c.first.map I.subtype) ×
      factorSupport z v I (c.second.map I.subtype)) ≃* movedSubgroup z v I := by
  dsimp only
  let σ := FFFactors.offenderRepresentation (starRepresentation z v)
  let I := FFFactors.offenderActor (starRepresentation z v)
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  have hd := (twoFactor_spaces σ c e₁ e₂).1
  have hs := (twoFactor_spaces σ c e₁ e₂).2.1
  have h₁ := (twoFactor_factor_support z v c e₁ e₂ c.first (Or.inl rfl)).2.2
  have h₂ := (twoFactor_factor_support z v c e₁ e₂ c.second (Or.inr rfl)).2.2
  have ht : ambientSpace z v (moved σ ⊤) = movedSubgroup z v I := by
    rw [ambient_moved, top_map]
  exact ((MulEquiv.subgroupCongr (h₁.trans (ambient_moved z v c.first).symm)).prodCongr
    (MulEquiv.subgroupCongr (h₂.trans (ambient_moved z v c.second).symm))).trans
    ((MulEquiv.ofBijective (ambientSumMap z v _ _ _ hs)
      (ambientSumMap_bijective z v _ _ _ hd hs)).trans (MulEquiv.subgroupCongr ht))

/-- The product equivalence is multiplication of the original inclusions into G. -/
theorem twoFactor_supportProduct_apply [Finite G]
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (a : factorSupport z v (FFFactors.offenderActor (starRepresentation z v))
      (c.first.map (FFFactors.offenderActor (starRepresentation z v)).subtype))
    (b : factorSupport z v (FFFactors.offenderActor (starRepresentation z v))
      (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype)) :
    (twoFactor_supportProduct z v c e₁ e₂ (a, b) : G) = (a : G) * (b : G) := by
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
