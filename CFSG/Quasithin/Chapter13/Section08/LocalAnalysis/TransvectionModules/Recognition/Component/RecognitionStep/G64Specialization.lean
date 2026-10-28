module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Displacement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Lift
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Perfect
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.SixExtension

/-!
# The self-generated specialization of G.6.4

The universal G.6.4 theorem is kept as an explicit premise at this boundary.
Its contract is the source contract: it retains the SQTK cover, the faithful
binary G.6.1 action, the involution and displacement-rank bound, the generated
module, all three concrete factor/module alternatives, and the two-factor
extension.  The specialization below uses the actual self-generated actor.
In that situation the marked transvection belongs to the first direct factor;
normality of that factor in the normal closure then forces the whole actor into
that factor, excluding the nontrivial second factor.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, G.6.1--4,
printed pp.345--346; application in 13.8.5, printed p.947.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

universe u

variable {A E : Type u} [Group A]
  [AddCommGroup E] [Module (ZMod 2) E]

/-! The concrete alternatives for one factor.  This is deliberately separate
from `ActorModel`: the universal theorem below does not assume or conclude the
specialized recognition predicate. -/

def G64SingleAlternative (ρ : Representation (ZMod 2) A E) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ HasActionModel ρ (linearRepresentation n)) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧
    HasActionModel ρ (BinaryPermutation.naturalRepresentation (Fin n))) ∨
  (∃ n, (n = 6 ∨ n = 8) ∧
    HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin n)))

/-! A factor model retains its actual invariant module and the equivariant
group/module identifications.  It is used in the two-factor clause so the
universal interface does not discard the source's module alternatives. -/

def G64FactorAlternativeAt (ρ : Representation (ZMod 2) A E) (K : Subgroup A)
    (W : Submodule (ZMod 2) E) : Prop :=
  ∃ hW : (∀ k : K, ∀ v : W, ρ (k : A) v ∈ W),
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧
        ∃ (eK : K ≃* BinaryLinear.GL (Fin n → ZMod 2))
          (eW : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)),
          ∀ (k : K) (v : W),
            eW ⟨ρ (k : A) v, hW k v⟩ =
              linearRepresentation n (eK k) (eW v)) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧
        ∃ (eK : K ≃* Equiv.Perm (Fin n))
          (eW : W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin n)),
          ∀ (k : K) (v : W),
            eW ⟨ρ (k : A) v, hW k v⟩ =
              BinaryPermutation.naturalRepresentation (Fin n) (eK k) (eW v)) ∨
  (∃ n, (n = 6 ∨ n = 8) ∧
        ∃ (eK : K ≃* Equiv.Perm (Fin n))
          (eW : W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin n)),
          ∀ (k : K) (v : W),
            eW ⟨ρ (k : A) v, hW k v⟩ =
              BinaryPermutation.coreRepresentation (Fin n) (eK k) (eW v))

def G64FactorModel (ρ : Representation (ZMod 2) A E) (K : Subgroup A) : Prop :=
  ∃ W : Submodule (ZMod 2) E,
    G64FactorAlternativeAt ρ K W

/-! The small factor groups in G.6.4(3)(ii). -/

def G64SmallFactor (K : Subgroup A) : Prop :=
  Nonempty (K ≃* BinaryLinear.GL (Fin 2 → ZMod 2)) ∨
  Nonempty (K ≃* BinaryLinear.GL (Fin 3 → ZMod 2)) ∨
  Nonempty (K ≃* Equiv.Perm (Fin 5))

structure G64OneFactorData (ρ : Representation (ZMod 2) A E) (t : A) where
  K : Subgroup A
  W : Submodule (ZMod 2) E
  K_eq : K = normalClosure ({t} : Set A)
  W_eq : W = ⊤
  model : G64FactorAlternativeAt ρ K W

/-! The two-factor part of the universal source conclusion.  Normality is
stated relative to the generated actor `K`; after self-generation this is
exactly the normality needed for the closure argument. -/

structure G64TwoFactorData (ρ : Representation (ZMod 2) A E) (t : A) where
  K1 : Subgroup A
  K2 : Subgroup A
  K1_le : K1 ≤ normalClosure ({t} : Set A)
  K2_le : K2 ≤ normalClosure ({t} : Set A)
  direct_product : K1 ⊔ K2 = normalClosure ({t} : Set A)
  trivial_intersection : K1 ⊓ K2 = ⊥
  commuting_factors : ⁅K1, K2⁆ = ⊥
  K1_normal_in_closure : ∀ x ∈ K1, ∀ g ∈ normalClosure ({t} : Set A),
    g * x * g⁻¹ ∈ K1
  K2_normal_in_closure : ∀ x ∈ K2, ∀ g ∈ normalClosure ({t} : Set A),
    g * x * g⁻¹ ∈ K2
  transvection_in_first : t ∈ K1
  second_nontrivial : K2 ≠ ⊥
  factor_one_model : G64FactorModel ρ K1
  factor_two_model : G64FactorModel ρ K2
  factor_one_small : G64SmallFactor K1
  factor_two_small : G64SmallFactor K2
  extension : ∃ u : A, u ^ 2 = 1 ∧
    normalClosure ({t} : Set A) ⊔ zpowers u = ⊤ ∧
    (∀ x ∈ K1, u * x * u⁻¹ ∈ K2) ∧
    (∀ x ∈ K2, u * x * u⁻¹ ∈ K1)

def G64UniversalConclusion (ρ : Representation (ZMod 2) A E) (t : A) : Prop :=
  Nonempty (G64OneFactorData ρ t) ∨ Nonempty (G64TwoFactorData ρ t)

/-! The exact universal premise used by the specialization.  The displacement
span is the source condition `V = <[V,a]^G>` and the rank expression is the
dimension of `[V,a]`.  The cover and its surjection are explicit arguments. -/

def G64Universal (κ : GroupClass.{u})
    (ρ : Representation (ZMod 2) A E) (t : A) [Finite A] : Prop :=
  ∀ {Cover : Type u} [Group Cover] [Finite Cover],
    (q : Cover →* A) → IsSQTK κ Cover → Function.Surjective q →
    pCore 2 A = ⊥ → Function.Injective ρ → t ^ 2 = 1 →
    t ≠ 1 →
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2 →
    displacementOrbit ρ t = ⊤ → G64UniversalConclusion ρ t

private theorem g64_rank_of_transvection
    (ρ : Representation (ZMod 2) A E)
    {t : A} (ht : IsTransvection ρ t) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2 := by
  rw [transvection_displacement_rank ht]
  decide

private theorem g64_normalClosure_le_factor
    {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : Representation (ZMod 2) A E} {t : A}
    (hgen : normalClosure ({t} : Set A) = ⊤)
    (d : G64TwoFactorData ρ t) : normalClosure ({t} : Set A) ≤ d.K1 := by
  have hN : d.K1.Normal :=
    ⟨fun x hx g => d.K1_normal_in_closure x hx g (by
      rw [hgen]
      exact mem_top g)⟩
  exact @normalClosure_le_normal A _ ({t} : Set A) d.K1 hN
    (Set.singleton_subset_iff.mpr d.transvection_in_first)

private theorem g64_one_factor_to_single
    {ρ : Representation (ZMod 2) A E} {t : A}
    (hgen : normalClosure ({t} : Set A) = ⊤)
    (d : G64OneFactorData ρ t) : G64SingleAlternative ρ := by
  obtain ⟨K, W, hKeq, hWeq, hm⟩ := d
  have hK : K = ⊤ := hKeq.trans hgen
  subst K
  subst W
  rw [hgen] at hm
  rcases hm with ⟨hW, hlin | hnat | hcore⟩
  · obtain ⟨n, hnlo, hnhi, eK, eW, he⟩ := hlin
    refine Or.inl ⟨n, hnlo, hnhi, ?_⟩
    refine ⟨Subgroup.topEquiv.symm.trans eK, Submodule.topEquiv.symm.trans eW, ?_⟩
    intro a v
    simpa [Subgroup.topEquiv, Submodule.topEquiv, Submonoid.topEquiv,
      MulEquiv.trans_apply, LinearEquiv.trans_apply] using
      he (Subgroup.topEquiv.symm a) (Submodule.topEquiv.symm v)
  · obtain ⟨n, hnlo, hnhi, eK, eW, he⟩ := hnat
    refine Or.inr (Or.inl ⟨n, hnlo, hnhi, ?_⟩)
    refine ⟨Subgroup.topEquiv.symm.trans eK, Submodule.topEquiv.symm.trans eW, ?_⟩
    intro a v
    simpa [Subgroup.topEquiv, Submodule.topEquiv, Submonoid.topEquiv,
      MulEquiv.trans_apply, LinearEquiv.trans_apply] using
      he (Subgroup.topEquiv.symm a) (Submodule.topEquiv.symm v)
  · obtain ⟨n, hn, eK, eW, he⟩ := hcore
    refine Or.inr (Or.inr ⟨n, hn, ?_⟩)
    refine ⟨Subgroup.topEquiv.symm.trans eK, Submodule.topEquiv.symm.trans eW, ?_⟩
    intro a v
    simpa [Subgroup.topEquiv, Submodule.topEquiv, Submonoid.topEquiv,
      MulEquiv.trans_apply, LinearEquiv.trans_apply] using
      he (Subgroup.topEquiv.symm a) (Submodule.topEquiv.symm v)

theorem actorModel_of_self_generated_g64
    {κ : GroupClass.{u}} [Finite A] (ρ : Representation (ZMod 2) A E) {t : A}
    {Cover : Type u} [Group Cover] [Finite Cover] (q : Cover →* A)
    (hcover : IsSQTK κ Cover) (hq : Function.Surjective q)
    (hcore : pCore 2 A = ⊥) (hρ : Function.Injective ρ)
    (ht : IsTransvection ρ t)
    (hgen : normalClosure ({t} : Set A) = ⊤)
    (horbit : displacementOrbit ρ t = ⊤)
    (hG64 : G64Universal κ ρ t) :
    ActorModel ρ := by
  have ht2 : t ^ 2 = 1 := transvection_square hρ ht
  have hrank := g64_rank_of_transvection ρ ht
  rcases hG64 q hcover hq hcore hρ ht2 ht.ne_one hrank horbit with hd | hd
  · obtain ⟨d⟩ := hd
    have hsingle := g64_one_factor_to_single hgen d
    simpa only [G64SingleAlternative, ActorModel] using hsingle
  · obtain ⟨d⟩ := hd
    have hle : normalClosure ({t} : Set A) ≤ d.K1 :=
      g64_normalClosure_le_factor hgen d
    have hK1 : d.K1 = ⊤ := top_unique (hgen ▸ hle)
    have hK2 : d.K2 = ⊥ := by
      have hi := d.trivial_intersection
      simpa only [hK1, top_inf_eq] using hi
    exact (d.second_nontrivial hK2).elim

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
