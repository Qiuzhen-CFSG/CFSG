module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.RadicalConsequences
public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.Faithfulness
import Mathlib.Tactic

/-!
# The source section as a marked syntheme quotient

The source map of 13.8.4(5) is on the literal cosets of (H ∩ M)*.
An explicit actor equivalence carrying that subgroup to the plane parabolic
induces a coset equivalence. Reindexing binary functions along it intertwines
the source permutation representation with the named fifteen-syntheme action.
The source commutator noncentrality gives a moved vector, so the proved finite
kernel obstruction also supplies faithfulness of the actual quotient action.

Quadraticity then excludes the relative two-core when its image is D₀ in this
same marking. For A₆ the quadratic radical subgroup already has order at most
two. The plane and residual markings remain explicit inputs here: subgroup
orders or module dimensions do not establish them, and the duad residual must
not be substituted for the plane residual.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.4(5),(6) and Lemma 13.8.34, printed pp.947,968
(PDF pp.964,985). These are conditional source adapters, not the full lemma.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.MarkedQuotient

private def cosets {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (J : Subgroup A) (K : Subgroup B)
    (h : J.map e.toMonoidHom = K) : A ⧸ J ≃ B ⧸ K :=
  Quotient.congr e.toEquiv (by
    intro a b
    simp only [QuotientGroup.leftRel_apply]
    change a⁻¹ * b ∈ J ↔ (e a)⁻¹ * e b ∈ K
    simp only [← h, ← map_inv, ← map_mul, Subgroup.mem_map_equiv, e.symm_apply_apply])

private theorem cosets_equivariant {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (J : Subgroup A) (K : Subgroup B)
    (h : J.map e.toMonoidHom = K) (a : A) (x : A ⧸ J) :
    cosets e J K h (a • x) = e a • cosets e J K h x := by
  induction x using Quotient.inductionOn with | h b =>
    change QuotientGroup.mk (e (a * b)) = QuotientGroup.mk (e a * e b)
    rw [map_mul]

private def reindex {Ω Ψ : Type*} (c : Ω ≃ Ψ) :
    (Ψ → ZMod 2) ≃ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun v x := v (c x)
  invFun v x := v (c.symm x)
  left_inv v := by ext x; simp
  right_inv v := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem reindex_equivariant {A Ω Ψ : Type*} [Group A]
    [Fintype Ω] [Fintype Ψ] (p : A →* Equiv.Perm Ω) (q : A →* Equiv.Perm Ψ)
    (c : Ω ≃ Ψ) (hc : ∀ a x, c (p a x) = q a (c x)) (a : A) (v : Ψ → ZMod 2) :
    reindex c (BinaryPermutation.representation Ψ (q a) v) =
      BinaryPermutation.representation Ω (p a) (reindex c v) := by
  ext x
  change v ((q a).symm (c x)) = v (c ((p a).symm x))
  simpa only [map_inv, Equiv.Perm.inv_def] using congrArg v (hc a⁻¹ x).symm

private theorem transport_surjection {A B X : Type*} [Group A] [Group B]
    [AddCommGroup X] [Module (ZMod 2) X]
    (e : A ≃* B) (J : Subgroup A) (K : Subgroup B)
    [Fintype (A ⧸ J)] (h : J.map e.toMonoidHom = K)
    (p : B →* Equiv.Perm (Fin 15)) (c : B ⧸ K ≃ Fin 15)
    (hc : ∀ b x, c (b • x) = p b (c x))
    (σ : Representation (ZMod 2) A X)
    (f : Representation.IntertwiningMap
      ((BinaryPermutation.representation (A ⧸ J)).comp
        (MulAction.toPermHom A (A ⧸ J))) σ)
    (hf : Function.Surjective f) :
    ∃ f' : (Fin 15 → ZMod 2) →ₗ[ZMod 2] X, Function.Surjective f' ∧
      ∀ a v, f' (BinaryPermutation.representation (Fin 15) (p (e a)) v) = σ a (f' v) := by
  let d := (cosets e J K h).trans c
  have hd : ∀ a x, d (a • x) = p (e a) (d x) := by
    intro a x
    change c (cosets e J K h (a • x)) = _
    rw [cosets_equivariant, hc]
    rfl
  refine ⟨f.toLinearMap.comp (reindex d).toLinearMap, hf.comp (reindex d).surjective, ?_⟩
  intro a v
  change f (reindex d (BinaryPermutation.representation (Fin 15) (p (e a)) v)) = _
  have hh := reindex_equivariant (MulAction.toPermHom A (A ⧸ J))
    (p.comp e.toMonoidHom) d hd a v
  change reindex d (BinaryPermutation.representation (Fin 15) (p (e a)) v) = _ at hh
  rw [hh]
  exact Representation.IntertwiningMap.isIntertwining _ _ f a (reindex d v)

variable {G : Type*} [Group G]
open scoped commutatorElement IsMulCommutative

/-- A compatible action on the literal source section inherits the earlier
noncentrality commutator bound. -/
theorem noncentral (H V V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃) :
    ∃ g v, σ g v ≠ v := by
  classical
  by_contra! ht
  apply hnc
  rw [commutator_comm]
  apply commutator_le.mpr
  intro h hh x hx
  have he := (hσ ⟨h, hh⟩ ⟨x, hx⟩).symm.trans
    (ht (QuotientGroup.mk' (pCore 2 H) ⟨h, hh⟩)
      (Additive.ofMul (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V)) ⟨x, hx⟩)))
  have he' := congrArg Additive.toMul he
  have hm := QuotientGroup.eq_iff_div_mem.mp he'
  change (h * x * h⁻¹) / x ∈ Source.UH H V₃ at hm
  simpa only [commutatorElement_def, div_eq_mul_inv] using hm

open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.SixLetterRadicalDisplacement.PermutationQuotients

/-- The actual source coset quotient, reindexed along a specified S₆ plane
marking. The noncentrality witness is derived from the source commutator. -/
theorem symmetric_source (H M V V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    [Fintype (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))]
    (e : Source.Hstar H ≃* S)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ) :
    ∃ f : P →ₗ[ZMod 2] Additive (Source.Vsection H V V₃), Function.Surjective f ∧
      (∀ g v, f (rho (e g) v) = σ g (f v)) ∧ (∃ g v, σ g v ≠ v) ∧
      Function.Injective σ := by
  obtain ⟨f, hf⟩ := source_13_8_4_permutation_surjection H M V V₃
    hflag hindex hnc hnorm σ hσ
  obtain ⟨f', hf', he⟩ := transport_surjection e _ H2 hmark synthemeHom cosetEquiv
    cosetEquiv_equivariant σ f hf
  have hmove := noncentral H V V₃ σ hσ hnc
  exact ⟨f', hf', he, hmove, actor_faithful_of_noncentral_quotient e σ f' hf' he hmove⟩

/-- The same literal source construction with the alternating plane parabolic.
The coordinate action is the restriction of the named syntheme homomorphism. -/
theorem alternating_source (H M V V₃ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    [Fintype (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))]
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6))
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hσ : SectionConjugation H V V₃ σ) :
    ∃ f : P →ₗ[ZMod 2] Additive (Source.Vsection H V V₃), Function.Surjective f ∧
      (∀ g v, f (rhoA (e g) v) = σ g (f v)) ∧ (∃ g v, σ g v ≠ v) ∧
      Function.Injective σ := by
  obtain ⟨f, hf⟩ := source_13_8_4_permutation_surjection H M V V₃
    hflag hindex hnc hnorm σ hσ
  obtain ⟨f', hf', he⟩ := transport_surjection e _ _ hmark
    (synthemeHom.comp (alternatingGroup (Fin 6)).subtype) alternatingCosetEquiv
    alternatingCosetEquiv_equivariant σ f hf
  have hmove := noncentral H V V₃ σ hσ hnc
  exact ⟨f', hf', he, hmove, alternating_actor_faithful_of_noncentral_quotient e σ f' hf' he hmove⟩

open Representation.BinaryOffender
variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]

/-- Monotonicity of quadraticity excludes the marked relative two-core.
The core marking is an explicit obligation of the plane-residual identification. -/
theorem symmetric_core_not_le (H L₁ Vα : Subgroup G)
    (e : Source.Hstar H ≃* S) (σ : Representation (ZMod 2) (Source.Hstar H) Q)
    (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rho (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v)
    (hcore : ((Source.starImage H L₁).pCoreIn 2).map e.toMonoidHom = D0)
    (hq : IsQuadratic σ (Source.starImage H Vα)) :
    ¬ (Source.starImage H L₁).pCoreIn 2 ≤ Source.starImage H Vα := by
  intro h
  apply not_quadratic_D0 (σ.comp e.symm.toMonoidHom) f hf
    (fun g v => by simpa using heq (e.symm g) v)
    (by obtain ⟨g, v, hv⟩ := hnc; exact ⟨e g, v, by simpa using hv⟩)
  intro a ha b hb v
  have ha' : e.symm a ∈ (Source.starImage H L₁).pCoreIn 2 :=
    Subgroup.mem_map_equiv.mp (hcore.symm ▸ ha)
  have hb' : e.symm b ∈ (Source.starImage H L₁).pCoreIn 2 :=
    Subgroup.mem_map_equiv.mp (hcore.symm ▸ hb)
  exact hq _ (h ha') _ (h hb') v

/-- The corresponding obstruction for the intrinsic alternating radical. -/
theorem alternating_core_not_le (H L₁ Vα : Subgroup G)
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6))
    (σ : Representation (ZMod 2) (Source.Hstar H) Q)
    (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rhoA (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v)
    (hcore : ((Source.starImage H L₁).pCoreIn 2).map e.toMonoidHom = alternatingRadical)
    (hq : IsQuadratic σ (Source.starImage H Vα)) :
    ¬ (Source.starImage H L₁).pCoreIn 2 ≤ Source.starImage H Vα := by
  intro h
  apply not_quadratic_alternatingRadical (σ.comp e.symm.toMonoidHom) f hf
    (fun g v => by simpa using heq (e.symm g) v)
    (by obtain ⟨g, v, hv⟩ := hnc; exact ⟨e g, v, by simpa using hv⟩)
  intro a ha b hb v
  have ha' : e.symm a ∈ (Source.starImage H L₁).pCoreIn 2 :=
    Subgroup.mem_map_equiv.mp (hcore.symm ▸ ha)
  have hb' : e.symm b ∈ (Source.starImage H L₁).pCoreIn 2 :=
    Subgroup.mem_map_equiv.mp (hcore.symm ▸ hb)
  exact hq _ (h ha') _ (h hb') v

/-- In the alternating case a quadratic subgroup inside the marked radical
has order at most two, without an assumed core noncontainment. -/
theorem alternating_card_le_two (H Vα : Subgroup G)
    (e : Source.Hstar H ≃* alternatingGroup (Fin 6))
    (σ : Representation (ZMod 2) (Source.Hstar H) Q)
    (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rhoA (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v)
    (hq : IsQuadratic σ (Source.starImage H Vα))
    (hV : (Source.starImage H Vα).map e.toMonoidHom ≤ alternatingRadical) :
    Nat.card (Source.starImage H Vα) ≤ 2 := by
  have hc := alternating_card_le_two_of_quadratic (σ.comp e.symm.toMonoidHom) f hf
    (fun g v => by simpa using heq (e.symm g) v)
    (by obtain ⟨g, v, hv⟩ := hnc; exact ⟨e g, v, by simpa using hv⟩)
    ((Source.starImage H Vα).map e.toMonoidHom)
    (fun a ha b hb v => hq _ (Subgroup.mem_map_equiv.mp ha)
      _ (Subgroup.mem_map_equiv.mp hb) v) hV
  rwa [Subgroup.card_map_of_injective e.injective] at hc

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.MarkedQuotient
