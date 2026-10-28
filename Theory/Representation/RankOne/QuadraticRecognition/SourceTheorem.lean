module
public import Theory.Representation.RankOne.QuadraticRecognition.SmallUnitary
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiAllActors
public import Theory.Representation.RankOne.QuadraticRecognition.SL2ProperActor

/-!
# Corrected binary rank-one quadratic module recognition

For the complete prime-two Chapter 5 catalogue, a faithful quadratic actor
has order at most its fixed-space index. Strictness against the actor's
square excludes every Suzuki and unitary row. In the SL₂ row, Sylow fixed
space generation and vanishing residual fixed space give irreducibility,
full-Sylow quadraticity and natural coordinates. The output retains the
field, actual group isomorphism, unchanged vectors, quotient, and all
natural-module consequences needed in the graph argument.

The model catalogue contains actual isomorphisms to SL₂, Suzuki, SU₃ or
PSU₃ carriers, including the small source parameters; it has no D₁₀ row.
The residual is Subgroup.pResidual 2, namely O². The published correction
V=⟨C_V(S)^G⟩ is an explicit hypothesis, used in the recognition proof.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985), (5.12),
pp.113–115, catalogue p.104 and natural-module definition/consequences
pp.112–113, with Stroth's review correction. CriticalRecognition gives the
literal (7.1)/(9.3) application to Z/(Z∩Z(L)).
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
universe u v

/-- The prime-two Chapter 5 catalogue, with actual matrix model isomorphisms.
PSL₂ equals SL₂ in characteristic two. The parameter zero Suzuki model is
Sz(2); unitary degree one is retained. D₁₀ is not in this catalogue. -/
inductive BinaryRankOneModel (G : Type u) [Group G] : Type (u+1) where
  | sl2 (F : Type u) [Field F] [Finite F] [CharP F 2]
      (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = 2^n)
      (e : G ≃* SL(2,F)) : BinaryRankOneModel G
  | suzuki (m : ℕ) (e : G ≃* SuzukiMatrixGroup m) : BinaryRankOneModel G
  | su3 (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F)
      (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
      (hconj : ∀ x, J.conj x=x^(2^n))
      (e : G ≃* J.specialSubgroup) : BinaryRankOneModel G
  | psu3 (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F)
      (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
      (hconj : ∀ x, J.conj x=x^(2^n))
      (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) : BinaryRankOneModel G

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

/-- A natural module is marked by its actual defining field, group equivalence,
unchanged vectors and equivariant coordinates. The p.112 source definition
and every p.113 consequence refer to this same action and Sylow subgroup. -/
@[expose] def NaturalRealization (ρ : Representation (ZMod 2) G V) (S : Sylow 2 G) : Prop :=
  ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
    (n : ℕ), 0 < n ∧ Nat.card F = 2^n ∧ ∃ e : G ≃* SL(2,F),
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let σ : Representation (ZMod 2) SL(2,F) V := ρ.comp e.symm.toMonoidHom
    let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    IsSourceNatural σ T n ∧ σ.IsIrreducible ∧
    Nat.card (fixedSpace σ T) = 2^n ∧
    (∀ t ∈ (T : Subgroup SL(2,F)), t ≠ 1 → fixedSpace σ (zpowers t) = fixedSpace σ T) ∧
    (∀ g ∉ normalizer (T : Set SL(2,F)),
      IsCompl (fixedSpace σ T) (fixedSpace σ (g • T : Sylow 2 SL(2,F)))) ∧
    (∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g : G, ρ g v = w) ∧
    ∃ E : V ≃ₗ[ZMod 2] (Fin 2 → F), ∀ g v, E (ρ g v) = Matrix.mulVec (e g).val (E v)

omit [Finite G] [Finite V] in
private theorem fixedSpace_transport {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) G V) (e : G ≃* H) (A : Subgroup G) :
    fixedSpace (ρ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) = fixedSpace ρ A := by
  rw [fixedSpace_comp_map,Subgroup.map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext a; simp
  rw [he,Subgroup.map_id]

omit [Finite G] [Finite V] in
private theorem quadratic_transport {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) G V) (e : G ≃* H) (A : Subgroup G)
    (hq : IsQuadratic ρ A) : IsQuadratic (ρ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) := by
  rintro a ⟨b,hb,rfl⟩ c ⟨d,hd,rfl⟩ v
  simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hq b hb d hd v

omit [Finite V] in
private theorem generation_transport {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) G V) (e : G ≃* H) (S : Sylow 2 G)
    (hg : GeneratedByFixedSpace ρ S) :
    GeneratedByFixedSpace (ρ.comp e.symm.toMonoidHom)
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  exact generatedByFixedSpace_of_equivariant_surjection ρ (ρ.comp e.symm.toMonoidHom)
    e.toMonoidHom LinearMap.id Function.surjective_id (by intro g v; simp) S hg

omit [Finite G] [Finite V] in
private theorem global_fixed_transport {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) G V) (e : G ≃* H) (hfix : fixedSpace ρ ⊤ = ⊥) :
    fixedSpace (ρ.comp e.symm.toMonoidHom) ⊤ = ⊥ := by
  rw [fixedSpace_comp_map,Subgroup.map_top_of_surjective _ e.symm.surjective,hfix]

/-- Corrected DGS85 (5.12), at the source prime two and on every actual
Chapter 5 model, including all small parameters. The residual is O²,
not O₂ or O^{2′}; corrected generation is from the given Sylow fixed space. -/
theorem binary_rank_one_bound_and_recognition
    (M : BinaryRankOneModel G) (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (S : Sylow 2 G) (A : Subgroup G) (hAS : A ≤ S)
    (hq : IsQuadratic ρ A) (hg : GeneratedByFixedSpace ρ S)
    (hres : fixedSpace ρ (pResidual 2 G) = ⊥) :
    Nat.card A ≤ Nat.card (V ⧸ fixedSpace ρ A) ∧
    (Nat.card (V ⧸ fixedSpace ρ A) < Nat.card A ^ 2 → NaturalRealization ρ S) := by
  have hfix : fixedSpace ρ ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone ρ le_top).trans hres.le)
  cases M with
  | sl2 F n hn hcard e =>
    let σ : Representation (ZMod 2) SL(2,F) V := ρ.comp e.symm.toMonoidHom
    let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let B := A.map e.toMonoidHom
    have hBT : B ≤ T := Subgroup.map_mono hAS
    have hfσ : Function.Injective σ := hf.comp e.symm.injective
    have hgσ := generation_transport ρ e S hg
    have hxσ := global_fixed_transport ρ e hfix
    have hqσ := quadratic_transport ρ e A hq
    have hbound := sl2_actor_bound σ hfσ T B hBT hcard
    have hfixed : fixedSpace σ B = fixedSpace ρ A := fixedSpace_transport ρ e A
    have hBc : Nat.card B = Nat.card A := Subgroup.card_map_of_injective e.injective
    refine ⟨?_,?_⟩
    · simpa only [hBc,hfixed] using hbound
    · intro hstrict
      have hs : Nat.card (V ⧸ fixedSpace σ B) < Nat.card B^2 := by
        simpa only [hBc,hfixed] using hstrict
      let : Algebra (ZMod 2) F := ZMod.algebra F 2
      obtain ⟨hnat,E,he⟩ := sl2_strict_actor_natural σ hfσ T B hBT hqσ hgσ hxσ hcard hs
      obtain ⟨hc,hu⟩ := sl2_natural_fixed_spaces σ T hnat.2.2 hgσ hxσ E
      refine ⟨F,inferInstance,inferInstance,inferInstance,n,hn,hcard,e,
        hnat,irreducible_of_natural_coordinates σ E he,hc.trans hcard,hu,?_,?_,E,?_⟩
      · intro g hgn
        exact sl2_sylow_fixed_isCompl σ T (g • T)
          (fun h => hgn (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)) hnat.2.2 hgσ hxσ
      · intro v w hv hw
        obtain ⟨g,hgv⟩ := transitive_of_natural_coordinates σ E he hv hw
        exact ⟨e.symm g,hgv⟩
      · intro g v
        simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using he (e g) v
  | suzuki m e =>
    have hb := suzuki_all_square_bound m (ρ.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) (A.map e.toMonoidHom)
      (Subgroup.map_mono hAS) (quadratic_transport ρ e A hq)
    rw [fixedSpace_transport,Subgroup.card_map_of_injective e.injective] at hb
    exact ⟨(Nat.le_self_pow (by decide) _).trans hb,fun h => False.elim (Nat.not_lt_of_ge hb h)⟩
  | su3 F J n hn hcard hconj e =>
    have hb := su3_all_quadratic_bounds J hn hcard hconj (ρ.comp e.symm.toMonoidHom)
      (hf.comp e.symm.injective) (global_fixed_transport ρ e hfix)
      (A.map e.toMonoidHom) (quadratic_transport ρ e A hq)
    rw [fixedSpace_transport,Subgroup.card_map_of_injective e.injective] at hb
    exact ⟨hb.1,fun h => False.elim (Nat.not_lt_of_ge hb.2 h)⟩
  | psu3 F J n hn hcard hconj e =>
    have hb := psu3_all_quadratic_bounds J hn hcard hconj (ρ.comp e.symm.toMonoidHom)
      (hf.comp e.symm.injective) (global_fixed_transport ρ e hfix)
      (A.map e.toMonoidHom) (quadratic_transport ρ e A hq)
    rw [fixedSpace_transport,Subgroup.card_map_of_injective e.injective] at hb
    exact ⟨hb.1,fun h => False.elim (Nat.not_lt_of_ge hb.2 h)⟩
end Representation.RankOne.QuadraticRecognition
