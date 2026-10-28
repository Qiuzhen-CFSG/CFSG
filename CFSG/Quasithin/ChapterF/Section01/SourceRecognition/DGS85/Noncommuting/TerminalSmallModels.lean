module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalModelBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalModuleSource
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.Field.ULift

/-!
# The only remaining terminal quotients are the field-two unitary groups

Apply the model square bounds to the very same V_t/Z_t representation,
Sylow image and nontrivial radius-one actor constructed in `TerminalModule`.
The intrinsic core equals the embedded graph core, so the actual source
catalogue applies without a model-selection premise. The path exclusion
then removes PSL₂, transporting its field to the original universe while
preserving the literal quotient isomorphism.

The output retains the constructed section, fixed-space generation,
faithful Sylow action, quadratic actor and index bound. It identifies the
remaining quotient as actual SU₃(2) or PSU₃(2); it does not yet exclude
these two groups or prove b=2.
Source: DGS, *Groups and Graphs* (1985), (7.5)(5) and final comparison,
pp.130--131. The reduced F1.11 application is in `TerminalSmallSource`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem model_transport {D H : Type*} [Group D] [Group H]
    (hm : IsRankOneModel D) (e : H ≃* D) : IsRankOneModel H := by
  cases hm with
  | linear n hn he => exact .linear n hn (he.of_mulEquiv e)
  | suzuki m he => exact .suzuki m ⟨e.trans he.some⟩
  | projective_unitary n hn he => exact .projective_unitary n hn (he.of_mulEquiv e)
  | special_unitary n hn he =>
    obtain ⟨F,hF,hfin,J,hc,hconj,⟨f⟩⟩ := he
    exact .special_unitary n hn ⟨F,hF,hfin,J,hc,hconj,⟨e.trans f⟩⟩
  | dihedral he => exact .dihedral ⟨e.trans he.some⟩

private theorem linear_source_lift {D : Type u} [Group D]
    {n : ℕ} (_hn : 0 < n) (h : ClassicalGroup.IsPSL D 2 (2^n)) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      Nonempty (D ≃* SL(2,k)) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let k := ULift.{u} F
  let f : SL(2,F) ≃* SL(2,k) := Atlas.fieldEquivSL 2 ULift.ringEquiv.symm
  exact ⟨k,inferInstance,inferInstance,inferInstance,
    ⟨(e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).trans f⟩⟩

/-- The long epsilon-two branch retains its actual section on a field-two unitary quotient. -/
theorem graph_epsilonTwo_terminal_small_unitary
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    (hb : 2 < b (family P)) :
    ∃ t y : Vertex (family P), ∃ hty : (graph (family P)).Adj t y,
      let := finite_endpoints h
      let c := d t y hty
      letI : Finite c.Pstar := Finite.of_injective
        (inclusion c.Pstar_le) (inclusion_injective _)
      letI := graph_local_core_normal t c
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      ∃ σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) W,
        Nonempty (BinaryConjugationSection c.Pstar (V (family P) t 1) (Z (family P) t)
          (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)))) ∧
        Nontrivial W ∧ Finite W ∧
        let π := QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)
        let T := c.sylow.mapSurjective (QuotientGroup.mk'_surjective
          ((Q (family P) t).subgroupOf c.Pstar))
        GeneratedByFixedSpace σ T ∧ Disjoint σ.ker (T : Subgroup _) ∧
        (∃ a : Vertex (family P), (graph (family P)).Adj v a ∧
          V (family P) a 1 ≤ c.Pstar ∧
          let A := ((V (family P) a 1).subgroupOf c.Pstar).map π
          A ≤ T ∧ 1 < Nat.card A ∧ IsQuadratic σ A ∧
          Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) ∧
        (IsSU (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) 3 2 ∨
          ClassicalGroup.IsPSU (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) 3 2) := by
  obtain ⟨t,y,hty,W,hadd,hmodule,σ,hs,hnt,hfin,hgen,hfaith,hactor,_,hnot⟩ :=
    graph_epsilonTwo_terminal_module h hB hS L hcov d hstar hodd hdich hob
      hc hne hvu hdu hepsilon hnat₀ hnat₁ hsyl hbranch hb
  let := hadd
  let := hmodule
  let := hfin
  let := finite_endpoints h
  let c := d t y hty
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let := graph_local_core_normal t c
  have hcoreEq : (Q (family P) t).subgroupOf c.Pstar = pCore 2 c.Pstar := by
    rw [show Q (family P) t = c.Pstar.pCoreIn 2 from c.same_core.symm]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  let eQ := QuotientGroup.quotientMulEquivOfEq hcoreEq
  have hm := model_transport c.quotient eQ
  have hsmall : IsSU (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) 3 2 ∨
      ClassicalGroup.IsPSU (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) 3 2 := by
    obtain ⟨a,_,_,hAT,hAc,hq,hbound⟩ := hactor
    rcases terminal_action_model_alternatives hm σ _ _ hAT hAc hq hgen hfaith hbound with
      ⟨n,hn,he⟩ | he
    · obtain ⟨k,hk,hkf,hkc,⟨e⟩⟩ := linear_source_lift hn he
      let := hk
      let := hkf
      let := hkc
      have he' : Nonempty ((c.Pstar ⧸ pCore 2 c.Pstar) ≃* SL(2,k)) := ⟨eQ.symm.trans e⟩
      change Nonempty (((d t y hty).Pstar ⧸ pCore 2 (d t y hty).Pstar) ≃* SL(2,k)) at he'
      rw [hstar] at he'
      exact (hnot k hk hkf hkc he').elim
    · exact he
  exact ⟨t,y,hty,W,hadd,hmodule,σ,hs,hnt,hfin,hgen,hfaith,hactor,hsmall⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
