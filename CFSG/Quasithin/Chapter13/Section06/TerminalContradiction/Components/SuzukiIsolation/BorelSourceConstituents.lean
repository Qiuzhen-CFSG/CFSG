module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceSemisimple
public import Theory.Representation.Suzuki.BorelConstituents
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Constituents

/-!
# Trivial and Steinberg constituents on the original central section

Each original V₃ seed is a sum of images of the trivial line and the full
Steinberg tensor for one compatible marking of A/O₂(A). The literal
component projection intertwines ambient H conjugation with automorphisms
of that marked quotient. Steinberg is invariant under those automorphisms,
so the H-span of the seeds remains within these two types.

The full original U_H/V₁ is therefore the sum of its trivial and Steinberg
type spans. Together with the proved source semisimplicity, this identifies
every simple constituent. The final application constructs F.11 for the
actual normal extra Suzuki component in the involution centralizer.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), §13.6,
printed p.918, and Notation 13.5.8, printed pp.934–935.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative TensorProduct MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source Section08 Ratio BenderSuzuki.MatrixGroups Representation
variable {G : Type*} [Group G]
  {H A : Subgroup G} (hAH : A ≤ H)

/-- The literal component map from its subgroup inside H to its marked Suzuki quotient. -/
def markedComponentProjection {m : ℕ}
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) : A.subgroupOf H →* SuzukiMatrixGroup m :=
  f.symm.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 A)).comp
    (subgroupOfEquivOfLe hAH).toMonoidHom)

theorem markedComponentProjection_surjective {m : ℕ}
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) :
    Function.Surjective (markedComponentProjection hAH f) :=
  f.symm.surjective.comp ((QuotientGroup.mk'_surjective (pCore 2 A)).comp
    (subgroupOfEquivOfLe hAH).surjective)

/-- The full tensor pulled back through the literal original component quotient. -/
def markedComponentSteinberg {m : ℕ} (K : Type*) [Field K] [Algebra (SuzukiNatural.F m) K]
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) :
    Representation K (A.subgroupOf H) (SuzukiSmallDegree.TensorSpace m K Finset.univ) :=
  (SuzukiSmallDegree.tensorRep m K Finset.univ).comp (markedComponentProjection hAH f)

/-- The pulled-back Steinberg action is irreducible on the actual component. -/
theorem markedComponentSteinberg_irreducible {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (SuzukiNatural.F m) K]
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) :
    (markedComponentSteinberg hAH K f).IsIrreducible :=
  (irreducible_comp_surjective_iff (markedComponentProjection hAH f)
    (markedComponentProjection_surjective hAH f) _).mpr
      (SuzukiSmallDegree.tensorRep_irreducible hm Finset.univ)

/-- The source quotient retains the exact ambient conjugation action. -/
theorem markedComponentProjection_conjugate {m : ℕ}
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) [(A.subgroupOf H).Normal] (x : H) :
    ∃ α : SuzukiMatrixGroup m ≃* SuzukiMatrixGroup m,
      ∀ a : A.subgroupOf H,
        markedComponentProjection hAH f (MulAut.conjNormal x a) =
          α (markedComponentProjection hAH f a) := by
  let e := subgroupOfEquivOfLe hAH
  let c : A ≃* A := (e.symm.trans (MulAut.conjNormal x)).trans e
  let q := QuotientGroup.congr (pCore 2 A) (pCore 2 A) c (pCore_map_iso 2 c)
  refine ⟨(f.trans q).trans f.symm,fun a => ?_⟩
  change f.symm (QuotientGroup.mk' (pCore 2 A) (e (MulAut.conjNormal x a))) =
    f.symm (q (f (f.symm (QuotientGroup.mk' (pCore 2 A) (e a)))))
  rw [f.apply_symm_apply]
  change _ = f.symm (QuotientGroup.mk' (pCore 2 A) (e (MulAut.conjNormal x (e.symm (e a)))))
  rw [e.symm_apply_apply]

/-- Ambient H conjugation preserves the actual pulled-back Steinberg constituent. -/
theorem markedComponentSteinberg_conjugate_equiv {m : ℕ} (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (SuzukiNatural.F m) K]
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) [(A.subgroupOf H).Normal] (x : H) :
    Nonempty (Representation.Equiv
      (Representation.conjugateRep (G := H) (markedComponentSteinberg hAH K f) x)
      (markedComponentSteinberg hAH K f)) := by
  obtain ⟨α,ha⟩ := markedComponentProjection_conjugate hAH f x
  obtain ⟨e⟩ := SuzukiSmallDegree.full_tensor_comp_equiv hm K α
  refine ⟨.mk e.toLinearEquiv (fun a => ?_)⟩
  change e.toLinearEquiv.toLinearMap ∘ₗ
      SuzukiSmallDegree.tensorRep m K Finset.univ
        (markedComponentProjection hAH f (MulAut.conjNormal x a)) = _
  rw [ha]
  exact e.isIntertwining' (markedComponentProjection hAH f a)


variable [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hHA : H ≤ normalizer (A : Set G))
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
attribute [local instance] sourceSpanCommGroup

include d hk hHA in
set_option backward.isDefEq.respectTransparency false in
/-- Every literal scalar seed is a sum of trivial and Steinberg images for one
compatible marking of the actual component quotient. -/
theorem source_pair_component_range_sum
    (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      ∀ a : V₃,
        ∃ f₀ : (trivial K (A.subgroupOf H) K).IntertwiningMap
          ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype),
        ∃ f₁ : (markedComponentSteinberg hAH K f).IntertwiningMap
          ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype),
        (1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) a ∈ f₀.range ⊔ f₁.range := by
  obtain ⟨f,hfix⟩ := source_pair_borel_marking hn hk hAH hHA d hF hz hAC hm e
  refine ⟨f,fun a => ?_⟩
  have ha : ∀ g ∈ SuzukiBorelSubgroup m,
      markedExtendedComponentRepresentation hn hk hAH hHA K f g
        ((1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) a) =
          (1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) a := by
    intro g hg
    change (extendScalars K (componentQuotientRepresentation hn hk hAH hHA)) (f g)
      ((1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) a) = _
    rw [extendScalars_apply,LinearMap.baseChange_tmul,hfix a g hg]
  obtain ⟨f₀,f₁,ha⟩ := SuzukiSmallDegree.borel_fixed_range_sum hm _ _ ha
  let p := markedComponentProjection hAH f
  have he := markedExtendedComponentRepresentation_comp hn hk hAH hHA K f
  change (markedExtendedComponentRepresentation hn hk hAH hHA K f).comp p = _ at he
  rw [← he]
  let g₀ : (trivial K (A.subgroupOf H) K).IntertwiningMap
      ((markedExtendedComponentRepresentation hn hk hAH hHA K f).comp p) := {
    toLinearMap := f₀.toLinearMap
    isIntertwining' b := f₀.isIntertwining' (p b) }
  let g₁ : (markedComponentSteinberg hAH K f).IntertwiningMap
      ((markedExtendedComponentRepresentation hn hk hAH hHA K f).comp p) := {
    toLinearMap := f₁.toLinearMap
    isIntertwining' b := f₁.isIntertwining' (p b) }
  exact ⟨g₀,g₁,ha⟩


include d hk hHA in
set_option backward.isDefEq.respectTransparency false in
/-- In a compatible original quotient marking, trivial and full Steinberg
images span the entire component restriction, and are its only irreducible
constituent types. -/
theorem source_pair_component_constituents
    (hF : HypothesisF11 ![L,A] (T : Subgroup G))
    {z : G} (hz : zpowers z = V₁) (hAC : A ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (trivial K (A.subgroupOf H) K) ⊔
        typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (markedComponentSteinberg hAH K f) = ⊤ ∧
      ∀ J : Subrepresentation
          ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype),
        IsAtom J →
        Nonempty (J.toRepresentation.Equiv (trivial K (A.subgroupOf H) K)) ∨
          Nonempty (J.toRepresentation.Equiv (markedComponentSteinberg hAH K f)) := by
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHA
  obtain ⟨f,hs⟩ := source_pair_component_range_sum hAH hn hk hHA d hF hz hAC hm e K
  have ht := markedComponentSteinberg_conjugate_equiv hAH hm K f
  have htop := Ratio.extendScalars_typeSpan_sup_eq_top hn K (A.subgroupOf H)
    (markedComponentSteinberg hAH K f) ht hs
  refine ⟨f,htop,fun J hJ => ?_⟩
  let := markedComponentSteinberg_irreducible hAH hm K f
  let := source_pair_component_semisimple hn hk hAH hHA d hF hz hAC hm e K
  exact Ratio.extendScalars_constituent_of_seed_ranges hn K (A.subgroupOf H)
    (markedComponentSteinberg hAH K f) ht hs J hJ


include d hk in
set_option backward.isDefEq.respectTransparency false in
/-- The original normal extra component has only the trivial and full Suzuki
Steinberg types on U_H/V₁, with its literal quotient map retained. -/
theorem normal_component_source_constituents
    {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal]
    (hDH : D.map (centralizer ({z} : Set G)).subtype ≤ H)
    {m : ℕ} (hm : 1 ≤ m) (e : (D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m)
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G))
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Algebra (SuzukiNatural.F m) K] :
    let A := D.map (centralizer ({z} : Set G)).subtype
    ∃ f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A),
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (trivial K (A.subgroupOf H) K) ⊔
        typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype)
          (markedComponentSteinberg hDH K f) = ⊤ ∧
      ∀ J : Subrepresentation
          ((extendScalars K (representation H V₃ V₁ hn)).comp (A.subgroupOf H).subtype),
        IsAtom J →
        Nonempty (J.toRepresentation.Equiv (trivial K (A.subgroupOf H) K)) ∨
          Nonempty (J.toRepresentation.Equiv (markedComponentSteinberg hDH K f)) := by
  let A := D.map (centralizer ({z} : Set G)).subtype
  have hHC : H ≤ centralizer ({z} : Set G) := by
    have he : centralizer (V₁ : Set G) = centralizer ({z} : Set G) := by
      rw [← hz, zpowers_eq_closure, centralizer_closure]
    rw [← he]
    exact hn.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
  have hHA : H ≤ normalizer (A : Set G) := hHC.trans (by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      D.le_normalizer_map (centralizer ({z} : Set G)).subtype)
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  exact source_pair_component_constituents hDH hn hk hHA d
    (source_A5_suzuki_pair_F11 d hz D e hout h25) hz (map_subtype_le D) hm
    (eQ.symm.trans e) K

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
