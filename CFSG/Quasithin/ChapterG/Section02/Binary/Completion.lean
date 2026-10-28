module

public import CFSG.Quasithin.ChapterG.Section02.Binary.SourceAssembly
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition

/-!
# All seven binary almost-special conclusions

The natural C₃ action recognizes the original star quotient as S₃.
The original two conjugates generate it, and the two-residual hypothesis
lifts generation to I=LU. These facts discharge the remaining premises of
the source layer, core-factorization, natural-module and order arguments.

The action on the literal S/S₂ is pulled back from the actual join L*U*
through the original star map. The resulting natural tensor, complementary
marked factors, fixed spaces and order formula use the same multiplicity.
Only U≤T and Φ(U)≤V₁ from G.2.2 remain explicit; their discharge belongs
to the G.2 assembly owner through CentralClosure.

Source: Aschbacher–Smith, G.2.3, printed pp.333–334.
-/

@[expose] public section
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise _root_.TensorProduct

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

/-- The original star quotient restricted to I, with its actual L*U* codomain. -/
def binarySourceJoinProjection (D : Setup G) (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) : D.I g →* (D.star D.L ⊔ D.star D.U : Subgroup D.Star) :=
  (D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL)).codRestrict _ fun x => by
    rw [← binary_star_sup D.L D.U le_sup_left (hUT.trans le_sup_right)]
    apply binary_star_mono (binary_I_le_join hgL)
    rw [← binaryStarRestriction_range (D.I g) (binary_I_le_LT hUT hgL)]
    exact ⟨x, rfl⟩

omit [Finite G] in
/-- Fixing the actual U* image is equivalent to fixing all original U lifts. -/
theorem binarySourceJoinProjection_fixed_iff (D : Setup G) (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L) {M : Type*}
    (f : (D.star D.L ⊔ D.star D.U : Subgroup D.Star) → M → M) (v : M) :
    (∀ a : (D.star D.L ⊔ D.star D.U : Subgroup D.Star),
      a.val ∈ D.star D.U → f a v = v) ↔
    (∀ u : D.I g, (u : G) ∈ D.U → f (D.binarySourceJoinProjection hUT g hgL u) v = v) := by
  constructor
  · intro hv u hu
    apply hv
    exact ⟨inclusion (binary_I_le_LT hUT hgL) u, hu, rfl⟩
  · intro hv a ha
    obtain ⟨u, hu, heu⟩ := ha
    let ui : D.I g := ⟨u, (show D.U ≤ D.I g from le_sup_left) hu⟩
    have he : D.binarySourceJoinProjection hUT g hgL ui = a := Subtype.ext heu
    simpa only [he] using hv ui hu

/-- Clause (1)'s equivalence, induced by the natural action of the original star quotient. -/
noncomputable def binarySourceJoinEquiv (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    (D.star D.L ⊔ D.star D.U : Subgroup D.Star) ≃* S₃ :=
  binaryStarJoinEquiv hUT g hgL (binaryStarEquiv h.toBaseHypothesis b hUT)
    (binary_source_star_generation h b hUT g hgL hgN)

/-- The core quotient action factors through the literal star projection. -/
theorem binary_source_projection (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    D.binaryCoreProjection g (binarySourceCoreEquiv h b hUT g hgL hgN) =
      (binarySourceJoinEquiv h b hUT g hgL hgN).toMonoidHom.comp
        (D.binarySourceJoinProjection hUT g hgL) := by
  rw [D.binaryCoreProjection_eq]
  apply MonoidHom.ext
  intro x
  rfl

/-- The source projection onto L*U* is surjective, with kernel O₂(I). -/
theorem binary_source_projection_exact (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    Function.Surjective (D.binarySourceJoinProjection hUT g hgL) ∧
      (D.binarySourceJoinProjection hUT g hgL).ker = pCore 2 (D.I g) := by
  let eJ := binarySourceJoinEquiv h b hUT g hgL hgN
  let e := binarySourceCoreEquiv h b hUT g hgL hgN
  constructor
  · intro y
    obtain ⟨q, hq⟩ := e.surjective (eJ y)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (D.I g)) q
    refine ⟨x, eJ.injective ?_⟩
    exact hq
  · rw [← binary_source_star_kernel h b hUT g hgL hgN]
    ext x
    change (D.binarySourceJoinProjection hUT g hgL x = 1) ↔
      D.binaryStarRestriction (D.I g) (binary_I_le_LT hUT hgL) x = 1
    exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩

/-- G.2.3(1–7) for n=1, with the original moving g and the actual star action.
The only preceding-source conclusions assumed are U≤T and Φ(U)≤V₁.
The tensor equivalence and order formula share their natural multiplicity;
the fixed/moved-space identities hold for every element of U−W. -/
theorem binary_source_lemma (D : Setup G) (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    ∃ (eJ : (D.star D.L ⊔ D.star D.U : Subgroup D.Star) ≃* S₃)
      (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* S₃)
      (P : Sylow 2 (D.star D.L ⊔ D.star D.U : Subgroup D.Star)),
      (P : Subgroup (D.star D.L ⊔ D.star D.U : Subgroup D.Star)).map
        (D.star D.L ⊔ D.star D.U).subtype = D.star D.U ∧
      D.I g = D.L ⊔ D.U ∧ (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) ∧
      Function.Surjective (D.binarySourceJoinProjection hUT g hgL) ∧
      (D.binarySourceJoinProjection hUT g hgL).ker = pCore 2 (D.I g) ∧
      (∀ x : D.I g, e (QuotientGroup.mk' (pCore 2 (D.I g)) x) =
        eJ (D.binarySourceJoinProjection hUT g hgL x)) ∧
    ∃ (hN : ((D.S₂ g).subgroupOf (D.S g)).Normal),
      letI := hN
      ∃ (hA : IsElementaryAbelian 2 ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))),
        letI := hA
        ∃ (σ : Representation (ZMod 2) S₃
            (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
          (d : Representation.BinaryConjugationSection (D.I g) (D.S g)
            (D.S₂ g) (σ.comp (eJ.toMonoidHom.comp (D.binarySourceJoinProjection hUT g hgL)))),
          D.S g = D.W g ⊔ conjugate (D.W g) g ∧
          (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) ∧
          D.V ≤ D.S₂ g ∧ D.S₂ g ≤ D.S g ∧
          D.V ≤ D.S g ⊓ centralizer (D.S g : Set G) ∧
          (D.V.subgroupOf (D.I g)).Normal ∧
          ((D.S₂ g).subgroupOf (D.I g)).Normal ∧
          ⁅D.S₂ g, D.I g⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ g) ∧
          (∀ s : D.S g, (d.coordinates s).toAdd =
            Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) s)) ∧
          Finite (multiplicitySpace σ) ∧
          IsCompl (d.imageSpace (D.W g)) (d.imageSpace (conjugate (D.W g) g)) ∧
          (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
                Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g)),
              ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
                  (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
                σ a (j z)) ∧
          Nat.card D.U = 2 ^ (Module.finrank (ZMod 2) (multiplicitySpace σ) + 3) *
            D.V.relIndex (D.S₂ g) ∧
          (∀ u : D.I g, (u : G) ∈ D.U → (u : G) ∉ D.W g →
              LinearMap.ker (σ (eJ (D.binarySourceJoinProjection hUT g hgL u)) - (1 : Module.End (ZMod 2) (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))) = d.imageSpace (D.W g) ∧
              LinearMap.range (σ (eJ (D.binarySourceJoinProjection hUT g hgL u)) - (1 : Module.End (ZMod 2) (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))) = d.imageSpace (D.W g) ∧
              (d.imageSpace (conjugate (D.W g) g)).map (σ (eJ (D.binarySourceJoinProjection hUT g hgL u)) - (1 : Module.End (ZMod 2) (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))) =
                d.imageSpace (D.W g)) ∧
          ∀ v, (∀ a : (D.star D.L ⊔ D.star D.U : Subgroup D.Star),
              a.val ∈ D.star D.U → σ (eJ a) v = v) ↔
            v ∈ d.imageSpace (D.W g) := by
  obtain ⟨_, ⟨P, hP⟩, hI, hprod⟩ := binary_source_recognition h b hUT g hgL hgN
  obtain ⟨_, _, hnorm, hindex, _⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨honto, hker⟩ := binary_source_projection_exact h b hUT g hgL hgN
  refine ⟨binarySourceJoinEquiv h b hUT g hgL hgN,
    binarySourceCoreEquiv h b hUT g hgL hgN, P, hP, hI, hprod, honto, hker,
    (fun _ => rfl), ?_⟩
  have hlater := D.binary_source_clauses_three_to_seven h b hUT hf g hgL hgN hI
    (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  obtain ⟨hN, hA, σ, d, H⟩ := hlater
  let d' : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
      (σ.comp ((binarySourceJoinEquiv h b hUT g hgL hgN).toMonoidHom.comp
        (D.binarySourceJoinProjection hUT g hgL))) :=
    { d with
      equivariant := by
        intro x s
        simpa only [MonoidHom.comp_apply, binary_source_projection,
          MulEquiv.coe_toMonoidHom] using d.equivariant x s }
  refine ⟨hN, hA, σ, d', ?_⟩
  simpa only [d', Representation.BinaryConjugationSection.imageSpace,
    binary_source_projection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    D.binarySourceJoinProjection_fixed_iff hUT g hgL
      (fun a v => σ (binarySourceJoinEquiv h b hUT g hgL hgN a) v)] using H

end CFSG.Quasithin.ChapterG.Section02.Setup
