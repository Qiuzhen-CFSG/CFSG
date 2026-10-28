module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreSection
public import Theory.Representation.BinaryConjugationSection.NaturalCentralExtension

/-!
# The original elementary core quotient after the Cartan collapse

The verified natural residual action and the orders |V|=q³, |Z|=q identify
its coordinate kernel with the literal Z. Once the neighboring core
intersection is V, the verified core-section action supplies the other natural
layer Q/V. Their original conjugation maps give [Q,Q]≤Z and make Q/Z
elementary abelian by the nonbinary natural-extension argument. The canonical
conjugation representation retains the image of V as its distinguished natural
submodule and identifies the quotient by that image with the other natural layer.

This is the elementary-abelian part of DGS, *Groups and Graphs* (1985),
9.10(6), pp.149–150. The intersection-equals-span premise is the precise
remaining output of 9.10(4)–(5). No splitting of the two natural factors is
claimed here. Both the original field marking and quotient are preserved.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private def naturalSection
    {A : Type*} [Group A] {H U Z₀ : Subgroup A}
    {F W : Type*} [Field F] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W]
    (π : H →* SL(2,F)) (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H U Z₀ (σ.comp π))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g w, E (σ g w) = Matrix.mulVec g.val (E w)) :
    BinaryConjugationSection H U Z₀
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp π) where
  section_le := c.section_le
  kernel_le := c.kernel_le
  normalized := c.normalized
  coordinates := E.toAddEquiv.toMultiplicative.toMonoidHom.comp c.coordinates
  onto := E.toAddEquiv.toMultiplicative.surjective.comp c.onto
  kernel_eq := by
    ext z
    change E (c.coordinates z).toAdd = 0 ↔ (z:A) ∈ Z₀
    rw [E.map_eq_zero_iff]
    exact c.coordinates_eq_one_iff z
  equivariant g z := by
    change E (c.coordinates _).toAdd = Matrix.mulVec (π g).val (E (c.coordinates z).toAdd)
    rw [c.equivariant]
    exact hE _ _

/-- The actual residual coordinates have literal kernel Z, by the source orders. -/
theorem reduced_natural_span_section
    (h : HypothesisF11 L S) {beta : Vertex (Reduction.reducedFamily L S)}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)) ≃* SL(2,F))
    {n : ℕ} (hres : NaturalResidualSection h beta eβ n)
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    (hVcard : Nat.card (V (Reduction.reducedFamily L S) beta 1) = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) beta) = Nat.card F) :
    let Γ := Reduction.reducedFamily L S
    let π := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta)))
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    Nonempty (BinaryConjugationSection (graphLocalGroup Γ beta) (V Γ beta 1) (Z Γ beta)
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp π)) := by
  classical
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let π := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let K := V Γ beta 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,σ,T,hσ,hfaith,hnat,E,hE⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcomp : σ.comp π = Representation.NormalElementaryQuotient.fixedQuotientAction A
      (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨⟨c₀⟩,_,_⟩ := neighborhood_residual_section ht (Reduction.reduced_kernel_sylow h)
    beta hb2 H (core_le_graphLocalGroup ht beta) (sylowGenerated_le _)
  let c : BinaryConjugationSection H (V Γ beta 1) K (σ.comp π) := hcomp.symm ▸ c₀
  have hZK : Z Γ beta ≤ K := le_inf (Z_le_V Γ beta 1) (by
    intro z hz
    exact centralizer_le (map_subtype_le _) ((mem_omegaCenterIn_iff _ _).mp (hω ▸ hz)).2.1)
  let : Finite (V Γ beta 1) := Finite.of_injective
    (inclusion (c.section_le.trans (sylowGenerated_le _))) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (show K ≤ V Γ beta 1 from inf_le_left))
    (inclusion_injective _)
  have hcardK : Nat.card K = Nat.card F := by
    have hh := c.card_section
    have hW : Nat.card (Representation.NormalElementaryQuotient.FixedQuotient A
        (pResidual 2 H)) = Nat.card F ^ 2 := by
      rw [Nat.card_congr E.toEquiv,Nat.card_fun,Nat.card_fin]
    rw [hVcard,hW] at hh
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith [sq_pos_of_pos hp]
  have hKZ : K = Z Γ beta :=
    (eq_of_le_of_card_ge hZK (by rw [hcardK,hZcard])).symm
  let cV := naturalSection π σ c E hE
  exact ⟨hKZ ▸ cV⟩

/-- The literal core quotient and its two natural factors after the kernel collapse. -/
theorem reduced_core_factors_of_intersection_eq_span
    (h : HypothesisF11 L S)
    {a beta x : Vertex (Reduction.reducedFamily L S)}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)) ≃* SL(2,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hres : NaturalResidualSection h beta eβ n)
    (hsec : CoreQuotientSection (Reduction.reducedFamily L S) a beta x F eβ)
    (hNspan : Q (Reduction.reducedFamily L S) a ⊓ Q (Reduction.reducedFamily L S) x =
      V (Reduction.reducedFamily L S) beta 1)
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    (hc : ⁅Q (Reduction.reducedFamily L S) beta,V (Reduction.reducedFamily L S) beta 1⁆ ≤
      Z (Reduction.reducedFamily L S) beta)
    (hVcard : Nat.card (V (Reduction.reducedFamily L S) beta 1) = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) beta) = Nat.card F) :
    let Γ := Reduction.reducedFamily L S
    ∃ hZ : ((Z Γ beta).subgroupOf (Q Γ beta)).Normal,
      letI := hZ
      ⁅Q Γ beta,Q Γ beta⁆ ≤ Z Γ beta ∧
        ∃ hE : IsElementaryAbelian 2 (Q Γ beta ⧸ (Z Γ beta).subgroupOf (Q Γ beta)),
          letI := hE
          let π := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta)))
          letI : Algebra (ZMod 2) F := ZMod.algebra F 2
          ∃ (ρ : Representation (ZMod 2) SL(2,F)
              (Additive (Q Γ beta ⧸ (Z Γ beta).subgroupOf (Q Γ beta))))
            (c : BinaryConjugationSection (graphLocalGroup Γ beta) (Q Γ beta) (Z Γ beta) (ρ.comp π)),
            (∀ s : Q Γ beta, (c.coordinates s).toAdd =
              Additive.ofMul (QuotientGroup.mk' ((Z Γ beta).subgroupOf (Q Γ beta)) s)) ∧
            ∃ (X : Subrepresentation ρ)
              (eX : X.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → F))
              (eQ : (Additive (Q Γ beta ⧸ (Z Γ beta).subgroupOf (Q Γ beta)) ⧸ X.toSubmodule)
                ≃ₗ[ZMod 2] (Fin 2 → F)),
              (∀ g x, eX (X.toRepresentation g x) = Matrix.mulVec g.val (eX x)) ∧
              (∀ g x, eQ (X.quotientRepresentation g x) = Matrix.mulVec g.val (eQ x)) ∧
              X.toSubmodule = c.imageSpace (V Γ beta 1) := by
  classical
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let H := graphLocalGroup Γ beta
  let π := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨cV'⟩ := reduced_natural_span_section h eβ hres hω hVcard hZcard
  obtain ⟨hN,hcard,hElem,τ,d,hd,hnatural⟩ := hsec
  let := hN
  let := hElem
  obtain ⟨EQ,hEQ⟩ := hnatural n hn hF
  let cQ := naturalSection π τ d EQ hEQ
  have cQ' : BinaryConjugationSection H (Q Γ beta) (V Γ beta 1)
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp π) := hNspan ▸ cQ
  have hNZ : H ≤ normalizer (Z Γ beta : Set (Reduction.G₀ L S)) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)
  let hZ : ((Z Γ beta).subgroupOf (Q Γ beta)).Normal :=
    normal_subgroupOf_of_le_normalizer ((core_le_graphLocalGroup ht beta).trans hNZ)
  have hk : π.ker = (Q Γ beta).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
    have hcore : (pCore 2 H).map H.subtype = Q Γ beta := graphLocalGroup_core ht beta
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hex : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
    have hbig : 2 < Nat.card F := by
      rw [hF]
      exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
    by_contra! hall
    let := Fintype.ofFinite F
    have hle : Nat.card F ≤ 2 := by
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card F ≤ ({0,1} : Finset F).card := Finset.card_le_card (by
          intro t _
          by_cases ht : t = 0
          · simp [ht]
          · simp [hall t ht])
        _ ≤ 2 := by simp
    omega
  obtain ⟨t,ht0,ht1⟩ := hex
  refine ⟨hZ,?_⟩
  exact BinaryConjugationSection.natural_central_extension_factors H (Q Γ beta) (V Γ beta 1)
    (Z Γ beta) cQ'.kernel_le (Z_le_V Γ beta 1) hNZ π
    (eβ.surjective.comp (QuotientGroup.mk'_surjective _)) hk cV' cQ' t ht0 ht1 hc

/-- The actual core quotient is elementary once (4)–(5) identify its kernel with V. -/
theorem reduced_core_elementary_of_intersection_eq_span
    (h : HypothesisF11 L S)
    {a beta x : Vertex (Reduction.reducedFamily L S)}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)) ≃* SL(2,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hres : NaturalResidualSection h beta eβ n)
    (hsec : CoreQuotientSection (Reduction.reducedFamily L S) a beta x F eβ)
    (hNspan : Q (Reduction.reducedFamily L S) a ⊓ Q (Reduction.reducedFamily L S) x =
      V (Reduction.reducedFamily L S) beta 1)
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    (hc : ⁅Q (Reduction.reducedFamily L S) beta,V (Reduction.reducedFamily L S) beta 1⁆ ≤
      Z (Reduction.reducedFamily L S) beta)
    (hVcard : Nat.card (V (Reduction.reducedFamily L S) beta 1) = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) beta) = Nat.card F) :
    let Γ := Reduction.reducedFamily L S
    ∃ hZ : ((Z Γ beta).subgroupOf (Q Γ beta)).Normal,
      letI := hZ
      ⁅Q Γ beta,Q Γ beta⁆ ≤ Z Γ beta ∧
        IsElementaryAbelian 2 (Q Γ beta ⧸ (Z Γ beta).subgroupOf (Q Γ beta)) := by
  obtain ⟨hZ,hQQ,hE,_⟩ := reduced_core_factors_of_intersection_eq_span h eβ hn hF
    hres hsec hNspan hω hc hVcard hZcard
  exact ⟨hZ,hQQ,hE⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
