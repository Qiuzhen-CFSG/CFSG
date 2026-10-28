module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReciprocalRecognizedSections
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalFixedLine
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalDefinition

/-!
# The neighboring center fills the natural residual fixed line

The alpha center fixes its own core, whose beta quotient image is the full
Sylow. Its image in the beta residual section is invariant under the whole
Sylow normalizer and generates the section. Natural fixed-line transitivity
therefore makes this image the full fixed line. Its exact coordinate kernel
gives [Z_alpha : C_Z_alpha(O²(L_beta))] = |F_beta|.

The application retains the actual beta marking and whole residual section;
it does not assume alpha recognition or equality of the two fields.
Source: DGS, Groups and Graphs (1985), 9.4(i), printed p.143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The neighboring center maps onto the full natural Sylow fixed line,
with its exact original residual-centralizer index. -/
theorem residual_neighbor_fixed_line (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    (hz : Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) v) (V (family P) v 1)
      (V (family P) v 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) v)).map
        (graphLocalGroup (family P) v).subtype : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v))))))
    (hf : Function.Injective σ) (R : Sylow 2 SL(2,F))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) (hnat : IsSourceNatural σ R n) :
    let H := graphLocalGroup (family P) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∃ T : Sylow 2 SL(2,F), ((Q (family P) w).subgroupOf H).map q = T ∧
      c.imageSpace (Z (family P) w) = fixedSpace σ T ∧
      (centralizer ((pResidual 2 H).map H.subtype : Set G)).relIndex (Z (family P) w) = Nat.card F ∧
      ∀ l : H, q l ∈ normalizer (T : Set SL(2,F)) ↔ (l : G) • w = w := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (V Γ v 1) := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨_,hfix,_⟩ := sourceNatural_generation_and_fixed σ hf R hn hF hnat
  obtain ⟨_,_,_,_,_,E,hE⟩ := sourceNatural_coordinates_and_consequences σ hf R hn hF hnat
  let : Nontrivial W := E.toEquiv.nontrivial
  obtain ⟨T,hT,hgen,hTf⟩ := linear_residual_section_sylow_generation h hB hS hvw hne hz e σ c
  have hquad : IsQuadratic σ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) R T
    exact SL2SylowFixedRecognition.quadratic_conjugate σ hnat.2.2 g
  have hZW : Z Γ w ≤ V Γ v 1 := CommutingNontrivial.Z_neighbor_le_V Γ hvw
  have hA : c.imageSpace (Z Γ w) ≤ fixedSpace σ T := by
    intro z hz' t
    have ht : (t : SL(2,F)) ∈ ((Q Γ w).subgroupOf H).map q := by rw [hT]; exact t.property
    obtain ⟨l,hl,he⟩ := ht
    change σ (t : SL(2,F)) z = z
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le (Q Γ w) (Z Γ w)
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ w (source_Z_Q_U h w).1))).le.trans bot_le)
      l hl z hz'
  have hnormal : ∀ g ∈ normalizer (T : Set SL(2,F)),
      ∀ z ∈ c.imageSpace (Z Γ w), σ g z ∈ c.imageSpace (Z Γ w) := by
    intro g hg z hz'
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) g
    obtain ⟨x,hx,rfl⟩ := (c.mem_imageSpace_iff (Z Γ w) z).mp hz'
    have hl : (l : G) ∈ normalizer (Z Γ w : Set G) :=
      CommutingNontrivial.stabilizer_normalizes_Z Γ w ((hTf l).mp hg)
    exact (c.mem_imageSpace_iff (Z Γ w) _).mpr
      ⟨⟨(l : G) * x * (l : G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized l.property) x).mp x.property⟩,
        (mem_normalizer_iff.mp hl x).mp hx,c.equivariant l x⟩
  have hfull : c.imageSpace (Z Γ w) = fixedSpace σ T := by
    rcases invariant_subspace_of_natural_fixed σ T hquad hgen hfix E hE _ hA hnormal with hzero | hfull
    · have hh : (⊥ : Subrepresentation (σ.comp q)) = ⊤ :=
        residual_section_neighbor_generation h hB hS hvw hz (σ.comp q) c ⊥ (by
          intro z hz'
          change (c.coordinates z).toAdd ∈ (⊥ : Submodule (ZMod 2) W)
          rw [←hzero]
          exact (c.mem_imageSpace_iff (Z Γ w) _).mpr ⟨z,hz',rfl⟩)
      exact False.elim (bot_ne_top hh)
    · exact hfull
  refine ⟨T,hT,hfull,?_,hTf⟩
  have hcard := c.imageSpace_card_eq_relIndex (Z Γ w) hZW
  rw [hfull] at hcard
  have hindex : (V Γ v 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G)).relIndex (Z Γ w) =
      (centralizer ((pResidual 2 H).map H.subtype : Set G)).relIndex (Z Γ w) := by
    apply congrArg Subgroup.index
    ext z
    exact and_iff_right (hZW z.property)
  exact hindex.symm.trans (hcard.symm.trans (sl2_natural_fixed_spaces σ T hquad hgen hfix E).1)

open Representation.NormalElementaryQuotient
variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original center at alpha has index equal to the beta field order
modulo its centralizer of the beta residual. -/
theorem reduced_natural_residual_neighbor_index (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    (centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S₀))).relIndex
      (Z Γ a) = Nat.card F := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,σ,R,hσ,hfaith,hnat,E,hE⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  have hcomp : σ.comp q = fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨_,_,⟨c⟩,_⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  obtain ⟨T,_,_,hindex,_⟩ := residual_neighbor_fixed_line ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hab.symm (core_escape_of_intersection_obstruction Γ hob)
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
    e σ (hcomp.symm ▸ c) hfaith R hn hF hnat
  exact hindex


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
