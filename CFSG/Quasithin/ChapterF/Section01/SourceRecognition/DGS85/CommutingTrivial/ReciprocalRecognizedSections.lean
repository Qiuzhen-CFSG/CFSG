module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.SaturatedResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReciprocalLinearSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReciprocalRecognition

/-!
# The whole natural residual sections in the reciprocal branch

The full catalogue selects the actual SL₂ quotient and gives the original
core and centralizer indices. Sharp-index saturation constructs the whole
residual quotient action, and corrected 5.12 gives its faithful natural
coordinates. Apply the same argument to the actual reverse critical pair
to obtain both sections over the same field, retaining each quotient map.
The constructed actions also discharge the descent premises of the existing
reciprocal parameter theorem, giving the original Sylow omega-center indices.

The two marked vertices are beta and alpha-prime, on the same vertex orbit.
This establishes the reciprocal 9.3 assertions under the earlier catalogue,
Chapter 8 reorientation, and 6.5 inputs. Reciprocal alpha recognition in 9.4,
the 9.5--9.11 geometry, distance three and both field-two conclusions remain
with Chapter 9 assembly. Source: DGS, Groups and Graphs (1985), 9.2--9.3,
printed p.142, and corrected 5.12, pp.113--115.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Natural coordinates on the whole original residual section, retaining
its literal quotient map and conjugation action. -/
def NaturalResidualSection (h : HypothesisF11 L S₀)
    (v : Vertex (Reduction.reducedFamily L S₀))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)) ≃* SL(2,F))
    (n : ℕ) : Prop :=
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ v
  let A := (V Γ v 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
  letI := neighborhoodIn_normal Γ v H (sylowGenerated_le _)
  ∃ hb2 : 2 < b Γ,
    letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
      (fun w => (source_Z_Q_U (Reduction.reduced_triple h) w).1)
      (Reduction.reduced_kernel_sylow h) v hb2 H
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    ∃ (σ : Representation (ZMod 2) SL(2,F) (FixedQuotient A (pResidual 2 H)))
      (T : Sylow 2 SL(2,F)),
      (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) ∧
      Function.Injective σ ∧ IsSourceNatural σ T n ∧
      ∃ E : FixedQuotient A (pResidual 2 H) ≃ₗ[ZMod 2] (Fin 2 → F),
        ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z)

/-- The sharp original actor and centralizer indices construct a faithful
natural action on the entire residual section. -/
theorem reduced_critical_saturated_residual_natural (h : HypothesisF11 L S₀)
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
    (hactor : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (hindex : (centralizer (V (Reduction.reducedFamily L S₀) a' 1 :
      Set (Reduction.G₀ L S₀))).relIndex (V (Reduction.reducedFamily L S₀) beta 1) ≤ Nat.card F) :
    NaturalResidualSection h beta e n := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,σ,hσ⟩ := reduced_critical_saturated_residual_action h hc hab hd hb hcomm hob
    hn hF e hactor hindex
  refine ⟨hb2,?_⟩
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨T,hT,hgen,hfaith,hcard,hlo,hu,hnat⟩ :=
    reduced_critical_residual_index_recognition h hc hab hd hb hcomm hob hn hF e hb2 σ hσ
  have hfield : 1 < Nat.card F := by
    rw [hF]
    exact Nat.one_lt_pow (by omega) (by decide)
  have hsquare : Nat.card F < Nat.card F ^ 2 := by nlinarith
  obtain ⟨hN,E,hE⟩ := hnat (by rw [hactor]; exact hindex.trans_lt hsquare)
  exact ⟨σ,T,hσ,hfaith,hN,E,hE⟩

/-- Original (9.3) in the reciprocal branch. Both quotient markings and
both whole natural residual sections are constructed from the earlier
catalogue, Chapter 8 exchange, and source 6.5 obstruction. -/
theorem reduced_large_neighbor_recognized_sections (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (M : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta))) :
    let Γ := Reduction.reducedFamily L S₀
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
      ∃ e' : (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (Q Γ beta).relIndex (V Γ a' 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        (∀ (T₀ : Sylow 2 (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))
          (R₀ : Sylow 2 (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))),
          (Q Γ a').relIndex (V Γ beta 1) = Nat.card (omegaCenterIn (T₀ : Subgroup (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)))) ∧
          (Q Γ beta).relIndex (V Γ a' 1) = Nat.card (omegaCenterIn (R₀ : Subgroup (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))))) ∧
        NaturalResidualSection h beta eβ n ∧ NaturalResidualSection h a' e' n := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,⟨eβ⟩,⟨e'⟩,hx,hy,hC⟩ :=
    reduced_large_neighbor_recognized_indices h hc hab hd hb hcomm htriv he h8 M
  let := instF
  let := finF
  let := charF
  let Γ := Reduction.reducedFamily L S₀
  have hfwd := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hfwd
  simp only [inf_relIndex_left] at hfwd
  have hC' := hfwd.trans hx
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute (Reduction.reduced_triple h) hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  have hfirst := reduced_critical_saturated_residual_natural h hc hab hd hb hcomm (hob a beta hab)
    hn hF eβ hy hC'.le
  have hsecond := reduced_critical_saturated_residual_natural h hzc hz.symm hd' hb hzcomm
    (hob z a' hz.symm) hn hF e' hx hC.le
  let ht := Reduction.reduced_triple h
  let H := graphLocalGroup Γ beta
  let H' := graphLocalGroup Γ a'
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  let := neighborhoodIn_normal Γ a' H' (sylowGenerated_le _)
  have hfirstSave := hfirst
  have hsecondSave := hsecond
  obtain ⟨hb2,σ,T,hσ,_,_⟩ := hfirst
  obtain ⟨hb2',τ,R,hτ,_,_⟩ := hsecond
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2' H'
  have hparameters := (reduced_large_neighbor_residual_natural h hc hab hd hb hcomm htriv he h8
    (hob a beta hab) (fun z hz _ => hob z a' hz.symm) hn hF hn hF eβ e'
    hb2 σ τ hσ hτ).2.2.2.1
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,e',hx,hy,hC',hC,hparameters,hfirstSave,hsecondSave⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
