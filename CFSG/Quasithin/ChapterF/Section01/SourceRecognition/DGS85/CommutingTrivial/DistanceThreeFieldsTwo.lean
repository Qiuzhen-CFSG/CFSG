module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedPairContradiction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NaturalCenterTransport

/-!
# Both field-two conclusions of DGS 9.10

The Cartan fixed-subgroup argument identifies the neighboring-core intersection
with the natural span. For a field of order greater than two, split the natural
self-extension, form the two exchanged elementary factors, and apply the
page150 normal-subgroup contradiction. The adjacent fields are kept distinct;
their proved equal orders then force both to have order two.

The original Chapter 8 reverse linear-output input and concrete rank-one models
are retained. The source assembly discharges the distance and core-obstruction
inputs from the full catalogue and F.1.11, respectively.

Source: DGS, *Groups and Graphs* (1985), 9.10, pp.147--150.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- Original commuting-trivial critical data force distance three and both adjacent fields to have order two. -/
theorem reduced_critical_distance_three_fields_two
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (h8distance : ChapterEightDistance (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    b Γ = 3 ∧
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nat.card F = 2 ∧ Nat.card K = 2 ∧
          Nonempty ((graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F)) ∧
          Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃* SL(2,K)) := by
  obtain ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec,
      hsecond,hneighbors,C,hCfix,hCS,hCE,hCo,hCa,ea,eb,hCprod,hdis,hcom,
      hkernels,hfixed,hintersection,hneigh,hdec,l,r,hal,hlb,hdr,hrx,hext,el,ed,er,
      hline,hldis,hlescape,hlkernel,hcollapse⟩ :=
    reduced_critical_distance_three_fixed_collapse h hc hab hd hb h8distance hcomm htriv h8 hob
      Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  have hn1 : n = 1 := by
    by_contra hn1
    have hn' : 1 < n := by omega
    obtain ⟨_,_,_,_,_,_,_,_,_,hcollapseβ,_⟩ := hcollapse hn'
    let ht := Reduction.reduced_triple h
    let Γ := Reduction.reducedFamily L S₀
    let : ∀ i, Finite (Γ i) := finite_endpoints ht
    let hB := Reduction.reduced_borel_core_sylow h
    let hS := Reduction.reduced_vertex_sylow h
    let : IsMulCommutative C := hCa
    let : Algebra (ZMod 2) K := ZMod.algebra K 2
    let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
    have hω := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
    obtain ⟨ρ,U,hact,hfaith,hnatural,E,hE⟩ := hnat
    have horders := linear_natural_neighbor_center_orders ht hB hS hab
      (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
      ρ hact hfaith ⟨U,hnatural⟩
    obtain ⟨ca⟩ := graph_natural_center_section ht a eα ρ hact E hE
    have hdb : a' ≠ beta := by
      intro he
      have hh := hd
      rw [he,SimpleGraph.dist_self,hb3] at hh
      omega
    obtain ⟨g,_,hga⟩ := locally_transitive Γ hab.symm hbx
    obtain ⟨ex,⟨cx⟩,hxcard,hxspan⟩ := reduced_middle_natural_center h g hga hxa' hbx.symm hdb
      eα ca hω horders.2
    have hCp : C ≤ stabilizer Γ a ⊓ stabilizer Γ beta :=
      hCfix.trans (inf_le_left.trans inf_le_left)
    have hCx : C ≤ stabilizer Γ x := hCfix.trans (inf_le_left.trans inf_le_right)
    have hCb : C ≤ stabilizer Γ beta := hCp.trans inf_le_right
    have hCF : C ≤ stabilizer Γ x ⊓ stabilizer Γ beta := le_inf hCx hCb
    obtain ⟨hdisX,hprodX⟩ := path_cartan_complement_at_edge ht hab hbx.symm C hCp hCF hCo hCS hCE
    have htor := (edge_complement_local_torus ht hB hS hbx.symm ex C hCF hdisX hprodX).1
    have hCp' : C ≤ stabilizer Γ beta ⊓ stabilizer Γ a := le_inf hCb (hCp.trans inf_le_left)
    have hdis' : Disjoint C ((stabilizer Γ beta ⊓ stabilizer Γ a : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2) := by
      rw [inf_comm]
      exact hCS
    have hprod' : C ⊔ (stabilizer Γ beta ⊓ stabilizer Γ a : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2 =
        stabilizer Γ beta ⊓ stabilizer Γ a := by
      rw [inf_comm (stabilizer Γ beta)]
      exact hCE
    have hpath := adjacent_linear_short_path_transitive ht hB hS hob hab eα eβ
    exact reduced_adapted_pair_nonbinary_contradiction h hxa' hbx.symm hdb hb3 ex eβ heq
      hn' hF hres hsec hcollapseβ hω hcV.le hcard (horders.2.trans heq) hxspan hxcard
      hab.symm (hpath beta 2 (by decide)) eα C hCx hCp' hCo hdis' hprod' htor cx
  have hFtwo : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
  exact ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hFtwo,heq.trans hFtwo,⟨eβ⟩,⟨eα⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
