module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeBetaKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedCommon
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedSplitting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanOuterFixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CoreElementaryQuotient
public import Theory.Representation.GeneralLinearNatural

/-!
# The original nonbinary Cartan collapse in DGS 9.10

Keep the full extended Cartan and the complete original source bundle.
Its fixed subgroup D propagates through the three interior cores and
splits over the terminal core, with preceding central line Z_l. The
natural actions on the center and neighborhood section show that D
misses the terminal span. Thus the intersection of D with the terminal
radius-two core is the fixed group Q₀ of the full Cartan.

Coprime action and conjugacy of the radius-two cores give both products
H = Q₀ × V_(alpha') and N_beta = Q₀ × V_beta. The first makes Q₀
elementary abelian. Two Hall--Witt steps then centralize Q₀ in the actual
beta local group; its Sylow-center span detects Q₀ and forces Q₀ = 1.
All natural actions, field markings and the original full Cartan are
retained. The resulting core-intersection identities supply the literal
inputs to the natural-extension and adapted-pair construction.

Source: DGS, *Groups and Graphs* (1985), 9.10(4)--(5), pp.148--149.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The nonbinary branch of the original source bundle has trivial full-Cartan fixed subgroup and both neighboring-core intersections equal their literal spans. -/
theorem reduced_critical_distance_three_fixed_collapse
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
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
 :
    let Γ := Reduction.reducedFamily L S₀
    b Γ = 3 ∧
    let H := graphLocalGroup Γ a
    let := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            (let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
            let : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).Adj x a' ∧
              ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ x ∧
              V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
              V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x ∧
              (let N := Q Γ a ⊓ Q Γ x
               N = Q Γ beta ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) ∧
               N ≤ Q Γ beta ∧ V Γ beta 1 ≤ N ∧
               stabilizer Γ beta ≤ normalizer (N : Set (Reduction.G₀ L S₀)) ∧
               ⁅Q Γ beta ⊓ Q Γ x,V Γ a' 1⁆ ≤ Z Γ x ∧
               ⁅N,(pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype⁆ ≤ V Γ beta 1 ∧
               CoreQuotientSection Γ a beta x F eβ ∧
               N = Q Γ beta ⊓ ballKernel Γ beta 2 ∧
               (∀ z : Vertex Γ, (graph Γ).Adj beta z → N ≤ Q Γ z) ∧
               ∃ C : Subgroup (Reduction.G₀ L S₀),
                 C ≤ stabilizer Γ a ⊓ stabilizer Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
                 Disjoint C ((stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2) ∧
                 C ⊔ (stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2 =
                   stabilizer Γ a ⊓ stabilizer Γ beta ∧
                 Odd (Nat.card C) ∧ IsMulCommutative C ∧
                 Nonempty ((C ⊓ graphLocalGroup Γ a : Subgroup (Reduction.G₀ L S₀)) ≃* Kˣ) ∧
                 Nonempty ((C ⊓ graphLocalGroup Γ beta : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
                 C = (C ⊓ graphLocalGroup Γ a) ⊔ (C ⊓ graphLocalGroup Γ beta) ∧
                 Disjoint (C ⊓ graphLocalGroup Γ a) (C ⊓ graphLocalGroup Γ beta) ∧
                 ⁅C ⊓ graphLocalGroup Γ a,C ⊓ graphLocalGroup Γ beta⁆ = ⊥ ∧
                 (1 < n → Disjoint (C ⊓ graphLocalGroup Γ a) (ballKernel Γ a 1) ∧
                   Disjoint (C ⊓ graphLocalGroup Γ beta) (ballKernel Γ beta 1)) ∧
                 (1 < n → ∀ v : Vertex Γ, beta.type = v.type →
                   ∀ T : Subgroup (Reduction.G₀ L S₀), T ≤ graphLocalGroup Γ v →
                     Odd (Nat.card T) → T ≠ ⊥ →
                     Q Γ v ⊓ centralizer (T : Set (Reduction.G₀ L S₀)) ≤ ballKernel Γ v 2) ∧
                 (1 < n → ∀ v w : Vertex Γ, (graph Γ).Adj v w →
                   ballKernel Γ v 1 ⊓ ballKernel Γ w 1 = Q Γ v ⊓ Q Γ w) ∧
                 (1 < n → ∀ v : Vertex Γ, beta.type = v.type →
                   ∀ w : Vertex Γ, (graph Γ).Adj v w →
                     ∀ T : Subgroup (Reduction.G₀ L S₀), T ≤ graphLocalGroup Γ v →
                       Odd (Nat.card T) → Disjoint T (ballKernel Γ w 1)) ∧
                 (1 < n →
                   let T := C ⊓ graphLocalGroup Γ beta
                   let D := Q Γ beta ⊓ centralizer (T : Set (Reduction.G₀ L S₀))
                   Disjoint T (ballKernel Γ a 1) ∧ Disjoint T (ballKernel Γ x 1) ∧
                   N = V Γ beta 1 ⊔ D ∧ ⁅N,T⁆ = ⁅V Γ beta 1,T⁆ ∧
                   N = ⁅V Γ beta 1,T⁆ ⊔ D ∧ Disjoint ⁅V Γ beta 1,T⁆ D ∧
                   ⁅⁅V Γ beta 1,T⁆,D⁆ = ⊥) ∧
                 ∃ l r : Vertex Γ, (graph Γ).Adj a l ∧ l ≠ beta ∧
                   (graph Γ).Adj a' r ∧ r ≠ x ∧
                   C ≤ stabilizer Γ l ⊓ stabilizer Γ r ∧
                   Nonempty ((C ⊓ graphLocalGroup Γ l : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
                   Nonempty ((C ⊓ graphLocalGroup Γ a' : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
                   Nonempty ((C ⊓ graphLocalGroup Γ r : Subgroup (Reduction.G₀ L S₀)) ≃* Kˣ) ∧
                   Z Γ a = Z Γ beta ⊔ Z Γ l ∧ Disjoint (Z Γ beta) (Z Γ l) ∧
                   ¬ Z Γ l ≤ Q Γ a' ∧
                   C ⊓ graphLocalGroup Γ l ≤ ballKernel Γ a' 1 ∧
                   (1 < n →
                     let T := C ⊓ graphLocalGroup Γ l
                     let D := C ⊓ graphLocalGroup Γ a'
                     C = T ⊔ D ∧ T = C ⊓ ballKernel Γ a' 1 ∧ Disjoint T D ∧
                     Disjoint T (ballKernel Γ a 1) ∧ Disjoint T (ballKernel Γ x 1) ∧
                     Q Γ l ⊓ centralizer (T : Set (Reduction.G₀ L S₀)) ≤ ballKernel Γ l 2 ∧
                     Disjoint T (ballKernel Γ beta 1) ∧
                     Q Γ a' ⊓ centralizer (C : Set (Reduction.G₀ L S₀)) = ⊥ ∧
                     (Q Γ l ⊓ centralizer (T : Set (Reduction.G₀ L S₀))) = Z Γ l ∧
                     Q Γ a ⊓ Q Γ x = V Γ beta 1 ∧
                     Q Γ x ⊓ Q Γ r = V Γ a' 1)) := by
  obtain ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec,
      hsecond,hneighbors,C,hCfix,hCS,hCE,hCo,hCa,ea,eb,hCprod,hdis,hcom,
      hkernels,hfixed,hintersection,hneigh,hdec,l,r,hal,hlb,hdr,hrx,hext,el,ed,er,
      hline,hldis,hlescape,hlkernel,hremote⟩ :=
    reduced_critical_distance_three_beta_kernel h hc hab hd hb h8distance hcomm htriv h8 hob
      Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  refine ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
    x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec,
    hsecond,hneighbors,C,hCfix,hCS,hCE,hCo,hCa,ea,eb,hCprod,hdis,hcom,
    hkernels,hfixed,hintersection,hneigh,hdec,l,r,hal,hlb,hdr,hrx,hext,el,ed,er,
    hline,hldis,hlescape,hlkernel,?_⟩
  intro hn'
  obtain ⟨hCT,hTk,hTD,hTa,hTx,hDrad,hTb⟩ := hremote hn'
  refine ⟨hCT,hTk,hTD,hTa,hTx,hDrad,hTb,?_⟩
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : IsMulCommutative C := hCa
  let : Finite C := Finite.of_injective
    (inclusion (hCfix.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))) (inclusion_injective _)
  let T := C ⊓ graphLocalGroup Γ l
  let Kd := C ⊓ graphLocalGroup Γ a'
  let D := Q Γ l ⊓ centralizer (T : Set (Reduction.G₀ L S₀))
  let Q₀ := Q Γ a' ⊓ centralizer (C : Set (Reduction.G₀ L S₀))
  let N := Q Γ a ⊓ Q Γ x
  let H := Q Γ x ⊓ Q Γ r
  let J := fun v : Vertex Γ => Q Γ v ⊓ ballKernel Γ v 2
  have bool_eq {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
    cases i <;> cases j <;> cases k <;> first | rfl | exact (hi rfl).elim | exact (hj rfl).elim
  have hbd : beta.type = a'.type := bool_eq hbx.1 hxa'.1.symm
  have hbl : beta.type = l.type := bool_eq hab.1.symm hal.1.symm
  have hax : a.type = x.type := bool_eq hab.1 hbx.1.symm
  have hrd : r.type = x.type := bool_eq hdr.1.symm hxa'.1
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have card_factor {A : Subgroup (Reduction.G₀ L S₀)} {k : Type u} [Field k] [Finite k]
      (e : Nonempty (A ≃* kˣ)) : Nat.card A = Nat.card k - 1 := by
    obtain ⟨f⟩ := e
    exact (Nat.card_congr f.toEquiv).trans (Nat.card_units k)
  have hcT : Nat.card T = Nat.card F - 1 := card_factor el
  have hcKd : Nat.card Kd = Nat.card F - 1 := card_factor ed
  have hTne : T ≠ ⊥ := by intro he; rw [he,card_bot] at hcT; omega
  have hKdne : Kd ≠ ⊥ := by intro he; rw [he,card_bot] at hcKd; omega
  have hoT : Odd (Nat.card T) := hCo.of_dvd_nat (card_dvd_of_le (show T ≤ C from inf_le_left))
  have hoKd : Odd (Nat.card Kd) := hCo.of_dvd_nat (card_dvd_of_le (show Kd ≤ C from inf_le_left))
  have hCp : C ≤ stabilizer Γ a ⊓ stabilizer Γ beta := hCfix.trans (inf_le_left.trans inf_le_left)
  have hCa₀ : C ≤ stabilizer Γ a := hCp.trans inf_le_left
  have hCb₀ : C ≤ stabilizer Γ beta := hCp.trans inf_le_right
  have hCx : C ≤ stabilizer Γ x := hCfix.trans (inf_le_left.trans inf_le_right)
  have hCd : C ≤ stabilizer Γ a' := hCfix.trans inf_le_right
  have hCl : C ≤ stabilizer Γ l := hext.trans inf_le_left
  have hCr : C ≤ stabilizer Γ r := hext.trans inf_le_right
  have htwo := adjacent_linear_short_path_transitive ht hB hS hob hab eα eβ
  have hmark {v w : Vertex Γ} {E : Type u} [Field E] [Finite E] [CharP E 2]
      (hv : v.type = w.type)
      (e : (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)) ≃* SL(2,E)) :
      Nonempty ((graphLocalGroup Γ w ⧸ pCore 2 (graphLocalGroup Γ w)) ≃* SL(2,E)) := by
    obtain ⟨g,hg⟩ := (same_orbit_iff Γ v w).mpr hv
    obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport ht g hg
    exact ⟨f.symm.trans e⟩
  obtain ⟨ex⟩ := hmark hax eα
  obtain ⟨ed'⟩ := hmark hbd eβ
  obtain ⟨el'⟩ := hmark hbl eβ
  obtain ⟨er'⟩ := hmark hrd.symm ex
  have hxa : x ≠ a := by
    intro he
    have hh := hc.1
    rw [←he,SimpleGraph.dist_eq_one_iff_adj.mpr hxa',hb3] at hh
    omega
  have hdb : a' ≠ beta := by
    intro he
    have hh := hd
    rw [he,SimpleGraph.dist_self,hb3] at hh
    omega
  have hDi := graph_cartan_fixed_interior_cores ht hB hS hal hab hbx hxa' hxa hdb eβ ex C
    hCl hCfix hCo hCS hCE hTne hTb hTx hDrad
  have hDa : D ≤ Q Γ a := hDi.trans (inf_le_left.trans inf_le_left)
  have hDb : D ≤ Q Γ beta := hDi.trans (inf_le_left.trans inf_le_right)
  have hDx : D ≤ Q Γ x := hDi.trans inf_le_right
  have hω := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hωtransport (v : Vertex Γ) (hv : beta.type = v.type) :
      Z Γ v = omegaCenterIn (graphLocalGroup Γ v) := by
    obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta v).mpr hv
    have hh := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    change Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) at hω
    rw [←hg,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hω]
  have hωl := hωtransport l hbl
  have hωd := hωtransport a' hbd
  have horders : Nat.card (Z Γ a) = Nat.card F ^ 2 ∧ Nat.card (Z Γ beta) = Nat.card F := by
    obtain ⟨ρ,U,hact,hfaith,hnatural,E,hE⟩ := hnat
    have hh := linear_natural_neighbor_center_orders ht hB hS hab
      (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
      ρ hact hfaith ⟨U,hnatural⟩
    rw [heq] at hh
    exact hh
  have hZcard (v : Vertex Γ) (hv : beta.type = v.type) : Nat.card (Z Γ v) = Nat.card F := by
    obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta v).mpr hv
    rw [←hg,Z_translate,card_map_of_injective (MulAut.conj g).injective]
    exact horders.2
  have hZxcard : Nat.card (Z Γ x) = Nat.card F ^ 2 := by
    obtain ⟨g,hg⟩ := (same_orbit_iff Γ a x).mpr hax
    rw [←hg,Z_translate,card_map_of_injective (MulAut.conj g).injective]
    exact horders.1
  obtain ⟨hlinex,hldisx⟩ := reduced_natural_neighbor_centers_split h hbx.symm hxa' hdb.symm
    hω hZxcard horders.2
  have hcut := linear_neighbor_centers_intersection ht hB hS hab.symm hbx hxa.symm hob hω eβ eα
  have hlQdis := reduced_preceding_line_disjoint_terminal_core h hb hd htriv hcentral
    hline (CommutingNontrivial.Z_neighbor_le_V Γ hab.symm) hcut hldis
  obtain ⟨hDsplit,hDZ,hDZc⟩ := graph_cartan_fixed_terminal_split ht hB hS hxa' ed'
    hωl (hZcard l hbl) hlQdis T inf_le_right hDx
  have hodd := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).1
  have hescape := linear_critical_reciprocal_escape ht hB hS hc hab hd (by change 2 < b Γ; rw [show b Γ = 3 from hb3]; decide) hodd eα eβ
  have hir := (reduced_large_neighbor_linear_indices h hc hab hd hb hcomm htriv hescape h8 hn hF eβ).2.1
  have hVdQb := graph_terminal_span_core_intersection ht hB hS hab hbx hxa' hb
    (Nat.card_pos : 0 < Nat.card F) horders.1 hcard
    hir
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  obtain ⟨ρ,U,hact,hfaith,hnatural,E,hE⟩ := hnat
  let qa := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ a)))
  let ca : BinaryConjugationSection (graphLocalGroup Γ a) (Z Γ a) ⊥ (ρ.comp qa) := {
    section_le := ((source_Z_Q_U ht a).1.trans
      (fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1)).trans (core_le_graphLocalGroup ht a)
    kernel_le := bot_le
    normalized := (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
    coordinates := {
      toFun := fun z => Multiplicative.ofAdd (Additive.ofMul z)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    onto := fun z => ⟨z.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext z
      change z = 1 ↔ (z : Reduction.G₀ L S₀) = 1
      exact Subtype.val_injective.eq_iff.symm
    equivariant := by
      intro g z
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (hact g (Additive.ofMul z)).symm }
  obtain ⟨cb⟩ := reduced_natural_span_section h eβ hres hω hcard horders.2
  let σb := (specialLinearNatural 2 (k := F)).restrictScalars (k := ZMod 2)
  have hfaithb : Function.Injective σb := fun g k he =>
    specialLinearNatural_injective 2 ((LinearMap.restrictScalars_injective (ZMod 2)) he)
  have hdisDV := graph_cartan_outer_fixed_disjoint_of_fields ht hB hS hab heq eα eβ ρ σb hfaithb
    ca cb E (LinearEquiv.refl (ZMod 2) (Fin 2 → F)) hE (fun _ _ => rfl) C hCo hCa₀ hCb₀ hCd
    ea eb horders.2 (hZcard a' hbd) hline hlinex hspan hldisx hωl hTne hTa hTb hDb hVdQb
  have hQdRad := hfixed hn' a' hbd Kd inf_le_right hoKd hKdne
  have hQcores := graph_cartan_common_fixed_cores ht hB hS hal hab hbx hxa' hdr
    (fun v => htwo v 2 (by decide)) eβ el' eα hlarge C hCl hCp hCx hCo hCS hCE hTne hTa hTb hQdRad
  have hQ₀D : Q₀ ≤ D := le_inf
    (hQcores.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))))
    (inf_le_right.trans (centralizer_le inf_le_left))
  have hQ₀N : Q₀ ≤ N := le_inf
    (hQcores.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))))
    (hQcores.trans (inf_le_left.trans inf_le_right))
  have hQ₀H : Q₀ ≤ H := le_inf (hQcores.trans (inf_le_left.trans inf_le_right)) (hQcores.trans inf_le_right)
  have hCdr := le_inf hCd hCr
  obtain ⟨hcdr,hgdr⟩ := path_cartan_complement_at_edge ht hab hdr C hCp hCdr hCo hCS hCE
  have hDRH := graph_cartan_fixed_terminal_intersection ht hB hS hdr (htwo a' 2 (by decide))
    er' C hCl hCdr hcdr hgdr hlkernel hoT hTne (hintersection hn' a' r hdr) hDx
  have hHJ : H = J a' := neighbor_core_intersection_radius_transport hab hbx hxa
    hxa' hdr hrx hax (htwo x 2 (by decide)) hsecond
  have hcentralJ : J beta = Q Γ beta ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) := hsecond.symm.trans hN
  have hVJ : V Γ beta 1 ≤ J beta := hVN.trans hsecond.le
  have hresJ : ⁅J beta,(pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype⁆ ≤ V Γ beta 1 := by
    change ⁅Q Γ beta ⊓ ballKernel Γ beta 2,_⁆ ≤ V Γ beta 1
    rw [←hsecond]; exact hresN
  obtain ⟨hcentl,hVJl,hmovel⟩ := radius_two_profile_transport ht hcentralJ hVJ hresJ l hbl
  obtain ⟨hcentd,hVJd,hmoved⟩ := radius_two_profile_transport ht hcentralJ hVJ hresJ a' hbd
  have hDT : D ≤ centralizer (T : Set (Reduction.G₀ L S₀)) := inf_le_right
  have hDHQ : D ⊓ H = Q₀ := by
    have hCnT : C ≤ normalizer (T : Set (Reduction.G₀ L S₀)) :=
      ((le_centralizer C).trans (centralizer_le (show T ≤ C from inf_le_left))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hCnD : C ≤ normalizer (D : Set (Reduction.G₀ L S₀)) :=
      (le_inf (hCl.trans (stabilizer_normalizes_Q Γ l))
        (hCnT.trans (normalizer_le_normalizer_centralizer T))).trans
        inf_normalizer_le_normalizer_inf
    have hCnH : C ≤ normalizer (H : Set (Reduction.G₀ L S₀)) :=
      (le_inf (hCx.trans (stabilizer_normalizes_Q Γ x)) (hCr.trans (stabilizer_normalizes_Q Γ r))).trans
        inf_normalizer_le_normalizer_inf
    have hh := cartan_fixed_intersection D (Q Γ a') H (V Γ a' 1) T Kd hDT
      (inf_le_right.trans (hHJ.le.trans inf_le_left)) (hCT ▸ le_inf hQ₀D hQ₀H)
      (inf_le_left.trans ((le_inf hCnD hCnH).trans inf_normalizer_le_normalizer_inf))
      (by rw [hHJ]; exact hmoved Kd inf_le_right hoKd) hdisDV
    rwa [←hCT] at hh
  have hDRQ : D ⊓ Q Γ a' = Q₀ := le_antisymm
    ((le_inf inf_le_left hDRH).trans hDHQ.le) (le_inf hQ₀D inf_le_left)
  have hDprod : D = Z Γ l ⊔ Q₀ := by
    change D = Z Γ l ⊔ (D ⊓ Q Γ a') at hDsplit
    simpa only [hDRQ] using hDsplit
  have hJlprod : J l = V Γ l 1 ⊔ Q₀ := by
    have hh := radius_two_odd_decomposition ht l T inf_le_right hoT hVJl
      (hmovel T inf_le_right hoT) hDrad
    change J l = V Γ l 1 ⊔ D at hh
    rw [hDprod] at hh
    simpa only [←sup_assoc,sup_eq_left.mpr (Z_le_V Γ l 1)] using hh
  have hcentJl : J l ≤ centralizer (V Γ l 1 : Set (Reduction.G₀ L S₀)) := hcentl.le.trans inf_le_right
  have hcardH : Nat.card H ≤ Nat.card Q₀ * Nat.card (V Γ a' 1) := by
    rw [hHJ]
    exact graph_radius_order_bound ht (hbl.symm.trans hbd) Q₀ hJlprod hcentJl
  have hQVd : ⁅Q₀,V Γ a' 1⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((hQ₀H.trans hHJ.le).trans (hcentd.le.trans inf_le_right))
  have hVdH : V Γ a' 1 ≤ H := hVJd.trans hHJ.ge
  have hdisQd : Disjoint Q₀ (V Γ a' 1) := hdisDV.mono_left hQ₀D
  let : Finite H := Finite.of_injective (inclusion (inf_le_left.trans (Q_le_stabilizer Γ x)))
    (inclusion_injective _)
  have hHprod : H = Q₀ ⊔ V Γ a' 1 := by
    apply (eq_of_le_of_card_ge (sup_le hQ₀H hVdH) ?_).symm
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQVd)).trans
        (Subgroup.centralizer_le_normalizer _)) hdisQd]
    exact hcardH
  have hHnorm : graphLocalGroup Γ a' ≤ normalizer (H : Set (Reduction.G₀ L S₀)) := by
    rw [hHJ]
    exact (sylowGenerated_le _).trans
      ((le_inf (stabilizer_normalizes_Q Γ a') (stabilizer_le_normalizer_ballKernel Γ a' 2)).trans
        inf_normalizer_le_normalizer_inf)
  have heV (v : Vertex Γ) : IsElementaryAbelian 2 (V Γ v 1) :=
    V_elementary Γ ht.generate (fun z => (source_Z_Q_U ht z).1) (source_kernel_sylow ht hB hS) v
      (by rw [hb3]; decide)
  have heQ := graph_cartan_fixed_elementary ht a' H Q₀ (hHJ.le.trans inf_le_left) hHnorm
    (heV a') hHprod hQVd hdisQd
  have hVbQd : V Γ beta 1 ⊓ Q Γ a' = Z Γ x :=
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv).symm.trans hcentral
  have hdisQb : Disjoint Q₀ (V Γ beta 1) := by
    apply disjoint_def.mpr
    intro z hzQ hzV
    exact disjoint_def.mp hdisQd hzQ
      (CommutingNontrivial.Z_neighbor_le_V Γ hxa'.symm (hVbQd.le ⟨hzV,hzQ.1⟩))
  have hQVb : ⁅Q₀,V Γ beta 1⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hQ₀N.trans (hN.le.trans inf_le_right))
  let : Finite N := Finite.of_injective (inclusion (hNQ.trans (Q_le_stabilizer Γ beta)))
    (inclusion_injective _)
  have hNprod : N = Q₀ ⊔ V Γ beta 1 := by
    apply (eq_of_le_of_card_ge (sup_le hQ₀N hVN) ?_).symm
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQVb)).trans
        (Subgroup.centralizer_le_normalizer _)) hdisQb]
    change Nat.card (Q Γ a ⊓ Q Γ x : Subgroup (Reduction.G₀ L S₀)) ≤ _
    rw [hsecond]
    exact graph_radius_order_bound ht hbl.symm Q₀ hJlprod hcentJl
  let : IsElementaryAbelian 2 Q₀ := heQ
  have hQN : ⁅Q₀,N⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    rw [hNprod]
    exact sup_le (le_centralizer Q₀) (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQVb))
  have hTβne : C ⊓ graphLocalGroup Γ beta ≠ ⊥ := by
    have hh := card_factor eb
    intro he
    rw [he,card_bot] at hh
    omega
  have hoTβ : Odd (Nat.card (C ⊓ graphLocalGroup Γ beta : Subgroup (Reduction.G₀ L S₀))) :=
    hCo.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hBQspan := graph_core_fixed_commutator_le_span ht eβ hsec hn' hF hNQ hresN
    (C ⊓ graphLocalGroup Γ beta) Q₀ inf_le_right hoTβ hTβne hQ₀N hQN
  have hgen := graph_cartan_core_commutator_generation ht hB hS hab hal hlb hbx hxa' hdb eα ex C T
    hCp hCl hCx hCd hCo hCS hCE inf_le_left hoT hTne hTa hTx hNQ
  let : IsElementaryAbelian 2 (V Γ beta 1) := heV beta
  have hZbX : Z Γ beta ≤ Z Γ x := hlinex ▸ le_sup_left
  have hZlV : Z Γ l ≤ V Γ beta 1 := (hline ▸ le_sup_right).trans (hspan ▸ le_sup_left)
  have hZxV : Z Γ x ≤ V Γ beta 1 := hspan ▸ le_sup_right
  have hZlT : ⁅Z Γ l,T⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (by
    intro z hz
    exact centralizer_le (show T ≤ graphLocalGroup Γ l from inf_le_right)
      ((mem_omegaCenterIn_iff _ _).mp (hωl ▸ hz)).2.1)
  have hVspan : V Γ beta 1 = Z Γ l ⊔ Z Γ x := by
    rw [hspan,hline]
    calc
      (Z Γ beta ⊔ Z Γ l) ⊔ Z Γ x = Z Γ l ⊔ (Z Γ beta ⊔ Z Γ x) := by ac_rfl
      _ = _ := by rw [sup_eq_right.mpr hZbX]
  have hVT : ⁅V Γ beta 1,T⁆ ≤ Z Γ x := by
    rw [hVspan]
    apply commutator_sup_le_of_relative_normal (V Γ beta 1) (Z Γ l) (Z Γ x) T (Z Γ x)
      (((le_centralizer (V Γ beta 1)).trans (centralizer_le hZxV)).trans
        (Subgroup.centralizer_le_normalizer _)) hZlV hZxV (hZlT.le.trans bot_le)
    exact le_normalizer_iff_commutator_le_left.mp
      (inf_le_left.trans (hCx.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x)))
  have hBQ := graph_cartan_fixed_commutator_le_central_line ht hB hS a beta a' l x hab.symm hbx C hCx
    hNprod (hN.le.trans inf_le_right) heQ hgen hBQspan hVT hcV.le hZbX
    ((sylowGenerated_le _).trans hNN) hcut.le
  let W := V Γ l 1 ⊔ V Γ a' 1
  have hQW : ⁅Q₀,W⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp
      ((le_inf (hQ₀D.trans inf_le_left) (hQ₀D.trans hDrad)).trans hcentJl))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQVd))
  have hZW : ⁅Z Γ beta,W⁆ = ⊥ := by
    let : IsElementaryAbelian 2 (V Γ l 1) := heV l
    let : IsElementaryAbelian 2 (V Γ a' 1) := heV a'
    have hbVl : Z Γ beta ≤ V Γ l 1 :=
      (hline ▸ le_sup_left).trans (CommutingNontrivial.Z_neighbor_le_V Γ hal.symm)
    have hbVd : Z Γ beta ≤ V Γ a' 1 := hZbX.trans
      (CommutingNontrivial.Z_neighbor_le_V Γ hxa'.symm)
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    exact sup_le ((le_centralizer (V Γ l 1)).trans (centralizer_le hbVl))
      ((le_centralizer (V Γ a' 1)).trans (centralizer_le hbVd))
  have hL := graph_outer_spans_generate_local_group ht hB hS hab hal hlb hbx hxa' hdb hxa.symm hb3
    (htwo beta 2 (by decide)) eβ hir
  have hzero : Q₀ = ⊥ := graph_cartan_fixed_eq_bot_of_core_section ht a beta x l a' eβ hsec hn' hF C
    hNQ hQ₀N hL hQN hQW hBQ hZW (hdisQb.mono_right (Z_le_V Γ beta 1))
  exact ⟨hzero,by simpa only [hzero,sup_bot_eq] using hDprod,
    by simpa only [hzero,bot_sup_eq] using hNprod,
    by simpa only [hzero,bot_sup_eq] using hHprod⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
