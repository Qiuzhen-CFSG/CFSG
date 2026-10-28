module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ExtendedCartanKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeExtendedCartan

/-!
# The remote kernel of the original extended Cartan

The two central neighbor lines span the alpha natural center, forcing the
new alpha-minus-one center out of the original alpha-prime core. Its
Cartan-normalized root image is transitive away from one neighbor. This
puts K_(alpha-minus-one) in the full alpha-prime kernel. The original
field orders identify it with the full Cartan intersection of that kernel
and give K = K_(alpha-minus-one) times K_(alpha-prime).

The same factor avoids the kernels at alpha and alpha+2, and its core
centralizer lies in its second kernel. Both original markings and natural
sections, the distance-three result and the earlier source premises are
retained. The beta-kernel exclusion in 9.10(3), (4)--(6), the exact 5.17
splitting and the final field-two conclusion remain source obligations.

Source: DGS, *Groups and Graphs* (1985), 9.10(2)--(3), printed p.148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The original configuration supplies the exact remote Cartan kernel
and two of the three exclusions in source 9.10(3). -/
theorem reduced_critical_distance_three_remote_kernel
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
                     Q Γ l ⊓ centralizer (T : Set (Reduction.G₀ L S₀)) ≤ ballKernel Γ l 2)) := by
  obtain ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec,
      hsecond,hneighbors,C,hCfix,hCS,hCE,hCo,hCa,ea,eb,hCprod,hdis,hcom,
      hkernels,hfixed,hintersection,hneigh,hdec,l,r,hal,hlb,hdr,hrx,hext,el,ed,er⟩ :=
    reduced_critical_distance_three_extended_cartan h hc hab hd hb h8distance hcomm htriv h8 hob
      Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  have hω := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have horders : Nat.card (Z Γ a) = Nat.card F ^ 2 ∧ Nat.card (Z Γ beta) = Nat.card F := by
    obtain ⟨ρ,T,hact,hfaith,hnatural,E,hE⟩ := hnat
    have hh := linear_natural_neighbor_center_orders ht hB hS hab
      (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
      ρ hact hfaith ⟨T,hnatural⟩
    rw [heq] at hh
    exact hh
  obtain ⟨hline,hldis,hlescape,hlkernel⟩ := reduced_extended_cartan_remote_kernel h hc hab hbx hxa'
    hd hb3 hal hlb hdr hrx hω eβ horders.1 horders.2 C hCfix hext hCo hCS hCE
  refine ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
    x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec,
    hsecond,hneighbors,C,hCfix,hCS,hCE,hCo,hCa,ea,eb,hCprod,hdis,hcom,
    hkernels,hfixed,hintersection,hneigh,hdec,l,r,hal,hlb,hdr,hrx,hext,el,ed,er,
    hline,hldis,hlescape,hlkernel,?_⟩
  intro hn'
  let : Finite C := Finite.of_injective
    (inclusion (hCfix.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))) (inclusion_injective _)
  let : IsMulCommutative C := hCa
  let T := C ⊓ graphLocalGroup Γ l
  let D := C ⊓ graphLocalGroup Γ a'
  have card_factor {H : Subgroup (Reduction.G₀ L S₀)} {k : Type u} [Field k] [Finite k]
      (e : Nonempty (H ≃* kˣ)) : Nat.card H = Nat.card k - 1 := by
    obtain ⟨f⟩ := e
    exact (Nat.card_congr f.toEquiv).trans (Nat.card_units k)
  have hcT : Nat.card T = Nat.card F - 1 := card_factor el
  have hcD : Nat.card D = Nat.card F - 1 := card_factor ed
  have hcC : Nat.card C = (Nat.card F - 1)^2 := by
    rw [hCprod,card_sup_eq_mul_of_normalizes_of_disjoint _ _ ?_ hdis,
      card_factor ea,card_factor eb,heq,pow_two]
    exact (show C ⊓ graphLocalGroup Γ beta ≤ C from inf_le_left).trans
      ((le_centralizer C).trans ((centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _)))
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have bool_eq {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
    cases i <;> cases j <;> cases k <;> first | rfl | exact (hi rfl).elim | exact (hj rfl).elim
  have hbd : beta.type = a'.type := bool_eq hbx.1 hxa'.1.symm
  have hbl : beta.type = l.type := bool_eq hab.1.symm hal.1.symm
  obtain ⟨g,hgd⟩ := (same_orbit_iff Γ beta a').mpr hbd
  obtain ⟨_,e,_,_,_⟩ := local_quotient_parameter_transport ht g hgd
  have hDU := nonbinary_odd_torus_disjoint_kernel ht hB hS hxa'.symm (e.symm.trans eβ) hlarge C hCo
  obtain ⟨hprod,hker,hdTD⟩ := cartan_kernel_factor_of_orders C T D (ballKernel Γ a' 1)
    inf_le_left inf_le_left hlkernel hDU hcC hcT hcD
  have hoT : Odd (Nat.card T) := hCo.of_dvd_nat (card_dvd_of_le (show T ≤ C from inf_le_left))
  have hTne : T ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcT
    omega
  exact ⟨hprod,hker,hdTD,
    hneigh hn' l hbl a hal.symm T inf_le_right hoT,
    odd_subgroup_disjoint_adjacent_kernel ht (hintersection hn' a' x hxa'.symm) T hlkernel hoT,
    hfixed hn' l hbl T inf_le_right hoT hTne⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
