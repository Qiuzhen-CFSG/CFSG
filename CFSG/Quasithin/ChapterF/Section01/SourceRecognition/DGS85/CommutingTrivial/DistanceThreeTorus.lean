module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathLength
public import Theory.GroupTheory.AmalgamGraph.PathComplement
public import Theory.Representation.BinaryConjugationSection.SL2OddFixed

/-!
# The actual path torus in the distance-three branch

Adjacent linear markings transport to the endpoint of the first nonregular
path. Source 6.8 and the adjacent-core obstruction make its length at least
four, giving the short-path transitivity used in 9.8.

The path supplement and Schur--Zassenhaus place a full edge complement inside
the path fixer. Intersecting with the intrinsic beta actor gives a complement
to its actual Sylow subgroup; the diagonal quotient identifies it with the
units of the same beta field. On the distance-two path from beta to alpha-prime
this torus normalizes both the commutator R and the middle center Z_x.
When the field is nonbinary, its fixed subgroup on the whole V_beta is
exactly the original residual centralizer, by the natural coordinates.
The original F1.11 application retains both recognized markings, both natural
actions, and the preceding middle-module reduction.

This supplies the torus placement in the nonbinary part of 9.8; the remaining
torus displacement argument, 5.17 splitting and 9.10--9.11 conclusions are
not asserted here. Source: Delgado--Goldschmidt--Stellmacher, Groups and
Graphs (1985), 6.7--6.8, pp.123--124, and 9.8, pp.145--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Actual adjacent linear markings and source 6.5 give path transitivity
through length four, without original-endpoint markings. -/
theorem adjacent_linear_short_path_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {a beta : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F))
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,K)) :
    ∀ v : Vertex (family P), ∀ k ≤ 4, RootPathTransitive (graph (family P)) G v k := by
  obtain ⟨n,_,ht,i,p,hp,hn,_,_⟩ := source_first_nonregular_path h hS
  have hnot : ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val := by
    intro hh
    exact hn (fun x y hx hy => hh ⟨x,hx.1⟩ ⟨y,hy.1⟩ hx.2 hy.2)
  have hcore : (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint := by
    by_cases he : a.type = p.endpoint.type
    · obtain ⟨g,hg⟩ := (same_orbit_iff (family P) a p.endpoint).mpr he
      obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
      exact source_path_core_le_endpoint_core h hB hS (source_rankOne_branching h)
        (ht _ _ le_rfl) p hp (f.symm.trans ea) hnot
    · have he' : beta.type = p.endpoint.type := by
        have hh := hab.1
        cases ha : a.type <;> cases hb : beta.type <;> cases hc : p.endpoint.type <;> simp_all
      obtain ⟨g,hg⟩ := (same_orbit_iff (family P) beta p.endpoint).mpr he'
      obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
      exact source_path_core_le_endpoint_core h hB hS (source_rankOne_branching h)
        (ht _ _ le_rfl) p hp (f.symm.trans eb) hnot
  have hlong := source_path_length_ge_four_of_core h hB p hp hcore hob
  exact fun v k hk => ht v k (hk.trans hlong)

/-- The path fixer contains a torus of the intrinsic local actor,
isomorphic to the units of its actual marked field. -/
theorem linear_path_torus
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v beta x : Vertex (family P)} {n : ℕ}
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (hbx : (graph (family P)).Adj beta x)
    (hb : beta ∈ p.vertices) (hx : x ∈ p.vertices)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F)) :
    ∃ D : Subgroup G, D ≤ graphLocalGroup (family P) beta ⊓ pathStabilizer (family P) p ∧
      Nonempty (D ≃* Fˣ) := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ beta
  let E := stabilizer Γ beta ⊓ stabilizer Γ x
  let S := E.pCoreIn 2
  let A := pathStabilizer Γ p
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer Γ beta from inf_le_left)) (inclusion_injective _)
  have hAE : A ≤ E := pathStabilizer_le_edge Γ p hb hx
  have hES : E ≤ normalizer (S : Set G) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hprod := source_path_edge_product h hB (source_rankOne_branching h) ht p hp hbx hb hx
  have hgen : A ⊔ S = E := by
    apply SetLike.coe_injective
    rw [coe_mul_of_left_le_normalizer_right A S (hAE.trans hES)]
    exact hprod.symm
  obtain ⟨C,hCA,hdis,hCS,_⟩ := exists_complement_le_of_core_supplement 2 E A hAE
    (source_edge_core_sylow h hB hbx) hgen
  obtain ⟨R,hR⟩ := local_edge_sylow h hB hS hbx
  change (R : Subgroup H).map H.subtype = S at hR
  have hSH : S ≤ H := hR ▸ map_subtype_le _
  have hR' : (R : Subgroup H) = S.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hSH,hR]
  have hN (l : H) : l ∈ normalizer (R : Set H) ↔ (l : G) ∈ E := by
    change l ∈ normalizer ((R : Subgroup H) : Set H) ↔ _
    rw [hR',←subgroupOf_normalizer_eq hSH]
    change (l : G) ∈ normalizer (S : Set G) ↔ _
    constructor
    · intro hl
      exact (local_edge_core_normalizer h hB hS hbx).le ⟨sylowGenerated_le _ l.property,hl⟩
    · exact fun hl => hES hl
  let D := C ⊓ H
  let DH := D.subgroupOf H
  have hDH : D ≤ H := inf_le_right
  have hDN : DH ≤ normalizer (R : Set H) := fun l hl => (hN l).mpr (hAE (hCA hl.1))
  have hd : Disjoint (R : Subgroup H) DH := by
    apply disjoint_def.mpr
    intro l hl hlD
    apply Subtype.ext
    apply disjoint_def.mp hdis hlD.1
    change (l : G) ∈ S
    rw [←hR]
    exact mem_map_of_mem H.subtype hl
  have hs : (R : Subgroup H) ⊔ DH = normalizer (R : Set H) := by
    apply le_antisymm (sup_le (R : Subgroup H).le_normalizer hDN)
    intro l hl
    have hlE := (hN l).mp hl
    have hm : (l : G) ∈ (C : Set G) * (S : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right C S ((hCA.trans hAE).trans hES),hCS]
      exact hlE
    obtain ⟨c,hc,s,hs,hcs⟩ := hm
    have hcH : c ∈ H := by
      have he : c = (l : G)*s⁻¹ := by rw [←hcs,mul_inv_cancel_right]
      rw [he]
      exact H.mul_mem l.property (H.inv_mem (hSH hs))
    have hsR : (⟨s,hSH hs⟩ : H) ∈ R := by change (⟨s,hSH hs⟩ : H) ∈ (R : Subgroup H); rw [hR']; exact hs
    have hcD : (⟨c,hcH⟩ : H) ∈ DH := ⟨hc,hcH⟩
    have hh := ((R : Subgroup H) ⊔ DH).mul_mem (mem_sup_right hcD) (mem_sup_left hsR)
    exact (show (⟨c,hcH⟩ : H)*⟨s,hSH hs⟩ = l from Subtype.ext hcs) ▸ hh
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨f⟩ := Matrix.SpecialLinearGroup.sylow_normalizer_complement_equiv_units q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) R
    (hk ▸ pCore_isPGroup.le_sylow_of_normal R) DH hDN hd hs
  exact ⟨D,le_inf hDH (inf_le_left.trans hCA),
    ⟨(subgroupOfEquivOfLe hDH).symm.trans f⟩⟩

/-- The torus used in 9.8 fixes beta, the middle vertex and alpha-prime,
and normalizes their literal commutator and middle center. -/
theorem distance_three_torus
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {beta x a' : Vertex (family P)}
    (hbx : (graph (family P)).Adj beta x) (hxa' : (graph (family P)).Adj x a')
    (hd : (graph (family P)).dist beta a' = 2)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,K)) :
    let Γ := family P
    let R := ⁅V Γ beta 1,V Γ a' 1⁆
    ∃ D : Subgroup G,
      D ≤ graphLocalGroup Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
      Nonempty (D ≃* Fˣ) ∧ Nat.card D = Nat.card F - 1 ∧ Odd (Nat.card D) ∧
      D ≤ (pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype ∧
      D ≤ normalizer (R : Set G) ∧ D ≤ normalizer (Z Γ x : Set G) ∧
      (2 < Nat.card F → D ≠ ⊥) := by
  let Γ := family P
  let H := graphLocalGroup Γ beta
  let : ∀ i, Finite (Γ i) := finite_endpoints h
  let p : BasedWalk (graph Γ) 2 beta := ⟨⟨x,hbx⟩,⟨⟨a',hxa'⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := nonbacktracking_of_geodesic p hd
  have ht := adjacent_linear_short_path_transitive h hB hS hob hbx eb ex beta 2 (by omega)
  obtain ⟨D,hD,⟨eD⟩⟩ := linear_path_torus h hB hS p hp ht hbx
    (by simp [p,BasedWalk.vertices]) (by simp [p,BasedWalk.vertices]) eb
  have hDb : D ≤ H := hD.trans inf_le_left
  have hDx : D ≤ stabilizer Γ x := fun d hd => hD hd |>.2 x (by simp [p,BasedWalk.vertices])
  have hDa' : D ≤ stabilizer Γ a' := fun d hd => hD hd |>.2 a' (by simp [p,BasedWalk.vertices])
  have hc : Nat.card D = Nat.card F-1 := by
    rw [Nat.card_congr eD.toEquiv, Nat.card_units]
  have ho : Odd (Nat.card D) := by
    rw [hc,hF]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega : n ≠ 0)) odd_one
  have hDR : D ≤ (pResidual 2 H).map H.subtype := by
    intro d hd
    let l : H := ⟨d,hDb hd⟩
    change H.subtype l ∈ (pResidual 2 H).map H.subtype
    apply mem_map_of_mem H.subtype
    apply mem_pResidual_of_orderOf_coprime
    have hodd : Odd (orderOf l) := by
      rw [Subgroup.orderOf_mk]
      apply ho.of_dvd_nat
      simpa only [Subgroup.orderOf_mk] using
        (_root_.orderOf_dvd_natCard (⟨d,hd⟩ : D))
    exact hodd.coprime_two_left
  refine ⟨D,le_inf (le_inf hDb hDx) hDa',⟨eD⟩,hc,ho,hDR,?_,
    hDx.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x),?_⟩
  · intro d hd
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (stabilizer_normalizes_V Γ beta 1 (sylowGenerated_le _ (hDb hd))),
      mem_normalizer_iff_map_conj_eq.mp (stabilizer_normalizes_V Γ a' 1 (hDa' hd))]
  · intro hlarge he
    rw [he, card_bot] at hc
    omega

open Representation.NormalElementaryQuotient
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The literal F1.11 distance-three configuration constructs the torus
normalizing its commutator, with both markings, natural sections and
the full middle-module reduction retained. -/
theorem reduced_critical_distance_three_torus
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb3 : b (Reduction.reducedFamily L S₀) = 3)
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
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
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
            letI : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).Adj x a' ∧
              (Q Γ x = V Γ beta 1 ⊔ (Q Γ x ⊓ Q Γ a')) ∧
              (let N := ⁅V Γ beta 1,V Γ a' 1⁆ ⊔ Z Γ x
               N ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (N : Set (Reduction.G₀ L S₀)) ∧
                 ⁅N,graphLocalGroup Γ x⁆ ≤ Z Γ x ∧
                 N ≤ centralizer (Q Γ x : Set (Reduction.G₀ L S₀))) ∧
              ∃ D : Subgroup (Reduction.G₀ L S₀),
                D ≤ graphLocalGroup Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
                Nonempty (D ≃* Fˣ) ∧ Nat.card D = Nat.card F-1 ∧ Odd (Nat.card D) ∧
                D ≤ (pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype ∧
                D ≤ normalizer ((⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)) ∧
                D ≤ normalizer (Z Γ x : Set (Reduction.G₀ L S₀)) ∧
                (2 < Nat.card F → D ≠ ⊥ ∧
                  V Γ beta 1 ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) =
                    V Γ beta 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup Γ beta)).map
                      (graphLocalGroup Γ beta).subtype : Set (Reduction.G₀ L S₀))) := by
  have hb : 1 < b (Reduction.reducedFamily L S₀) := by omega
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat⟩ :=
    reduced_critical_recognized_sections h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hdist : (graph (Reduction.reducedFamily L S₀)).dist beta a' = 2 := by omega
  obtain ⟨x,hbx,hxa',t,htb,hta',ht2⟩ :=
    linear_distance_two_exchange ht hB hS hab hdist eα
  have htypes : beta.type = a'.type := by
    apply (even_dist_iff Γ ht.generate beta a').mp
    exact ⟨1,hdist⟩
  obtain ⟨g,hgb,hga⟩ := same_type_edge_transport Γ hab hxa' htypes
  obtain ⟨_,f',_,_,_⟩ := local_quotient_parameter_transport ht g hgb
  obtain ⟨_,fx,_,_,_⟩ := local_quotient_parameter_transport ht g hga
  have hω := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hω' : Z Γ a' = omegaCenterIn (graphLocalGroup Γ a') := by
    have hh := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    change Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) at hω
    rw [←hgb,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hω]
  have hcV' : ⁅Q Γ a',V Γ a' 1⁆ = Z Γ a' := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcV
    rwa [map_commutator,←Q_translate,←V_translate,←Z_translate,hgb] at hh
  obtain ⟨hprod,hNQ,hLnN,hNL,hNC⟩ :=
    distance_three_commutator_middle_reduction ht hB hS hob hbx hxa' hdist hb3
      (f'.symm.trans eβ) (fx.symm.trans eα) hi hcV hcV' hω hω'
  obtain ⟨D,hD,eD,hcard,hodd,hDR,hDnR,hDnZ,hDne⟩ :=
    distance_three_torus ht hB hS hob hbx hxa' hdist hn hF eβ (fx.symm.trans eα)
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,x,hbx,hxa',hprod,
    ⟨hNQ,hLnN,hNL,hNC⟩,D,hD,eD,hcard,hodd,hDR,hDnR,hDnZ,?_⟩
  intro hlarge
  refine ⟨hDne hlarge,?_⟩
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,σ,T,hσ,hfaith,hnatβ,E,hE⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcomp : σ.comp q = fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨_,_,⟨c⟩,_⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
  exact BinaryConjugationSection.natural_odd_fixed_eq_kernel H (V Γ beta 1) _ q
    (hk ▸ pCore_isPGroup) σ (hcomp.symm ▸ c) E hE D
    (hD.trans (inf_le_left.trans inf_le_left)) hodd (hDne hlarge)
    (inf_le_right.trans (centralizer_le hDR))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
