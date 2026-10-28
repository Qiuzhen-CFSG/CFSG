module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeTorusEscape
public import Theory.GroupTheory.Commutator.PointCentralizers

/-!
# The nonbinary distance-three case of DGS 9.8

A noncentral neighboring core element fixes exactly the adjacent central
omega in the natural center. The three-subgroup lemma and coprime
commutator idempotence therefore bound the torus-fixed part of Q_beta by
Q_x. Coprime decomposition gives the actual edge Sylow product
S = [Q_beta,D] Q_x.

For R = [V_beta,V_alpha-prime], its residual-fixed subgroup centralizes
this S and lies in its central omega, hence in Z_beta. Thus R modulo
Z_beta is fully moved by D. The images of R and Z_x in the natural beta
section lie in the same Sylow fixed line. Their coordinate kernel is fixed
by D, so [R,D] lies in Z_x and consequently R lies in Z_x.
This fixed-line argument implements the source's uniqueness of the moved
torus submodule without assuming a splitting of the whole extension.

The original F1.11 application retains both actual markings and natural
actions, and discharges the earlier span premise. In the nonbinary b=3
case it proves V_beta = Z_alpha Z_x, its cube order, and its exact forward
centralizer. It does not assert b=3 or that either field is binary.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.8, printed pp.145--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A neighboring core element outside the local core fixes exactly the
neighboring central omega in the natural center. -/
theorem linear_natural_neighbor_point_centralizer
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    (hz : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) v)),
      (∀ (l : graphLocalGroup (family P) v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      Function.Injective ρ → (∃ S : Sylow 2 SL(2,F), IsSourceNatural ρ S n) →
      ∀ u ∈ Q (family P) w, u ∉ Q (family P) v →
        Z (family P) v ⊓ centralizer ({u} : Set G) = Z (family P) w := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Finite (Z Γ v) := Finite.of_injective (inclusion (Z_le_stabilizer Γ v)) (inclusion_injective _)
  dsimp only
  intro ρ hact hf ⟨S,hnat⟩ u hu hune
  have hcw := (linear_natural_neighbor_center_orders h hB hS hvw hne hz hn hF e
    ρ hact hf ⟨S,hnat⟩).2
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hvw hne e
  have hquad : IsQuadratic ρ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) S T
    exact SL2SylowFixedRecognition.quadratic_conjugate ρ hnat.2.2 g
  obtain ⟨_,hcard,hfix,_⟩ := sourceNatural_coordinates_and_consequences ρ hf T hn hF
    ⟨hnat.1,hnat.2.1,hquad⟩
  let l : H := ⟨u,neighbor_core_le_localGroup h hB hS hvw hu⟩
  change ((Q Γ w).subgroupOf H).map q = (T : Subgroup SL(2,F)) at hT
  have hlT : q l ∈ T := by
    change q l ∈ (T : Subgroup SL(2,F))
    rw [←hT]
    exact mem_map_of_mem q (show l ∈ (Q Γ w).subgroupOf H from hu)
  have hlne : q l ≠ 1 := by
    intro hh
    have hh' : l ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).mp
      (e.injective (hh.trans e.map_one.symm))
    exact hune ((graphLocalGroup_core h v) ▸ mem_map_of_mem H.subtype hh')
  let C := Z Γ v ⊓ centralizer ({u} : Set G)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ Z Γ v from inf_le_left)) (inclusion_injective _)
  let j : C → fixedSpace ρ (zpowers (q l)) := fun z =>
    ⟨Additive.ofMul ⟨z,z.property.1⟩,by
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hact]
      exact mul_inv_eq_iff_eq_mul.mpr (z.property.2 u (Set.mem_singleton u))⟩
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : fixedSpace ρ (zpowers (q l)) => (z.val.toMul : G)) he)
  have hc : Nat.card C ≤ Nat.card (Z Γ w) := by
    have hh := Nat.card_le_card_of_injective j hj
    rw [hfix (q l) hlT hlne,hcard,←hF,←hcw] at hh
    exact hh
  apply (eq_of_le_of_card_ge (show Z Γ w ≤ C from ?_) hc).symm
  apply le_inf
  · exact hz ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hvw.symm
  · intro z hz' a ha
    have hau : a = u := ha
    subst a
    exact CommutingNontrivial.Z_centralizes_Q Γ w (source_Z_Q_U h w).1 hz' u hu

/-- When the neighboring core has the full linear Sylow image, the two
literal vertex cores generate the two-core of their full edge stabilizer. -/
theorem linear_neighbor_core_join_eq_edge_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    Q (family P) v ⊔ Q (family P) w =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 := by
  let Γ := family P
  let := finite_endpoints h
  let H := graphLocalGroup Γ v
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hQwH := neighbor_core_le_localGroup h hB hS hvw
  have hQvE : Q Γ v ≤ E := le_inf (Q_le_stabilizer Γ v)
    ((neighbor_core_le_localGroup h hB hS hvw.symm).trans (sylowGenerated_le _))
  have hQwE : Q Γ w ≤ E := le_inf (hQwH.trans (sylowGenerated_le _)) (Q_le_stabilizer Γ w)
  have hQwS : Q Γ w ≤ E.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 _) hQwE (inf_le_right.trans (stabilizer_normalizes_Q Γ w))
  obtain ⟨T,hT⟩ := local_edge_sylow h hB hS hvw
  change (T : Subgroup H).map H.subtype = E.pCoreIn 2 at hT
  have hQwT : (Q Γ w).subgroupOf H ≤ (T : Subgroup H) := by
    intro z hz
    have hzS : (z : G) ∈ (T : Subgroup H).map H.subtype := hT.symm ▸ hQwS hz
    obtain ⟨y,hy,he⟩ := hzS
    exact H.subtype_injective he ▸ hy
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨R,hR,_⟩ := linear_neighbor_core_sylow_image h hB hS hvw hne e
  change ((Q Γ w).subgroupOf H).map q = (R : Subgroup SL(2,F)) at hR
  let T' := T.mapSurjective hq
  have hRT : (R : Subgroup SL(2,F)) ≤ (T' : Subgroup SL(2,F)) := by
    rw [←hR]
    exact map_mono hQwT
  have hImg : ((Q Γ w).subgroupOf H).map q = (T : Subgroup H).map q :=
    hR.trans (R.is_maximal' T'.isPGroup' hRT).symm
  have hh := congrArg (Subgroup.comap q) hImg
  rw [comap_map_eq,comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal T),hk] at hh
  have hm := congrArg (Subgroup.map H.subtype) hh
  have hcore : (pCore 2 H).map H.subtype = Q Γ v := graphLocalGroup_core h v
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hQwH,hcore,hT] at hm
  exact (sup_comm (Q Γ v) (Q Γ w)).trans hm

open Representation.NormalElementaryQuotient
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The nonbinary distance-three branch of 9.8 on the original source
configuration: actual Sylow product, residual-fixed kernel bound, full
commutator containment and the resulting whole span, order and centralizer.
Both recognized markings and both natural actions remain literal. -/
theorem reduced_critical_distance_three_nonbinary_span
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
              (Q Γ x = V Γ beta 1 ⊔ (Q Γ x ⊓ Q Γ a')) ∧
              (let N := ⁅V Γ beta 1,V Γ a' 1⁆ ⊔ Z Γ x
               N ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (N : Set (Reduction.G₀ L S₀)) ∧
                 ⁅N,graphLocalGroup Γ x⁆ ≤ Z Γ x ∧
                 N ≤ centralizer (Q Γ x : Set (Reduction.G₀ L S₀))) ∧
              ∃ k : graphLocalGroup Γ beta,
                (k : Reduction.G₀ L S₀) • x = a ∧
                V Γ beta 1 = ⁅V Γ beta 1,V Γ a' 1⁆ ⊔
                  (⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)).map
                    (MulAut.conj (k : Reduction.G₀ L S₀)).toMonoidHom ⊔ Z Γ x ∧
                (⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ x →
                  V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
                  V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x) ∧
              ∃ D : Subgroup (Reduction.G₀ L S₀),
                D ≤ graphLocalGroup Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
                Nonempty (D ≃* Fˣ) ∧ Nat.card D = Nat.card F-1 ∧ Odd (Nat.card D) ∧
                D ≤ (pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype ∧
                D ≤ normalizer ((⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)) ∧
                D ≤ normalizer (Z Γ x : Set (Reduction.G₀ L S₀)) ∧
                (2 < Nat.card F → D ≠ ⊥ ∧
                  V Γ beta 1 ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) =
                    V Γ beta 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup Γ beta)).map
                      (graphLocalGroup Γ beta).subtype : Set (Reduction.G₀ L S₀)) ∧
                  (¬ ⁅D,graphLocalGroup Γ x⁆ ≤ Q Γ x) ∧
                  Q Γ beta ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) ≤ Q Γ x ∧
                  (Q Γ beta ⊔ Q Γ x = ⁅Q Γ beta,D⁆ ⊔ Q Γ x) ∧
                  ((stabilizer Γ beta ⊓ stabilizer Γ x).pCoreIn 2 = ⁅Q Γ beta,D⁆ ⊔ Q Γ x) ∧
                  (⁅V Γ beta 1,V Γ a' 1⁆ ⊓
                    centralizer ((pResidual 2 (graphLocalGroup Γ beta)).map
                      (graphLocalGroup Γ beta).subtype : Set (Reduction.G₀ L S₀))) ≤ Z Γ beta ∧
                  (⁅V Γ beta 1,V Γ a' 1⁆ ⊔ Z Γ beta =
                    ⁅⁅V Γ beta 1,V Γ a' 1⁆,D⁆ ⊔ Z Γ beta) ∧
                  ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ x ∧
                  V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
                  V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x) := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,hbx,hxa',hprod,hN,k₀,hk₀,hspan₀,hwhole₀,D,hD,eD,hcard,hodd,hDR,hDnR,hDnZ,hlargeD⟩ :=
    reduced_critical_distance_three_torus_escape h hc hab hd hb3 hcomm htriv h8 hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  change b Γ = 3 at hb3
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hb : 1 < b Γ := by change b Γ = 3 at hb3; omega
  have hω := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
    x,hbx,hxa',hprod,hN,k₀,hk₀,hspan₀,hwhole₀,D,hD,eD,hcard,hodd,hDR,hDnR,hDnZ,?_⟩
  intro hlarge
  obtain ⟨hDne,hfix,hesc⟩ := hlargeD hlarge
  refine ⟨hDne,hfix,hesc,?_⟩
  have hDb : D ≤ graphLocalGroup Γ beta := hD.trans (inf_le_left.trans inf_le_left)
  let : Finite D := Finite.of_injective (inclusion (hDb.trans (sylowGenerated_le _))) (inclusion_injective _)
  let : Finite (Q Γ beta) := Finite.of_injective (inclusion (Q_le_stabilizer Γ beta)) (inclusion_injective _)
  let : Finite (Q Γ x) := Finite.of_injective (inclusion (Q_le_stabilizer Γ x)) (inclusion_injective _)
  let : Finite (Z Γ x) := Finite.of_injective (inclusion (Z_le_stabilizer Γ x)) (inclusion_injective _)
  have hZbD : Z Γ beta ≤ centralizer (D : Set (Reduction.G₀ L S₀)) := by
    intro z hz
    exact centralizer_le hDb ((mem_omegaCenterIn_iff _ _).mp (hω ▸ hz)).2.1
  have hDU : D ≤ normalizer (Q Γ beta : Set (Reduction.G₀ L S₀)) :=
    (hDb.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ beta)
  obtain ⟨k,hkβ,hkx⟩ := graphLocalGroup_transitive ht hB hS beta ⟨x,hbx⟩ ⟨a,hab.symm⟩
  change k • x = a at hkx
  let f := (MulAut.conj k).toMonoidHom
  have hnQ := stabilizer_normalizes_Q Γ beta (sylowGenerated_le _ hkβ)
  have hnZ := CommutingNontrivial.stabilizer_normalizes_Z Γ beta (sylowGenerated_le _ hkβ)
  have hQb : (Q Γ beta).map f = Q Γ beta := mem_normalizer_iff_map_conj_eq.mp hnQ
  have hZb : (Z Γ beta).map f = Z Γ beta := mem_normalizer_iff_map_conj_eq.mp hnZ
  have hQx : (Q Γ x).map f = Q Γ a := by rw [←Q_translate,hkx]
  have hZx : (Z Γ x).map f = Z Γ a := by rw [←Z_translate,hkx]
  have hZU : ⁅Z Γ x,Q Γ beta⁆ ≤ Z Γ beta := by
    have hh : ⁅Z Γ x,Q Γ beta⁆ = Z Γ beta := by
      apply map_injective (f := f) (MulAut.conj k).injective
      rw [map_commutator,hZx,hQb,hZb,commutator_comm]
      exact hcQ
    exact hh.le
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨ρ,Tα,hρ,hfaithα,hnatα,Eα,hEα⟩ := hnat
  have hpa := linear_natural_neighbor_point_centralizer ht hB hS hab
    (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
    ρ hρ hfaithα ⟨Tα,hnatα⟩
  have hpoint : ∀ u ∈ Q Γ beta, u ∉ Q Γ x →
      Z Γ x ⊓ centralizer ({u} : Set (Reduction.G₀ L S₀)) ≤ Z Γ beta := by
    intro u hu hune z hz
    have hu' : f u ∈ Q Γ beta := hQb ▸ mem_map_of_mem f hu
    have hun' : f u ∉ Q Γ a := by
      intro he
      rw [←hQx] at he
      obtain ⟨r,hr,he⟩ := he
      exact hune ((MulAut.conj k).injective he ▸ hr)
    have hz' : f z ∈ Z Γ a ⊓ centralizer ({f u} : Set (Reduction.G₀ L S₀)) := by
      refine ⟨hZx ▸ mem_map_of_mem f hz.1,?_⟩
      apply mem_centralizer_singleton_iff.mpr
      exact ((show Commute u z from hz.2 u (Set.mem_singleton u)).map f).eq.symm
    have hzβ : f z ∈ Z Γ beta := hpa (f u) hu' hun' ▸ hz'
    exact (mem_normalizer_iff.mp hnZ z).mpr hzβ
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
  let cβ := (show BinaryConjugationSection H (V Γ beta 1)
      (V Γ beta 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S₀)))
      (σ.comp q) from hcomp.symm ▸ c)
  obtain ⟨Tfix,hTfix,hZImage,hidx,_⟩ := residual_neighbor_fixed_line ht hB hS hbx
    (core_escape_of_intersection_obstruction Γ (hob x beta hbx.symm)) hω eβ σ
    cβ hfaith T hn hF hnatβ
  have hmove : ¬ Z Γ x ≤ centralizer (D : Set (Reduction.G₀ L S₀)) := by
    intro hcentral
    have hZfix : Z Γ x ≤ centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S₀)) := by
      intro z hz
      exact (hfix ▸ (show z ∈ V Γ beta 1 ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) from
        ⟨CommutingNontrivial.Z_neighbor_le_V Γ hbx hz,hcentral hz⟩)).2
    have hone : (centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S₀))).relIndex (Z Γ x) = 1 :=
      relIndex_eq_one.mpr hZfix
    have hi : (centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S₀))).relIndex (Z Γ x) = Nat.card F := hidx
    omega
  have hfixed := fixed_subgroup_le_of_point_centralizers (Z Γ x) (Z Γ beta) (Q Γ beta) (Q Γ x) D
    ((Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) x).isPGroup) hodd hDnZ hZU hZbD hpoint hmove
  have hsup := sup_eq_commutator_sup_of_fixed_le (Q Γ beta) (Q Γ x) D
    (isPGroup_pCoreIn 2 _) hodd hDU hfixed
  have hedge := linear_neighbor_core_join_eq_edge_core ht hB hS hbx
    (core_escape_of_intersection_obstruction Γ (hob x beta hbx.symm)) eβ
  refine ⟨hfixed,hsup,hedge.symm.trans hsup,?_⟩
  let H := graphLocalGroup Γ beta
  let J := (pResidual 2 H).map H.subtype
  let R := ⁅V Γ beta 1,V Γ a' 1⁆
  let R₀ := R ⊓ centralizer (J : Set (Reduction.G₀ L S₀))
  let S := (stabilizer Γ beta ⊓ stabilizer Γ x).pCoreIn 2
  have hJ : H ≤ normalizer (J : Set (Reduction.G₀ L S₀)) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hcommJ : ⁅Q Γ beta,D⁆ ≤ J :=
    (commutator_mono (core_le_graphLocalGroup ht beta) hDR).trans
      (le_normalizer_iff_commutator_le_right.mp hJ)
  have hR₀Q : R₀ ≤ Q Γ x := inf_le_left.trans (le_sup_left.trans hN.1)
  have hR₀C : R₀ ≤ centralizer (S : Set (Reduction.G₀ L S₀)) := by
    apply le_centralizer_iff.mpr
    rw [show S = ⁅Q Γ beta,D⁆ ⊔ Q Γ x from hedge.symm.trans hsup]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le hcommJ)))
      (le_centralizer_iff.mp (inf_le_left.trans (le_sup_left.trans hN.2.2.2)))
  have hdist : (graph Γ).dist a' beta = 2 := by
    rw [SimpleGraph.dist_comm]
    change (graph Γ).dist beta a' + 1 = b Γ at hd
    change b Γ = 3 at hb3
    omega
  have hRV : R ≤ V Γ beta 1 := le_normalizer_iff_commutator_le_left.mp
    ((V_le_stabilizer Γ ht.generate a' beta (by omega)).trans (stabilizer_normalizes_V Γ beta 1))
  have hb2 : 2 < b Γ := by change b Γ = 3 at hb3; omega
  obtain ⟨_,_,hVe,_,_⟩ := reduced_neighbor_quadratic h (Reduction.reduced_kernel_sylow h) hc hab.symm hb2 hd
  let := hVe
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht hS hbx
  have hTS := sylow_image_eq_edge_core (stabilizer Γ beta) (stabilizer Γ beta ⊓ stabilizer Γ x)
    inf_le_left (source_edge_core_sylow ht hB hbx) T hT
  have hR₀S : R₀ ≤ S := hR₀Q.trans (le_sup_right.trans hedge.le)
  have hR₀Ω : R₀ ≤ omegaCenterIn S := by
    intro r hr
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hR₀S hr,hR₀C hr,
      elemPow_eq_one_of_isElementaryAbelian (A := V Γ beta 1) r (hRV hr.1)⟩
  have hΩZ : omegaCenterIn S ≤ Z Γ beta := by
    change omegaCenterIn ((stabilizer Γ beta ⊓ stabilizer Γ x).pCoreIn 2) ≤ Z Γ beta
    rw [←hTS]
    exact le_iSup (fun T : Sylow 2 (stabilizer Γ beta) =>
      omegaCenterIn ((T : Subgroup (stabilizer Γ beta)).map (stabilizer Γ beta).subtype)) T
  have hR₀Z : R₀ ≤ Z Γ beta := hR₀Ω.trans hΩZ
  refine ⟨hR₀Z,?_⟩
  have hRD : R ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) ≤ Z Γ beta := by
    intro r hr
    exact hR₀Z ⟨hr.1,(hfix ▸ (show r ∈ V Γ beta 1 ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) from
      ⟨hRV hr.1,hr.2⟩)).2⟩
  let : Finite R := Finite.of_injective (inclusion (le_sup_left.trans hN.1)) (inclusion_injective _)
  have hRmove := sup_eq_commutator_sup_of_fixed_le R (Z Γ beta) D
    ((IsElementaryAbelian.isPGroup 2 (V Γ beta 1)).to_le hRV) hodd hDnR hRD
  refine ⟨hRmove,?_⟩
  have hRim : cβ.imageSpace R ≤ cβ.imageSpace (Z Γ x) := by
    have hZI : cβ.imageSpace (Z Γ x) = fixedSpace σ Tfix := hZImage
    rw [hZI]
    intro z hz t
    obtain ⟨l,hl,he⟩ := show (t : SL(2,F)) ∈ ((Q Γ x).subgroupOf (graphLocalGroup Γ beta)).map q from
      hTfix.symm ▸ t.property
    change σ (t : SL(2,F)) z = z
    rw [←he]
    apply cβ.fixed_on_imageSpace_of_commutator_le (Q Γ x) R ?_ l hl z hz
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (le_sup_left.trans hN.2.2.2))).le.trans bot_le
  let K₀ := V Γ beta 1 ⊓ centralizer (J : Set (Reduction.G₀ L S₀))
  have hpre : R ≤ Z Γ x ⊔ K₀ := by
    intro r hr
    let rV : V Γ beta 1 := ⟨r,hRV hr⟩
    obtain ⟨z,hz,he⟩ := (cβ.mem_imageSpace_iff (Z Γ x) _).mp
      (hRim ((cβ.mem_imageSpace_iff R _).mpr ⟨rV,hr,rfl⟩))
    have hk : ((z⁻¹*rV : V Γ beta 1) : Reduction.G₀ L S₀) ∈ K₀ := by
      apply (cβ.coordinates_eq_one_iff _).mp
      rw [map_mul,map_inv,Multiplicative.toAdd.injective he,inv_mul_cancel]
    have hh := (Z Γ x ⊔ K₀).mul_mem (mem_sup_left hz) (mem_sup_right hk)
    simpa using hh
  have hK₀D : K₀ ≤ centralizer (D : Set (Reduction.G₀ L S₀)) :=
    inf_le_right.trans (centralizer_le hDR)
  have hZV := CommutingNontrivial.Z_neighbor_le_V Γ hbx
  have hbound : ⁅Z Γ x ⊔ K₀,D⁆ ≤ Z Γ x :=
    commutator_sup_le_of_relative_normal (V Γ beta 1) (Z Γ x) K₀ D (Z Γ x)
      (((le_centralizer (V Γ beta 1)).trans (centralizer_le hZV)).trans (Subgroup.centralizer_le_normalizer _))
      hZV inf_le_left (le_normalizer_iff_commutator_le_left.mp hDnZ)
      ((commutator_eq_bot_iff_le_centralizer.mpr hK₀D).le.trans bot_le)
  have hR : R ≤ Z Γ x := (le_sup_left.trans hRmove.le).trans (sup_le
    ((commutator_mono hpre le_rfl).trans hbound)
    (hω ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hbx))
  exact ⟨hR,hwhole₀ hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
