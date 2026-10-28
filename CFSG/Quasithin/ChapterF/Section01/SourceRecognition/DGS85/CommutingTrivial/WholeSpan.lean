module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CommutatorDichotomy

/-!
# DGS 9.8 at critical distance greater than three

Both alternatives of the normal-commutator dichotomy bound the original
neighborhood span by q^3. In the central alternative, the opposite full-index
actor and its conjugate span the terminal neighborhood using just two centers;
conjugacy transports the order bound back to beta. The actual natural residual
section gives a two-center subgroup of order q^3, so the bound is sharp and
V_beta = Z_alpha Z_(alpha+2).

The original forward and reciprocal centralizer indices then identify both
path centralizers. Since the commutator lies in both elementary spans, this
gives [V_beta,V_alpha-prime] <= Z_(alpha-prime-1) intersect Z_(alpha+2).
The source application constructs both markings and retains both natural
actions, the literal quotient maps, and the earlier catalogue, Chapter 8 and
6.5 inputs. The b=3 part of 9.8, cubic splitting in 5.17, and the terminal
9.10--9.11 distance and field conclusions remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.8, printed pp.145--146; 9.3--9.6, printed pp.142--144.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

private theorem two_centers_card_le_cube
    {G : Type*} [Group G] (A B C S : Subgroup G) [Finite S] [IsMulCommutative S]
    {q : ℕ} (hq : 0 < q) (hA : A ≤ S) (hB : B ≤ S) (hCA : C ≤ A) (hCB : C ≤ B)
    (hcA : Nat.card A = q^2) (hcB : Nat.card B = q^2) (hcC : Nat.card C = q)
    (hs : S = A ⊔ B) : Nat.card S ≤ q^3 := by
  let : Finite B := Finite.of_injective (inclusion hB) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hA) (inclusion_injective _)
  have hiCB : C.relIndex B = q := by
    have hh := relIndex_mul_card_of_le hCB
    rw [hcB,hcC,pow_two] at hh
    nlinarith
  have hn : A ≤ normalizer (B : Set G) := (hA.trans (le_centralizer S)).trans
    ((centralizer_le hB).trans (Subgroup.centralizer_le_normalizer _))
  have hiAS : A.relIndex S ≤ q := by
    rw [hs,sup_comm,relIndex_sup_of_normalizes B A hn]
    exact (relIndex_le_of_le_left (L := B) hCA (by rw [hiCB]; omega)).trans_eq hiCB
  have hh := relIndex_mul_card_of_le hA
  rw [hcA] at hh
  calc
    Nat.card S = A.relIndex S * q^2 := hh.symm
    _ ≤ q*q^2 := Nat.mul_le_mul_right _ hiAS
    _ = q^3 := by ring

/-- A commutator trapped in a neighboring center already bounds the whole
span by the cube of the actual field order. No extension splitting is used. -/
theorem linear_neighborhood_card_bound_of_commutator
    {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {w v : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hz : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    (hcore : ⁅Q (family P) w,V (family P) w 1⁆ ≤ Z (family P) w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (A : Subgroup G) (hAH : A ≤ graphLocalGroup (family P) w) (hpA : IsPGroup 2 A)
    (hi : (Q (family P) w).relIndex A = Nat.card F)
    (hAv : A ≤ stabilizer (family P) v)
    (hR : ⁅V (family P) w 1,A⁆ ≤ Z (family P) v)
    (hcv : Nat.card (Z (family P) v) = Nat.card F ^ 2)
    (hcw : Nat.card (Z (family P) w) = Nat.card F)
    [Finite (V (family P) w 1)] [IsMulCommutative (V (family P) w 1)] :
    Nat.card (V (family P) w 1) ≤ Nat.card F ^ 3 := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ w
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨T,hT⟩ := local_quotient_neighbor_stabilizer h hB hS hv e
  obtain ⟨t,ht⟩ := SetLike.exists_not_mem_of_ne_top (normalizer (T : Set SL(2,F)))
    (Matrix.SpecialLinearGroup.sylow_normalizer_ne_top T)
  obtain ⟨g,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) t
  have hgv : (g : G) • v ≠ v := fun he => ht ((hT g).mpr he)
  have hgw : (g : G) • w = w := sylowGenerated_le _ g.property
  have hZw : Z Γ w ≤ Z Γ v := hz ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hv
  have hs := linear_neighborhood_commutator_span h hB hS hv hZw hcore e A hAH hpA hi hAv g hgv
  let f := (MulAut.conj (g : G)).toMonoidHom
  let D := (Z Γ v).map f
  have hZm : (Z Γ w).map f = Z Γ w := by rw [←Z_translate,hgw]
  have hVm : (V Γ w 1).map f = V Γ w 1 := by rw [←V_translate,hgw]
  have hZV := CommutingNontrivial.Z_neighbor_le_V Γ hv
  have hDV : D ≤ V Γ w 1 := (map_mono hZV).trans_eq hVm
  have hZD : Z Γ w ≤ D := hZm ▸ map_mono hZw
  have hcd : Nat.card D = Nat.card F ^ 2 :=
    (card_map_of_injective (K := Z Γ v) (f := f) (MulAut.conj (g : G)).injective).trans hcv
  have hspan : V Γ w 1 = Z Γ v ⊔ D := by
    apply le_antisymm ?_ (sup_le hZV hDV)
    rw [hs]
    exact sup_le (sup_le (hR.trans le_sup_left) ((map_mono hR).trans le_sup_right)) le_sup_left
  exact two_centers_card_le_cube _ _ _ _ Nat.card_pos hZV hDV hZw hZD hcv hcd hcw hspan

private theorem centralizer_of_cube_card
    {G : Type*} [Group G] (W D B : Subgroup G) [Finite W]
    {q : ℕ} (hq : 0 < q) (hBW : B ≤ W) (hBC : B ≤ centralizer (D : Set G))
    (hcW : Nat.card W = q^3) (hcB : Nat.card B = q^2)
    (hi : (centralizer (D : Set G)).relIndex W = q) :
    W ⊓ centralizer (D : Set G) = B := by
  let C := W ⊓ centralizer (D : Set G)
  let : Finite C := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hh := relIndex_mul_card_of_le (show C ≤ W from inf_le_left)
  change (W ⊓ centralizer (D : Set G)).relIndex W * Nat.card C = Nat.card W at hh
  rw [inf_relIndex_left,hi,hcW] at hh
  have hc : Nat.card C = q^2 := by nlinarith
  exact (eq_of_le_of_card_ge (le_inf hBW hBC) (by change Nat.card C ≤ Nat.card B; rw [hc,hcB])).symm

/-- DGS 9.8 for b > 3 on the original reduced critical configuration:
the whole span, its exact cube order, both literal centralizers, and both
commutator containments. Earlier-source inputs and both natural actions
are retained. -/
theorem reduced_critical_large_distance_whole_span
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
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
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧ NaturalResidualSection h beta eβ n ∧
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
            ∃ x v : Vertex Γ,
              (graph Γ).Adj beta x ∧ (graph Γ).dist x a' + 2 = b Γ ∧
              (graph Γ).Adj a' v ∧ (graph Γ).dist beta v + 2 = b Γ ∧
              V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
              V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x ∧
              V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) = Z Γ v ∧
              ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ v ⊓ Z Γ x := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      v,w,r,hv,hw,hr,hne,hdav,hdaw,hdbv,hdbw,hdbr,
      ew,hresw,hiW,hgen,hsupp,hnorm,hDQ,hbound,hpair,hDV,hdich⟩ :=
    reduced_critical_commutator_dichotomy h hc hab hd hb hcomm h8 hob Mα Mβ Mα' Mαsource
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
  have hZ := fun x => (source_Z_Q_U ht x).1
  have hSyl := Reduction.reduced_kernel_sylow h
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have hb2 : 2 < b Γ := by change 3 < b Γ at hb; omega
  change (graph Γ).dist beta w + 3 = b Γ at hdbw
  change (graph Γ).dist beta v + 2 = b Γ at hdbv
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  obtain ⟨hodd,_,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  have hbw : beta.type = w.type := by
    apply (even_dist_iff Γ ht.generate beta w).mp
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    exact ⟨k-1,by omega⟩
  have hba' : beta.type = a'.type := by
    apply (even_dist_iff Γ ht.generate beta a').mp
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    exact ⟨k,by omega⟩
  let := Z_elementary Γ hZ a
  obtain ⟨ρ,T,hact,hfaith,hna,E,hE⟩ := hnat
  obtain ⟨hca,hcb⟩ := linear_natural_neighbor_center_orders ht hB hS hab
    (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
    ρ hact hfaith ⟨T,hna⟩
  rw [heq] at hca hcb
  have hfinite (y : Vertex Γ) : Finite (V Γ y 1) := Finite.of_injective
    (inclusion ((V_le_Q Γ ht.generate hZ hSyl y (r := 1) hb1).trans (Q_le_stabilizer Γ y)))
    (inclusion_injective _)
  let := hfinite beta
  let := hfinite a'
  let := hfinite w
  let helem (y : Vertex Γ) : IsElementaryAbelian 2 (V Γ y 1) :=
    V_elementary Γ ht.generate hZ hSyl y (r := 1) (by simpa using hb2)
  let := helem beta
  let := helem a'
  let := helem w
  obtain ⟨g,hgw,hgv⟩ := same_type_edge_transport Γ hab hw hbw
  obtain ⟨k,hka',hkv⟩ := same_type_edge_transport Γ hab hv.symm hba'
  have htransomega (t : Reduction.G₀ L S₀) (y : Vertex Γ) (hy : t • beta = y) :
      Z Γ y = omegaCenterIn (graphLocalGroup Γ y) := by
    have hh := graphLocalGroup_conjugate ht t beta
    change graphLocalGroup Γ (t • beta) = (graphLocalGroup Γ beta).map (MulAut.conj t).toMonoidHom at hh
    change Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) at hω
    rw [←hy,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj t).injective,hω]
  have htranscard (t : Reduction.G₀ L S₀) (y z : Vertex Γ) (hy : t • y = z) :
      Nat.card (Z Γ z) = Nat.card (Z Γ y) := by
    have hh := card_map_of_injective (K := Z Γ y)
      (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
    rwa [←Z_translate,hy] at hh
  have hωw := htransomega g w hgw
  have hωa' := htransomega k a' hka'
  have hcv := (htranscard g a v hgv).trans hca
  have hcw := (htranscard g beta w hgw).trans hcb
  have hca' := (htranscard k beta a' hka').trans hcb
  have hVcard (t : Reduction.G₀ L S₀) (y : Vertex Γ) (hy : t • beta = y) :
      Nat.card (V Γ y 1) = Nat.card (V Γ beta 1) := by
    have hh := card_map_of_injective (K := V Γ beta 1)
      (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
    rwa [←V_translate,hy] at hh
  have hupper : Nat.card (V Γ beta 1) ≤ Nat.card F ^ 3 := by
    rcases hdich with ⟨_,hwhole⟩ | hR
    · have hZv := CommutingNontrivial.Z_neighbor_le_V Γ hw.symm
      have hZr := CommutingNontrivial.Z_neighbor_le_V Γ hr
      obtain ⟨t,ht',htr⟩ := graphLocalGroup_transitive ht hB hS w ⟨v,hw.symm⟩ ⟨r,hr⟩
      have hcr := (htranscard t v r htr).trans hcv
      rw [←hVcard g w hgw]
      exact two_centers_card_le_cube _ _ _ _ Nat.card_pos hZv hZr
        (hωw ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hw.symm)
        (hωw ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hr) hcv hcr hcw hwhole
    · have hcVa' : ⁅Q Γ a',V Γ a' 1⁆ = Z Γ a' := by
        have hh := congrArg (Subgroup.map (MulAut.conj k).toMonoidHom) hcV
        rwa [map_commutator,←Q_translate,←V_translate,←Z_translate,hka'] at hh
      have hRv : ⁅V Γ a' 1,V Γ beta 1⁆ ≤ Z Γ v := by
        rw [commutator_comm]
        exact hR.trans (hωw ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hw.symm)
      obtain ⟨_,fa',_,_,_⟩ := local_quotient_parameter_transport ht k hka'
      let : IsMulCommutative (V (family (fun i => (Reduction.P₀ L S₀ i).subgroupOf (Reduction.G₀ L S₀))) a' 1) := (helem a').toIsMulCommutative
      let : Finite (V (family (fun i => (Reduction.P₀ L S₀ i).subgroupOf (Reduction.G₀ L S₀))) a' 1) := hfinite a'
      have hu := linear_neighborhood_card_bound_of_commutator ht hB hS hv hωa' hcVa'.le
        (fa'.symm.trans eβ) (V Γ beta 1)
        (neighbor_le_graphLocalGroup ht hSyl beta a' hb1 hd.le)
        (IsElementaryAbelian.isPGroup 2 _) hi
        (V_le_stabilizer Γ ht.generate beta v (by omega)) hRv hcv hca'
      rw [←hVcard k a' hka']
      exact hu
  have hneβ : a' ≠ beta := by intro he; rw [he,SimpleGraph.dist_self] at hd; omega
  obtain ⟨x,hx,hxd⟩ := exists_predecessor Γ ht.generate a' beta hneβ
  have hdx : (graph Γ).dist x a' + 2 = b Γ := by
    rw [SimpleGraph.dist_comm (u := x) (v := a')]
    rw [SimpleGraph.dist_comm (u := a') (v := beta)] at hxd
    omega
  have hax : a ≠ x := by
    intro he
    have hcd : (graph Γ).dist a a' = b Γ := hc.1
    rw [←he,hcd] at hdx
    omega
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  have hres₀ := hres
  obtain ⟨hb2β,σ,Tβ,hσ,hfaithβ,hnatβ,Eβ,hEβ⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate hZ hSyl beta hb2β H
  have hcomp : σ.comp q = Representation.NormalElementaryQuotient.fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨⟨c⟩,_,_⟩ := neighborhood_residual_section ht hSyl beta hb2β H
    (core_le_graphLocalGroup ht beta) (sylowGenerated_le _)
  let : IsMulCommutative (V (family (fun i => (Reduction.P₀ L S₀ i).subgroupOf (Reduction.G₀ L S₀))) beta 1) := (helem beta).toIsMulCommutative
  obtain ⟨_,_,hcardpair⟩ := natural_residual_neighbor_pair_kernel ht hB hS hab.symm hx hax
    (core_escape_of_intersection_obstruction Γ (hob a beta hab))
    (core_escape_of_intersection_obstruction Γ (hob x beta hx.symm)) hω eβ σ
    (hcomp.symm ▸ c) hfaithβ Tβ hn hF hnatβ hca hcb
  have hwhole : V Γ beta 1 = Z Γ a ⊔ Z Γ x :=
    (eq_of_le_of_card_ge (sup_le (CommutingNontrivial.Z_neighbor_le_V Γ hab.symm)
      (CommutingNontrivial.Z_neighbor_le_V Γ hx)) (hcardpair.symm ▸ hupper)).symm
  have hcard : Nat.card (V Γ beta 1) = Nat.card F ^ 3 := hwhole ▸ hcardpair
  have hcard' : Nat.card (V Γ a' 1) = Nat.card F ^ 3 := (hVcard k a' hka').trans hcard
  have htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥ := by
    by_contra he
    exact Nat.ne_of_gt hb (h8 a beta a' hc hab hd hb1 hcomm he)
  have h8' (z : Vertex Γ) (hz : (graph Γ).Adj z a') (hzc : IsCriticalPair Γ z beta)
      (hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥)
      (he : ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥) : False :=
    Nat.ne_of_gt hb (h8 z a' beta hzc hz (by rwa [SimpleGraph.dist_comm]) hb1 hzcomm he)
  have hescape := linear_critical_reciprocal_escape ht hB hS hc hab hd hb2 hodd eα eβ
  obtain ⟨_,_,hC'⟩ := reduced_large_neighbor_linear_indices h hc hab hd hb1 hcomm htriv hescape
    (fun z hz hzc hzcomm he => (h8' z hz hzc hzcomm he).elim) hn hF eβ
  have hC : (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F := by
    have hh := congrArg (fun N : Subgroup (Reduction.G₀ L S₀) => N.relIndex (V Γ beta 1))
      (reduced_neighbor_centralizer_eq_core_inter h beta a' hb1 hd htriv)
    change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
      (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hh
    simp only [inf_relIndex_left] at hh
    exact hh.trans hi
  have hspanQ (y z : Vertex Γ) (hyz : (graph Γ).dist y z + 1 < b Γ) : V Γ y 1 ≤ Q Γ z := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht'
    apply Z_le_Q_of_dist_lt_b Γ hZ hSyl t z
    have ht'' := (mem_ball_iff Γ ht.generate y t 1).mp ht'
    have hh := (connected Γ ht.generate).dist_triangle (u := t) (v := y) (w := z)
    rw [SimpleGraph.dist_comm (u := t) (v := y)] at hh
    omega
  have hcx : Nat.card (Z Γ x) = Nat.card F ^ 2 := by
    obtain ⟨t,_,htx⟩ := graphLocalGroup_transitive ht hB hS beta ⟨a,hab.symm⟩ ⟨x,hx⟩
    exact (htranscard t a x htx).trans hca
  have hfixedx : Z Γ x ≤ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) :=
    (CommutingNontrivial.Z_centralizes_Q Γ x (hZ x)).trans
      (centralizer_le (hspanQ a' x (by rw [SimpleGraph.dist_comm]; omega)))
  have hfixedv : Z Γ v ≤ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) :=
    (CommutingNontrivial.Z_centralizes_Q Γ v (hZ v)).trans
      (centralizer_le (hspanQ beta v (by omega)))
  have hcent := centralizer_of_cube_card _ _ _ Nat.card_pos
    (CommutingNontrivial.Z_neighbor_le_V Γ hx) hfixedx hcard hcx hC
  have hcent' := centralizer_of_cube_card _ _ _ Nat.card_pos
    (CommutingNontrivial.Z_neighbor_le_V Γ hv) hfixedv hcard' hcv hC'
  have hRβ : ⁅V Γ beta 1,V Γ a' 1⁆ ≤ V Γ beta 1 := le_normalizer_iff_commutator_le_left.mp
    ((V_le_stabilizer Γ ht.generate a' beta (by rw [SimpleGraph.dist_comm]; exact hd.le)).trans
      (stabilizer_normalizes_V Γ beta 1))
  have hRa' : ⁅V Γ beta 1,V Γ a' 1⁆ ≤ V Γ a' 1 := le_normalizer_iff_commutator_le_right.mp
    ((V_le_stabilizer Γ ht.generate beta a' hd.le).trans (stabilizer_normalizes_V Γ a' 1))
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres₀,K,instK,finK,charK,m,hm,hK,eα,
    heq,hcQ,hcV,⟨ρ,T,hact,hfaith,hna,E,hE⟩,x,v,hx,hdx,hv,hdbv,hwhole,hcard,hcent,hcent',?_⟩
  exact le_inf (hcent' ▸ le_inf hRa' (hRβ.trans (le_centralizer _)))
    (hcent ▸ le_inf hRβ (hRa'.trans (le_centralizer _)))


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
