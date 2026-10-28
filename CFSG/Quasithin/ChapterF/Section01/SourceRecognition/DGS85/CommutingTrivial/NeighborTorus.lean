module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborFixedLine
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborCoreClosure
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The actual beta torus and its neighboring fixed subgroup

Every nonidentity odd beta actor has nontrivial image modulo the two-core.
Its natural action on the whole residual section is fixed-free. The exact
coordinate kernel therefore identifies its fixed subgroup on Z_alpha with
C_Z_alpha(O²(L_beta)), hence with Z_alpha intersect Z(W). Odd actors lie
in the two-residual, giving the reverse containment as well.

Schur--Zassenhaus in the original local Sylow normalizer constructs a beta
torus of order |F_beta|-1 inside the actual edge. Its elements lie in the
two-residual and in W. InitialAlphaBounds applies the fixed-subgroup result
to this constructed torus in both initial-recognition branches.
Source: DGS, Groups and Graphs (1985), 9.4(ii), printed p.143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

private theorem odd_quotient_ne_one {H : Type*} [Group H]
    {D : Type*} [Group D] (q : H →* D) (hk : q.ker = pCore 2 H)
    (k : H) (ho : Odd (orderOf k)) (hne : k ≠ 1) : q k ≠ 1 := by
  intro he
  have hm : k ∈ pCore 2 H := hk ▸ he
  have hc := pCore_isPGroup.orderOf_coprime ho.coprime_two_left (⟨k,hm⟩ : pCore 2 H)
  rw [Subgroup.orderOf_mk] at hc
  exact hne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc dvd_rfl dvd_rfl))

/-- Odd beta actors have the exact source fixed subgroup on the neighboring center. -/
private theorem residual_neighbor_odd_fixed
    (H A : Subgroup G) {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (q : H →* SL(2,F)) (hk : q.ker = pCore 2 H)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H A
      (A ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G)) (σ.comp q))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))
    (Z : Subgroup G) (hZA : Z ≤ A)
    (k : H) (ho : Odd (orderOf k)) (hne : k ≠ 1) :
    Z ⊓ centralizer ({(k : G)} : Set G) =
      Z ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) := by
  have hkn : q k ≠ 1 := odd_quotient_ne_one q hk k ho hne
  apply le_antisymm
  · rintro z ⟨hz,hfix⟩
    refine ⟨hz,?_⟩
    let zA : A := ⟨z,hZA hz⟩
    have hconj : (⟨(k : G)*z*(k : G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized k.property) z).mp zA.property⟩ : A) = zA := by
      apply Subtype.ext
      change (k : G)*z*(k : G)⁻¹=z
      rw [←mem_centralizer_singleton_iff.mp hfix,mul_inv_cancel_right]
    have heq : σ (q k) (c.coordinates zA).toAdd = (c.coordinates zA).toAdd := by
      exact (c.equivariant k zA).symm.trans (congrArg (fun x => (c.coordinates x).toAdd) hconj)
    have hz0 : E (c.coordinates zA).toAdd = 0 :=
      Matrix.SL2.odd_power_fixed_eq_zero (q k) (orderOf k) ho
        (by rw [←map_pow,pow_orderOf_eq_one,map_one]) hkn _ (by rw [←hE,heq])
    have hcoord : c.coordinates zA = 1 := E.injective (hz0.trans (map_zero E).symm)
    exact ((c.coordinates_eq_one_iff zA).mp hcoord).2
  · rintro z ⟨hz,hfix⟩
    refine ⟨hz,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (hfix k (mem_map_of_mem H.subtype
      (mem_pResidual_of_orderOf_coprime ho.coprime_two_left))).symm


open Representation.NormalElementaryQuotient
variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Source 9.4(ii) holds for every nonidentity odd beta actor, hence for every
nonidentity element of the actual beta torus. -/
theorem reduced_natural_residual_neighbor_odd_fixed (h : HypothesisF11 L S₀)
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
    {n : ℕ}
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
    ∀ k : H, Odd (orderOf k) → k ≠ 1 →
      Z Γ a ⊓ centralizer ({(k : Reduction.G₀ L S₀)} : Set (Reduction.G₀ L S₀)) =
        Z Γ a ⊓ (Subgroup.center W).map W.subtype := by
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
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcomp : σ.comp q = fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨_,_,⟨c⟩,_⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  dsimp only
  intro k ho hne
  exact (residual_neighbor_odd_fixed H (V Γ beta 1) q hk σ (hcomp.symm ▸ c) E hE
    (Z Γ a) (CommutingNontrivial.Z_neighbor_le_V Γ hab.symm) k ho hne).trans
      (neighbor_core_closure_center_intersection ht (Reduction.reduced_borel_core_sylow h)
        (Reduction.reduced_vertex_sylow h) hab.symm
        (core_escape_of_intersection_obstruction Γ hob) e).symm

private theorem exists_linear_sylow_torus
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
    (q : H →* SL(2,F)) (hq : Function.Surjective q) (R : Sylow 2 H)
    (hk : q.ker ≤ (R : Subgroup H)) :
    ∃ K : Subgroup H, K ≤ normalizer (R : Set H) ∧
      Nat.card K = Nat.card F - 1 := by
  let N := normalizer (R : Set H)
  obtain ⟨f,hf,hfk⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal q hq R hk
  have hker : f.ker = (R : Subgroup H).subgroupOf N := by
    ext x
    exact hfk x
  let RN : Sylow 2 N := R.subtype (R : Subgroup H).le_normalizer
  have hcop : Nat.Coprime (Nat.card f.ker) f.ker.index := by
    rw [hker]
    exact RN.card_coprime_index
  obtain ⟨D,hD⟩ := exists_right_complement'_of_coprime hcop
  refine ⟨D.map N.subtype,map_subtype_le _,?_⟩
  rw [card_map_of_injective N.subtype_injective,←hD.symm.index_eq_card]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).trans
    (Nat.card_units (α := F))

/-- The beta linear marking constructs an actual odd torus in the original
edge, of the full field-minus-one order, inside the residual and W. -/
theorem reduced_linear_neighbor_torus (h : HypothesisF11 L S₀)
    {a beta : Vertex (Reduction.reducedFamily L S₀)}
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    ∃ K : Subgroup (Reduction.G₀ L S₀),
      K ≤ H ⊓ stabilizer Γ a ∧ Odd (Nat.card K) ∧ Nat.card K = Nat.card F - 1 ∧
      K ≤ (pResidual 2 H).map H.subtype ∧ K ≤ conjugateSpanBy (Q Γ a) (stabilizer Γ beta) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := hk.symm ▸ pCore_isPGroup
  obtain ⟨T,hTf⟩ := local_quotient_neighbor_stabilizer ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab.symm e
  let R : Sylow 2 H := T.comapOfKerIsPGroup q hp
    (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  have hR : (R : Subgroup H).map q = T := map_comap_eq_self_of_surjective hq _
  have hkR : q.ker ≤ (R : Subgroup H) := by
    intro x hx
    change q x ∈ (T : Subgroup SL(2,F))
    rw [show q x = 1 from hx]
    exact one_mem _
  obtain ⟨D,hDN,hDcard⟩ := exists_linear_sylow_torus q hq R hkR
  let K := D.map H.subtype
  have hKcard : Nat.card K = Nat.card F - 1 :=
    (card_map_of_injective H.subtype_injective).trans hDcard
  have hodd : Odd (Nat.card K) := by
    rw [hKcard,hF]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by omega : n ≠ 0)) odd_one
  have hKa : K ≤ stabilizer Γ a := by
    rintro x ⟨y,hy,rfl⟩
    apply (hTf y).mp
    have hh := le_normalizer_map q (mem_map_of_mem q (hDN hy))
    rwa [hR] at hh
  have hDodd : Odd (Nat.card D) := by
    change Odd (Nat.card (D.map H.subtype)) at hodd
    rwa [card_map_of_injective H.subtype_injective] at hodd
  have hKR : K ≤ (pResidual 2 H).map H.subtype := by
    rintro x ⟨y,hy,rfl⟩
    refine mem_map_of_mem H.subtype (mem_pResidual_of_orderOf_coprime ?_)
    have hyodd : Odd (orderOf y) := by
      simpa only [Subgroup.orderOf_mk] using hDodd.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨y,hy⟩ : D))
    exact hyodd.coprime_two_left
  refine ⟨K,le_inf (map_subtype_le _) hKa,hodd,hKcard,hKR,?_⟩
  have he := neighbor_core_closure_eq_residual_sup ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab.symm
    (core_escape_of_intersection_obstruction Γ hob) e
  exact hKR.trans (le_sup_left.trans he.ge)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
