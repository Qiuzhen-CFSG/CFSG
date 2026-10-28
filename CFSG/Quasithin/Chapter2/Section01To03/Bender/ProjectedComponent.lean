module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ThreeComponentRank
public import Theory.GroupTheory.CentralFactorProjection
public import Theory.GroupTheory.SylowNormalizerOuterAction

/-!
# The projected component factors in the Bender reduction

Start with the actual inner-action equality Aut_U(L) = Q, expressed using
ambient implementers, and the normalizer action on Q supplied by the Bender
models. The centerless component gives a homomorphic projection onto Q.
Source (*) puts N_L(Q) in M before any split of U is available. Its transitive
action forces Q into U, yielding Q = U intersect L and U = C_U(L) times Q.

The normalizer is then exactly L intersect M. Its action on Q and its
actual action on U have identical full centralizer kernels, so their images
are isomorphic. This transports cyclicity and oddness without discarding
the norm-one torus kernel in the unitary case. The final theorem applies the
existing component geometry, three-component rank and GO obstruction.

This is a conditional source reduction, not Bender recognition. The earlier
1.1.5 component alternatives and the strongly closed action still must select
the Bender row and its Q; the concrete model normalizer facts and I.3.2 balance
must be supplied. The good-centralizer branch still needs Shult I.8.3.

Source: Aschbacher--Smith, Proposition 2.2.2, printed p.520 (PDF p.537),
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Subgroup.CentralFactor
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

omit [Finite G] in
/-- Source (*) puts the relative normalizer of the projected subgroup
in M by applying it to the actual two-group U joined with that image. -/
theorem LocalControlWitness.projected_normalizer_le
    (w : LocalControlWitness T M) (L : Subgroup G) (f : w.U →* G)
    (hf : f.range ≤ L)
    (hc : ∀ u : w.U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G)) :
    L ⊓ normalizer (f.range : Set G) ≤ M := by
  let _ : IsElementaryAbelian 2 w.U := w.elementary
  have hUp := IsElementaryAbelian.isPGroup 2 w.U
  have hQp := hUp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hp : IsPGroup 2 (w.U ⊔ f.range : Subgroup G) :=
    hUp.to_sup_of_normal_right' hQp
      ((le_centralizer_iff.mp (projection_range_centralizes f hf hc)).trans
        (Subgroup.centralizer_le_normalizer _))
  exact (projection_normalizer_le_join_normalizer f hc).trans
    (w.source_star _ hp ((le_sup_left : w.U ≤ w.U ⊔ f.range) w.z_mem)).2

/-- The nontrivial projection of the distinguished z, and the model
normalizer transitivity, give the source split and its size bound. -/
theorem LocalControlWitness.projected_split
    (w : LocalControlWitness T M) (L : Subgroup G) (hLM : ¬ L ≤ M)
    (f : w.U →* G) (hf : f.range ≤ L)
    (hc : ∀ u : w.U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (hsize : 2 < Nat.card f.range)
    (htrans : ∀ a ∈ f.range, a ≠ 1 → ∀ b ∈ f.range, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (f.range : Set G), n * a * n⁻¹ = b) :
    f.range ≤ w.U ∧
    w.U = componentFixedSubgroup w L ⊔ (w.U ⊓ L) ∧
    w.U ≤ normalizer (L : Set G) ∧ 2 < Nat.card (w.U ⊓ L : Subgroup G) := by
  have hz : f ⟨w.z, w.z_mem⟩ ≠ 1 := by
    intro he
    have hzc := hc ⟨w.z, w.z_mem⟩
    simp only [he, inv_one, mul_one] at hzc
    apply hLM
    intro l hl
    apply w.centralizer_le
    exact mem_centralizer_singleton_iff.mpr (hzc l hl)
  have hQU := projection_range_le_of_transitive f hc
    ((w.projected_normalizer_le L f hf hc).trans w.normalizes) hsize htrans
    ⟨w.z, w.z_mem⟩ hz
  exact ⟨hQU, projection_split_of_range_le f hf hc hQU,
    projection_le_normalizer f hf hc, hsize.trans_le (card_le_of_le (le_inf hQU hf))⟩

omit [Finite G] in
/-- After identifying the projected image with U∩L, its relative
normalizer is exactly N_L(U) = L∩M. -/
theorem LocalControlWitness.projected_normalizer_eq
    (w : LocalControlWitness T M) (L : Subgroup G) (f : w.U →* G)
    (hf : f.range ≤ L)
    (hc : ∀ u : w.U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (hQ : f.range = w.U ⊓ L) :
    L ⊓ normalizer (f.range : Set G) = L ⊓ M := by
  apply le_antisymm (le_inf inf_le_left (w.projected_normalizer_le L f hf hc))
  rw [hQ]
  exact le_inf inf_le_left
    ((le_inf (inf_le_right.trans w.normalizes) (inf_le_left.trans L.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf)

omit [Finite G] in
/-- The two literal action images are isomorphic by equality of their
full centralizer kernels. Odd torus elements in those kernels are retained. -/
theorem LocalControlWitness.projected_actor_equiv
    (w : LocalControlWitness T M) (L : Subgroup G) (f : w.U →* G)
    (hf : f.range ≤ L)
    (hc : ∀ u : w.U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (hQ : f.range = w.U ⊓ L) :
    Nonempty (componentActor w L ≃*
      (Theory.GroupTheory.normalizerAction L f.range).range) := by
  let N := L ⊓ normalizer (f.range : Set G)
  have hNM : N ≤ M := w.projected_normalizer_le L f hf hc
  let a := Theory.GroupTheory.normalizerAction L f.range
  let b : N →* sourceActionImage w :=
    (conjugationAction M w.U w.normalizes).rangeRestrict.comp (inclusion hNM)
  have hr : b.range = componentActor w L := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨⟨n, n.property.1, hNM n.property⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      have hn : (n : G) ∈ N := by
        change (n : G) ∈ L ⊓ normalizer (f.range : Set G)
        rw [w.projected_normalizer_eq L f hf hc hQ]
        exact n.property
      exact ⟨⟨n, hn⟩, rfl⟩
  have hk : a.ker = b.ker := by
    ext n
    have ha : n ∈ a.ker ↔ (n : G) ∈ centralizer (f.range : Set G) := by
      change inclusion inf_le_right n ∈ f.range.normalizerMonoidHom.ker ↔ _
      rw [normalizerMonoidHom_ker]
      rfl
    have hb : n ∈ b.ker ↔ (n : G) ∈ centralizer (w.U : Set G) := by
      change b n = 1 ↔ _
      rw [Subtype.ext_iff]
      change w.U.normalizerMonoidHom ⟨n, w.normalizes (hNM n.property)⟩ = 1 ↔ _
      rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
      rfl
    rw [ha, hb]
    constructor
    · intro hn u hu
      have he := projection_conjugate f hc (⟨u, hu⟩ : w.U) n.property.1
      rw [← hn (f ⟨u, hu⟩) ⟨⟨u, hu⟩, rfl⟩, mul_inv_cancel_right] at he
      have he' : (n : G) * u * (n : G)⁻¹ = u := by
        simpa only [inv_mul_cancel_right] using he
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    · intro hn
      exact Subgroup.centralizer_le (hQ ▸ inf_le_left) hn
  exact ⟨(MulEquiv.subgroupCongr hr).symm.trans
    ((QuotientGroup.quotientKerEquivRange b).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivRange a)))⟩

/-- The projected-factor construction supplies the split, size,
U-normalization and actual L∩M action to the proved three-component/GO
argument. The earlier model and balance inputs remain explicit. -/
theorem LocalControlWitness.false_of_projected_component
    (w : LocalControlWitness T M) {C : GroupClass} (hG : IsSimpleQTKE C G)
    (hTM : (T : Subgroup G) ≤ M) (L : Subgroup G)
    (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    (hbalance : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      ∃ K : Subgroup G, Theory.GroupTheory.IsComponentIn K (centralizer ({v} : Set G)) ∧ L ≤ K)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (f : w.U →* G) (hf : f.range ≤ L)
    (hc : ∀ u : w.U, (u : G) * (f u)⁻¹ ∈ centralizer (L : Set G))
    (hsize : 2 < Nat.card f.range)
    (hcyclic : IsCyclic (Theory.GroupTheory.normalizerAction L f.range).range)
    (hodd : Odd (Nat.card (Theory.GroupTheory.normalizerAction L f.range).range))
    (htrans : ∀ a ∈ f.range, a ≠ 1 → ∀ b ∈ f.range, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (f.range : Set G), n * a * n⁻¹ = b) : False := by
  obtain ⟨hQU, hsplit, hUL, hsize'⟩ := w.projected_split L hmax.1.1 f hf hc hsize htrans
  have hQ := projection_range_eq_inf_of_disjoint f hf hc hQU hdis
  obtain ⟨e⟩ := w.projected_actor_equiv L f hf hc hQ
  have hlocal : ∀ a ∈ w.U ⊓ L, a ≠ 1 → ∀ b ∈ w.U ⊓ L, b ≠ 1 →
      ∃ n ∈ L ⊓ M, n * a * n⁻¹ = b := by
    intro a ha ha1 b hb hb1
    obtain ⟨n, hn, he⟩ := htrans a (hQ.symm ▸ ha) ha1 b (hQ.symm ▸ hb) hb1
    exact ⟨n, w.projected_normalizer_eq L f hf hc hQ ▸ hn, he⟩
  apply false_of_maximal_component_geometry_of_local_transitivity w hG hTM L hmax
    hsplit hbalance hsize' (e.isCyclic.mpr hcyclic) _ hUL hlocal
  rwa [Nat.card_congr e.toEquiv]

/-- The source inner-action equality, written with actual implementers
in Q, constructs the projection and proves the full internal-product split.
In the Bender rows Q is the actual omega-one subgroup of the component Sylow. -/
theorem LocalControlWitness.inner_component_split
    (w : LocalControlWitness T M) (L Q : Subgroup G) (hLM : ¬ L ≤ M)
    (hQL : Q ≤ L) (hdis : Disjoint L (centralizer (L : Set G)))
    (hinner : ∀ u : w.U, ∃ q : Q, (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G))
    (honto : ∀ q : Q, ∃ u : w.U, (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G))
    (hsize : 2 < Nat.card Q)
    (htrans : ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (Q : Set G), n * a * n⁻¹ = b) :
    Q = w.U ⊓ L ∧ w.U = componentFixedSubgroup w L ⊔ Q ∧
    Disjoint (componentFixedSubgroup w L) Q ∧
    w.U ≤ normalizer (L : Set G) ∧
    L ⊓ normalizer (Q : Set G) = L ⊓ M := by
  obtain ⟨f, hf, hc⟩ := exists_projection_of_inner_implementers Q hQL hdis hinner honto
  have hfL : f.range ≤ L := hf ▸ hQL
  obtain ⟨hQU, hsplit, hUL, _⟩ := w.projected_split L hLM f hfL hc
    (hf ▸ hsize) (hf ▸ htrans)
  have hQ := projection_range_eq_inf_of_disjoint f hfL hc hQU hdis
  have hQU' : Q = w.U ⊓ L := hf.symm.trans hQ
  refine ⟨hQU', hQU' ▸ hsplit, hdis.symm.mono inf_le_right hQL, hUL, ?_⟩
  rw [← hf]
  exact w.projected_normalizer_eq L f hfL hc hQ

/-- Bad-centralizer reduction from actual inner-action witnesses and
the concrete normalizer action on Q. No projection, splitting, TI,
stabilizer-normality, three-component rank or GO conclusion is assumed.
The source selection, model-local facts and I.3.2 balance must still be
constructed before this proves the bad-centralizer branch of 2.2.2. -/
theorem LocalControlWitness.false_of_inner_component
    (w : LocalControlWitness T M) {C : GroupClass} (hG : IsSimpleQTKE C G)
    (hTM : (T : Subgroup G) ≤ M) (L Q : Subgroup G)
    (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    (hbalance : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      ∃ K : Subgroup G, Theory.GroupTheory.IsComponentIn K (centralizer ({v} : Set G)) ∧ L ≤ K)
    (hQL : Q ≤ L) (hdis : Disjoint L (centralizer (L : Set G)))
    (hinner : ∀ u : w.U, ∃ q : Q, (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G))
    (honto : ∀ q : Q, ∃ u : w.U, (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G))
    (hsize : 2 < Nat.card Q)
    (hcyclic : IsCyclic (Theory.GroupTheory.normalizerAction L Q).range)
    (hodd : Odd (Nat.card (Theory.GroupTheory.normalizerAction L Q).range))
    (htrans : ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (Q : Set G), n * a * n⁻¹ = b) : False := by
  obtain ⟨f, hf, hc⟩ := exists_projection_of_inner_implementers Q hQL hdis hinner honto
  exact w.false_of_projected_component hG hTM L hmax hbalance hdis f (hf ▸ hQL) hc
    (hf ▸ hsize) (hf ▸ hcyclic) (hf ▸ hodd) (hf ▸ htrans)

end CFSG.Quasithin.Chapter2.BenderFusion
