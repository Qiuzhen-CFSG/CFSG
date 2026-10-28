module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Basic
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Theory.GroupTheory.CentralCommutatorQuotient


/-!
# From the opposite displacement plane to the two edge identities

Let x be the selected moving element, and put K = [<x>, Q_c]. If K lies
in the actual natural subgroup U_c and has order four, its containment in
the initial edge displacement makes that containment an equality. Edge
transitivity and nilpotent saturation then identify K with the other edge
displacement.

For the kernel product, the natural layer U_a has order eight, and x
supplies its missing generator modulo K and the central summand of Z_a.
Evaluation y ↦ [x,y] on C_(Q_t)(K) is a homomorphism. Its restriction to
Q_c covers K, while its kernel is Q_a. This gives the literal relative
centralizer identity, with both endpoint kernels inside Q_t.

The opposite-action construction of the order-four subgroup in U_c is
still required. The exported theorem is the conditional algebraic assembly
into EdgeData, not an unconditional proof of the source selection. In
particular, no favorable pairing or escape counterexample is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), the first
three sentences on printed p.891; the moving choice starts on pp.890–891.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection

private theorem invariant_plane_eq {G : Type*} [Group G]
    (T U K : Subgroup G) [Finite U] (hT : Group.IsNilpotent T)
    (hUT : U ≤ T) (hKU : K ≤ U) (hKN : T ≤ normalizer (K : Set G))
    (hU : Nat.card U = 8) (hK : Nat.card K = 4)
    (hD : Nat.card (⁅U,T⁆ : Subgroup G) = 4) (hDU : ⁅U,T⁆ ≤ U) :
    K = ⁅U,T⁆ := by
  let J := K ⊔ ⁅U,T⁆
  have hJU : J ≤ U := sup_le hKU hDU
  let : Finite J := Finite.of_injective (inclusion hJU) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKU) (inclusion_injective _)
  have hDK : ⁅U,T⁆ ≤ K := by
    by_contra hn
    have hne : K ≠ J := fun he => hn (he ▸ (show ⁅U,T⁆ ≤ J from le_sup_right))
    have hlt : 4 < Nat.card J := by
      by_contra! hh
      exact hne (eq_of_le_of_card_ge le_sup_left (by omega))
    have hdvd : Nat.card J ∣ 8 := hU ▸ card_dvd_of_le hJU
    have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    have hfull : J = U := eq_of_le_of_card_ge hJU (by omega)
    have hUK := le_of_le_sup_commutator_of_isNilpotent T U K T hT
      hUT (hKU.trans hUT) le_rfl hKN hfull.ge
    have hh := congrArg (fun H : Subgroup G => Nat.card H) (le_antisymm hKU hUK)
    omega
  exact (eq_of_le_of_card_ge hDK (by omega)).symm

private theorem cyclic_row_surjective {G : Type*} [Group G]
    (Q K : Subgroup G) (x : G)
    (hKQ : K ≤ centralizer (Q : Set G))
    (hKx : K ≤ centralizer (zpowers x : Set G))
    (hK : ⁅zpowers x,Q⁆ = K) :
    ∀ k ∈ K, ∃ q ∈ Q, ⁅x,q⁆ = k := by
  have hr (q : G) (hq : q ∈ Q) : ⁅x,q⁆ ∈ K :=
    hK ▸ commutator_mem_commutator (mem_zpowers x) hq
  let row := centralCommutatorHom Q K hKQ x hr
  let f := K.subtype.comp row
  have hKr : K ≤ f.range := by
    rw [← hK, commutator_comm]
    apply commutator_le.mpr
    intro q hq z hz
    have hv (v : G) (hv : v ∈ zpowers x) : ⁅q,v⁆ ∈ K := by
      rw [← hK, commutator_comm]
      exact commutator_mem_commutator hq hv
    let col := centralCommutatorHom (zpowers x) K hKx q hv
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    have he := congrArg Subtype.val (map_zpow col (⟨x, mem_zpowers x⟩ : zpowers x) n)
    change ⁅q,x ^ n⁆ = ⁅q,x⁆ ^ n at he
    rw [he]
    apply f.range.zpow_mem
    rw [← commutatorElement_inv]
    exact f.range.inv_mem ⟨⟨q,hq⟩, rfl⟩
  intro k hk
  obtain ⟨q, hq⟩ := hKr hk
  exact ⟨q, q.property, hq⟩

private theorem kernel_product_of_generation {G : Type*} [Group G]
    (X T Q N E : Subgroup G) (x : G)
    (hQT : Q ≤ T) (hEX : E ≤ X) (hx : x ∈ X)
    (hN : N = T ⊓ centralizer (X : Set G))
    (hQE : Q ≤ centralizer (E : Set G))
    (hXE : E ≤ centralizer (zpowers x : Set G))
    (hcomm : ⁅X,T⁆ ≤ E) (hrow : ⁅zpowers x,Q⁆ = E)
    (hgen : X ≤ (zpowers x ⊔ E) ⊔ centralizer (T : Set G)) :
    N ⊔ Q = T ⊓ centralizer (E : Set G) := by
  let C := T ⊓ centralizer (E : Set G)
  have hNC : N ≤ C := by
    rw [hN]
    exact inf_le_inf_left _ (centralizer_le hEX)
  have hQC : Q ≤ C := le_inf hQT hQE
  have hr (q : G) (hq : q ∈ C) : ⁅x,q⁆ ∈ E :=
    hcomm (commutator_mem_commutator hx hq.1)
  let row := centralCommutatorHom C E (le_centralizer_iff.mp inf_le_right) x hr
  apply le_antisymm (sup_le hNC hQC)
  intro y hy
  obtain ⟨q, hq, he⟩ := cyclic_row_surjective Q E x
    (le_centralizer_iff.mp hQE) hXE hrow _ (hr y hy)
  let y' : C := ⟨y,hy⟩
  let q' : C := ⟨q,hQC hq⟩
  have hroweq : row y' = row q' := Subtype.ext he.symm
  have hzero : ⁅x,y*q⁻¹⁆ = 1 := by
    have hh : row (y' * q'⁻¹) = 1 := by rw [map_mul, map_inv, hroweq, mul_inv_cancel]
    exact congrArg Subtype.val hh
  have hzC : y*q⁻¹ ∈ C := C.mul_mem hy (C.inv_mem (hQC hq))
  have hzN : y*q⁻¹ ∈ N := by
    rw [hN]
    refine ⟨hzC.1, ?_⟩
    have hfix : X ≤ centralizer ({y*q⁻¹} : Set G) := by
      apply hgen.trans
      refine sup_le (sup_le ?_ ?_) ?_
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp hzero))
      · intro e he
        exact mem_centralizer_singleton_iff.mpr (hzC.2 e he)
      · intro z hz
        exact mem_centralizer_singleton_iff.mpr (hz _ hzC.1).symm
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hfix hz)
  have hh := (N ⊔ Q).mul_mem (mem_sup_left hzN) (mem_sup_right hq)
  simpa only [inv_mul_cancel_right] using hh

private theorem moving_generator_cover {G : Type*} [Group G]
    (X U F E T Q : Subgroup G) [IsMulCommutative X] [Finite U]
    (hU : U ≤ X) (hF : F ≤ X) (hE : E ≤ U)
    (hX : X = U ⊔ F) (hFT : F ≤ centralizer (T : Set G))
    (hQT : Q ≤ T) (hEQ : E ≤ centralizer (Q : Set G))
    (hUc : Nat.card U = 8) (hEc : Nat.card E = 4)
    (x : G) (hx : x ∈ X) (hm : ⁅zpowers x,Q⁆ ≠ ⊥) :
    X ≤ (zpowers x ⊔ E) ⊔ centralizer (T : Set G) := by
  have hUF : U ≤ normalizer (F : Set G) := by
    apply le_normalizer_iff.mpr
    intro u hu v hv
    rw [show u*v = v*u from congrArg Subtype.val
      (mul_comm (⟨u,hU hu⟩ : X) ⟨v,hF hv⟩), mul_inv_cancel_right]
    exact hv
  have hxprod : x ∈ (U : Set G) * (F : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right U F hUF, ← hX]
    exact hx
  obtain ⟨u,hu,v,hv,rfl⟩ := hxprod
  have huE : u ∉ E := by
    intro he
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact zpowers_le.mpr ((centralizer (Q : Set G)).mul_mem
      (hEQ he) (centralizer_le hQT (hFT hv)))
  let J := zpowers u ⊔ E
  have hJU : J ≤ U := sup_le (zpowers_le.mpr hu) hE
  let : Finite J := Finite.of_injective (inclusion hJU) (inclusion_injective _)
  have hne : E ≠ J := fun he => huE (he ▸ (show u ∈ J from mem_sup_left (mem_zpowers u)))
  have hlt : 4 < Nat.card J := by
    by_contra! hh
    exact hne (eq_of_le_of_card_ge le_sup_right (by omega))
  have hdvd : Nat.card J ∣ 8 := hUc ▸ card_dvd_of_le hJU
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hfull : J = U := eq_of_le_of_card_ge hJU (by omega)
  rw [hX]
  refine sup_le ?_ (hFT.trans le_sup_right)
  rw [← hfull]
  refine sup_le (zpowers_le.mpr ?_) (le_sup_right.trans le_sup_left)
  have hh := ((zpowers (u*v) ⊔ E) ⊔ centralizer (T : Set G)).mul_mem
    (mem_sup_left (mem_sup_left (mem_zpowers (u*v))))
    (mem_sup_right ((centralizer (T : Set G)).inv_mem (hFT hv)))
  simpa only [mul_inv_cancel_right] using hh

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- A moving cyclic displacement that is a plane in the actual U_c supplies
all three edge identities. Its opposite-action producer remains separate. -/
theorem MovingSeed.edgeData_of_natural_plane (common : CommonFacts R source geometry)
    {a c : Vertex R} (s : MovingSeed a c) (ha : color R a = false)
    (hc : color R c = false)
    (hnatural : ⁅zpowers s.element,Q R c⁆ ≤ U R c)
    (hfour : Nat.card (⁅zpowers s.element,Q R c⁆ : Subgroup (FreeAmalgam R)) = 4) :
    Nonempty (EdgeData a c) := by
  let K := ⁅zpowers s.element,Q R c⁆
  have hKa : K ≤ U R a := (s.displacement_le_edge ha).trans
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) a s.neighbor ha s.adjacent_start)
  let : Finite (U R a) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at a ha]; decide)
  let : Finite (U R c) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at c hc]; decide)
  let : Finite (edgeCommutator R a s.neighbor) := Finite.of_injective
    (inclusion (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) a s.neighbor ha s.adjacent_start)) (inclusion_injective _)
  have hdis : K = edgeCommutator R a s.neighbor :=
    eq_of_le_of_card_ge (s.displacement_le_edge ha)
      ((Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
        (moduleFacts common) a s.neighbor ha s.adjacent_start).trans_eq hfour.symm)
  have hEc : Nat.card (⁅U R c,Q R s.neighbor⁆ : Subgroup (FreeAmalgam R)) = 4 := by
    rw [← Escape.EdgeTransfer.edge_commutator_eq_natural common.large_distance
      (moduleFacts common) c s.neighbor hc s.adjacent_center]
    rw [← DistanceFour.Early.OrderTwo.edge_card_eq a s.neighbor c s.neighbor
      ha hc s.adjacent_start s.adjacent_center]
    change Nat.card (edgeCommutator R a s.neighbor) = 4
    rw [← hdis]
    exact hfour
  have hnorm : Q R s.neighbor ≤ normalizer (K : Set (FreeAmalgam R)) := by
    rw [hdis]
    exact normalizer_commutator_ge_right _ _
  let := finite_stabilizer R s.neighbor
  let : Finite (Q R s.neighbor) := Finite.of_injective
    (inclusion (show Q R s.neighbor ≤ stabilizer R s.neighbor from fun _ hx => hx.1))
    (inclusion_injective _)
  have heq : K = edgeCommutator R c s.neighbor := by
    change K = ⁅Z R c,Q R s.neighbor⁆
    rw [Escape.EdgeTransfer.edge_commutator_eq_natural common.large_distance
      (moduleFacts common) c s.neighbor hc s.adjacent_center]
    exact invariant_plane_eq (Q R s.neighbor) (U R c) K
      (Escape.EdgeTransfer.edge_kernel_two source c s.neighbor hc s.adjacent_center).isNilpotent
      ((U_le_Z R c).trans (Escape.EdgeTransfer.edge_Z_le_Q common.large_distance
        c s.neighbor hc s.adjacent_center)) hnatural hnorm
      (common.natural.card_at c hc) hfour hEc
      (le_normalizer_iff_commutator_le_left.mp
        ((show Q R s.neighbor ≤ stabilizer R c from fun _ hx =>
          hx.2 c (adjacent_symm R s.adjacent_center)).trans (U_normalized c)))
  have hQT : Q R c ≤ Q R s.neighbor :=
    (endpoint_kernels_normal ha s.adjacent_start s.adjacent_center).2.1
  have hKQ : K ≤ centralizer (Q R c : Set (FreeAmalgam R)) :=
    (hnatural.trans (U_le_Z R c)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc))
  have hTX : Q R s.neighbor ≤ stabilizer R a := fun _ hx =>
    hx.2 a (adjacent_symm R s.adjacent_start)
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) a ha
  have hKx : K ≤ centralizer (zpowers s.element : Set (FreeAmalgam R)) := by
    intro k hk z hz
    exact congrArg Subtype.val (mul_comm
      (⟨z,zpowers_le.mpr s.element_mem hz⟩ : Z R a) ⟨k,U_le_Z R a (hKa hk)⟩)
  have hgen : Z R a ≤ (zpowers s.element ⊔ K) ⊔
      centralizer (Q R s.neighbor : Set (FreeAmalgam R)) := by
    apply moving_generator_cover (Z R a) (U R a)
      (Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R))) K
      (Q R s.neighbor) (Q R c) (U_le_Z R a) inf_le_left hKa
      ((naturalStructure common).decomposition_at a ha)
      (inf_le_right.trans (centralizer_le hTX)) hQT hKQ
      (common.natural.card_at a ha) hfour s.element s.element_mem
    intro hz
    exact s.moving (hz ▸ bot_le)
  have hprod : Q R a ⊔ Q R c = Q R s.neighbor ⊓ centralizer (K : Set (FreeAmalgam R)) :=
    kernel_product_of_generation (Z R a) (Q R s.neighbor) (Q R c) (Q R a) K
      s.element hQT (hKa.trans (U_le_Z R a)) s.element_mem
      (common.centralizer a s.neighbor ha s.adjacent_start).symm
      (le_centralizer_iff.mp hKQ) hKx hdis.ge rfl hgen
  exact ⟨{ toMovingSeed := s
           displacement := hdis
           edge_eq := hdis.symm.trans heq
           kernel_product := hdis ▸ hprod }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
