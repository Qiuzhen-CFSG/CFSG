module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelsSourceProduct
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalBranchAction
public import Theory.GroupTheory.NormalTripleInvolutions
public import Theory.GroupTheory.CentralTwoQuotientOddCore
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# Excluding radius one in the original large source action

The three branch labels become a normal triple of involutions modulo the
central label. Their literal action on the three neighbors makes them
pairwise noncommuting. They generate a normal symmetric-three subgroup,
whose odd core contradicts the characteristic-two source stabilizer.
The final theorem applies this obstruction to every centered source interval.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.8),
printed pp.399--400.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

private theorem normal_triple_oddCore_nontrivial
    {Q : Type*} [Group Q] [Finite Q] (x : Fin 3 → Q)
    (hpow : ∀ i, x i ^ 2 = 1)
    (hnormal : ∀ (g : Q) (i : Fin 3), ∃ j : Fin 3, g * x i * g⁻¹ = x j)
    (hnc : ∀ i j : Fin 3, i ≠ j → ¬Commute (x i) (x j)) :
    pPrimeCore 2 Q ≠ ⊥ := by
  let K : Subgroup Q := closure (Set.range x)
  have hx (i : Fin 3) : x i ∈ K := subset_closure ⟨i,rfl⟩
  let y : Fin 3 → K := fun i => ⟨x i,hx i⟩
  have hgen : closure (Set.range y) = ⊤ := by
    apply top_unique
    intro k _
    have hle : K ≤ (closure (Set.range y)).map K.subtype := by
      apply (closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      exact ⟨y i,subset_closure ⟨i,rfl⟩,rfl⟩
    obtain ⟨l,hl,he⟩ := hle k.property
    exact (Subtype.ext he : l=k) ▸ hl
  have hKcard : Nat.card K = 6 := card_eq_six_of_normal_triple_involutions y
    (fun i => Subtype.ext (hpow i)) hgen
    (fun g i => by obtain ⟨j,hj⟩ := hnormal g i; exact ⟨j,Subtype.ext hj⟩)
    (fun i j hij hc => hnc i j hij (congrArg Subtype.val hc.eq))
  let : K.Normal := ⟨by
    intro k hk g
    have hN : K.map (MulAut.conj g).toMonoidHom ≤ K := by
      rw [MonoidHom.map_closure]
      apply (closure_le _).mpr
      rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
      obtain ⟨j,hj⟩ := hnormal g i
      change g*x i*g⁻¹ ∈ K
      rw [hj]
      exact hx j
    exact hN (mem_map_of_mem (MulAut.conj g).toMonoidHom hk)⟩
  let P : Sylow 3 K := Classical.choice inferInstance
  have hPcard : Nat.card P=3 := by
    rw [P.card_eq_multiplicity,hKcard]
    have hf : (Nat.factorization 6) 3=1 := by
      change (Nat.factorization (2*3)) 3=1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
    rw [hf,pow_one]
  have hPnormal : (P : Subgroup K).Normal := by
    have hidx : (P : Subgroup K).index=2 := by
      have hh := (P : Subgroup K).card_mul_index
      rw [hPcard,hKcard] at hh
      omega
    exact normal_of_index_eq_two hidx
  let : (P : Subgroup K).Characteristic := P.characteristic_of_normal hPnormal
  let T := (P : Subgroup K).map K.subtype
  have hTcard : Nat.card T = 3 := by
    rw [card_map_of_injective K.subtype_injective]
    exact hPcard
  intro hcore
  have hTbot : T = ⊥ := pPrimeCore_eq_bot_iff.mp hcore T inferInstance
    (by rw [hTcard]; decide)
  have hh : Nat.card T = 1 := by simp [hTbot]
  omega

open SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private structure RadiusOneData (F : Bool → Subgroup G) where
  side : Bool
  label : RankTwo.Vertex F → G
  order_two : ∀ a, a.type=side → orderOf (label a)=2
  central : ∀ a, a.type=side → label a ∈ RankTwo.stabilizer F a ∧
    ∀ g ∈ RankTwo.stabilizer F a, Commute (label a) g
  conjugate : ∀ (g : G) a, a.type=side → label (g • a)=g*label a*g⁻¹
  fixes : ∀ a, a.type=side → ∀ b, (RankTwo.graph F).dist a b≤2 → label a • b=b
  moves : ∀ a, a.type=side → ∀ b, (RankTwo.graph F).dist a b=3 → label a • b≠b
  product : ∀ v a b c, (RankTwo.graph F).Adj v a → (RankTwo.graph F).Adj v b →
    (RankTwo.graph F).Adj v c → a≠b → a≠c → b≠c → a.type=side →
    label a * label b * label c=1

private theorem RadiusOneData.same_type_dist_two (d : RadiusOneData F)
    (h : CubicTreeAction F) {a b : RankTwo.Vertex F} (ha : a.type=d.side)
    (hd : (RankTwo.graph F).dist a b=2) : b.type=d.side := by
  have he := (RankTwo.even_dist_iff F h.generated a b).mp (by rw [hd]; decide)
  exact he.symm.trans ha

private theorem BranchFrame.cross_dist_three (h : CubicTreeAction F)
    {a : RankTwo.Vertex F} (b : BranchFrame F a) {i j : Fin 3} (hij : i≠j) :
    (RankTwo.graph F).dist (b.c i) (b.e j).val=3 := by
  have hene : (b.e i).val ≠ (b.e j).val := fun he => hij (b.e.injective (Subtype.ext he))
  have hcne : b.c i ≠ (b.e j).val := by
    intro he
    have ht := (RankTwo.even_dist_iff F h.generated a (b.c i)).mp (by rw [b.c_dist h]; decide)
    exact (b.e j).property.1 (ht.trans (congrArg (fun v : RankTwo.Vertex F => v.type) he))
  let p : (RankTwo.graph F).Walk (b.c i) (b.e j).val :=
    .cons (b.c_adj i).symm (.cons (b.e i).property.symm (.cons (b.e j).property .nil))
  have hai : (RankTwo.graph F).Adj a (b.e i).val := (b.e i).property
  have haj : (RankTwo.graph F).Adj a (b.e j).val := (b.e j).property
  have hp : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    change [b.c i,(b.e i).val,a,(b.e j).val].Nodup
    simp [b.c_ne_center i, hcne, hene, (b.c_adj i).ne.symm, hai.ne.symm, haj.ne]
  obtain ⟨q,hq,hlen⟩ := (h.tree.connected (b.c i) (b.e j).val).exists_path_of_dist
  have he : p=q := (h.tree.existsUnique_path _ _).unique hp hq
  have hpL : p.length=3 := rfl
  rw [he] at hpL
  exact hlen.symm.trans hpL

private theorem branch_perms_noncommute :
    ∀ (σ τ : Equiv.Perm (Fin 3)) (i j : Fin 3), i≠j →
      (∀ k, σ k=k ↔ k=i) → (∀ k, τ k=k ↔ k=j) → ¬ Commute σ τ := by
  unfold Commute SemiconjBy
  decide +kernel

private theorem RadiusOneData.branch_action_fixed_iff
    (d : RadiusOneData F) (h : CubicTreeAction F)
    {a : RankTwo.Vertex F} (ha : a.type=d.side) (b : BranchFrame F a) (i j : Fin 3) :
    b.branchAction ⟨d.label (b.c i),d.fixes (b.c i)
      (d.same_type_dist_two h ha (b.c_dist h i)) a
      (by rw [SimpleGraph.dist_comm,b.c_dist h])⟩ j = j ↔ j=i := by
  let g : RankTwo.stabilizer F a := ⟨d.label (b.c i),d.fixes (b.c i)
    (d.same_type_dist_two h ha (b.c_dist h i)) a
    (by rw [SimpleGraph.dist_comm,b.c_dist h])⟩
  change b.branchAction g j=j ↔ j=i
  constructor
  · intro hj
    by_contra hji
    apply d.moves (b.c i) (d.same_type_dist_two h ha (b.c_dist h i))
      (b.e j).val (b.cross_dist_three h (Ne.symm hji))
    change g.val • (b.e j).val = (b.e j).val
    rw [← b.branchAction_eval, hj]
  · intro hji
    subst j
    apply b.e.injective
    apply Subtype.ext
    rw [b.branchAction_eval]
    exact d.fixes (b.c i) (d.same_type_dist_two h ha (b.c_dist h i)) _
      (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr (b.c_adj i).symm]; omega)

private theorem RadiusOneData.impossible
    (d : RadiusOneData F) (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (a : RankTwo.Vertex F) (ha : a.type=d.side) : False := by
  classical
  let H := RankTwo.stabilizer F a
  let : Finite H := h.finite_stabilizer a
  let z : H := ⟨d.label a,(d.central a ha).1⟩
  let Z := zpowers z
  have hzC : z ∈ center H := mem_center_iff.mpr fun x =>
    Subtype.ext ((d.central a ha).2 x x.property).symm.eq
  have hZC : Z ≤ center H := zpowers_le.mpr hzC
  let : Z.Normal := ⟨by
    intro x hx g
    rw [mem_center_iff.mp (hZC hx) g,mul_assoc,mul_inv_cancel,mul_one]
    exact hx⟩
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_zpowers,show orderOf z=2 from (Subgroup.orderOf_coe z).symm.trans (d.order_two a ha)]
    rfl)
  have hodd : pPrimeCore 2 H=⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA a)
  have hoddQ : pPrimeCore 2 (H ⧸ Z)=⊥ :=
    pPrimeCore_quotient_eq_bot_of_central_two_subgroup Z hZC hZtwo hodd
  obtain ⟨b⟩ := h.exists_branchFrame a
  have hcSide (i : Fin 3) : (b.c i).type=d.side :=
    d.same_type_dist_two h ha (b.c_dist h i)
  have hdSide (i : Fin 3) : (b.d i).type=d.side :=
    d.same_type_dist_two h ha (b.d_dist h i)
  have hcH (i : Fin 3) : d.label (b.c i) ∈ H :=
    d.fixes _ (hcSide i) a (by rw [SimpleGraph.dist_comm,b.c_dist h])
  have hdH (i : Fin 3) : d.label (b.d i) ∈ H :=
    d.fixes _ (hdSide i) a (by rw [SimpleGraph.dist_comm,b.d_dist h])
  let c : Fin 3 → H := fun i => ⟨d.label (b.c i),hcH i⟩
  let e : Fin 3 → H := fun i => ⟨d.label (b.d i),hdH i⟩
  let q := QuotientGroup.mk' Z
  let x : Fin 3 → H ⧸ Z := fun i => q (c i)
  have hcpow (i : Fin 3) : c i ^2=1 := Subtype.ext (d.order_two _ (hcSide i) ▸ pow_orderOf_eq_one _)
  have hepow (i : Fin 3) : e i ^2=1 := Subtype.ext (d.order_two _ (hdSide i) ▸ pow_orderOf_eq_one _)
  have hpair (i : Fin 3) : q (e i)=q (c i) := by
    have hp : z*c i*e i=1 := Subtype.ext (d.product _ _ _ _
      (b.e i).property.symm (b.c_adj i) (b.d_adj i)
      (b.c_ne_center i).symm (b.d_ne_center i).symm (b.c_ne_d i) ha)
    have hqz : q z=1 := (QuotientGroup.eq_one_iff z).mpr (mem_zpowers z)
    have he := congrArg q hp
    rw [map_mul,map_mul,hqz,one_mul,map_one] at he
    have hi : (q (e i))⁻¹=q (e i) := inv_eq_of_mul_eq_one_left (by
      rw [←pow_two,←map_pow,hepow,map_one])
    exact ((mul_eq_one_iff_eq_inv.mp he).trans hi).symm
  have hnorm : ∀ (g : H ⧸ Z) (i : Fin 3), ∃ j, g*x i*g⁻¹=x j := by
    intro g i
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective Z g
    have hdist : (RankTwo.graph F).dist a (k.val • b.c i)=2 := by
      have hh := RankTwo.dist_smul F k.val a (b.c i)
      rw [show k.val • a=a from k.property] at hh
      exact hh.trans (b.c_dist h i)
    have htype : (k.val • b.c i).type=a.type := (hcSide i).trans ha.symm
    rcases b.radiusTwo_cases h htype hdist.le with hk | ⟨j,hk | hk⟩
    · rw [hk,dist_self] at hdist
      omega
    · refine ⟨j,?_⟩
      change q k*q (c i)*(q k)⁻¹=q (c j)
      rw [←map_inv,←map_mul,←map_mul]
      apply congrArg q
      apply Subtype.ext
      exact (d.conjugate k.val (b.c i) (hcSide i)).symm.trans (congrArg d.label hk)
    · refine ⟨j,?_⟩
      change q k*q (c i)*(q k)⁻¹=q (c j)
      rw [←hpair j,←map_inv,←map_mul,←map_mul]
      apply congrArg q
      apply Subtype.ext
      exact (d.conjugate k.val (b.c i) (hcSide i)).symm.trans (congrArg d.label hk)
  have hker : Z ≤ b.branchAction.ker := by
    apply zpowers_le.mpr
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro i
    apply b.e.injective
    apply Subtype.ext
    rw [b.branchAction_eval]
    exact d.fixes a ha _ (by
      have hai : (RankTwo.graph F).Adj a (b.e i).val := (b.e i).property
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hai]
      omega)
  let φ : H ⧸ Z →* Equiv.Perm (Fin 3) := QuotientGroup.lift Z b.branchAction hker
  have hnc : ∀ i j : Fin 3, i≠j → ¬ Commute (x i) (x j) := by
    intro i j hij hh
    apply branch_perms_noncommute (b.branchAction (c i)) (b.branchAction (c j)) i j hij
      (d.branch_action_fixed_iff h ha b i) (d.branch_action_fixed_iff h ha b j)
    have he := congrArg φ hh.eq
    simp only [map_mul] at he
    change b.branchAction (c i)*b.branchAction (c j) =
      b.branchAction (c j)*b.branchAction (c i) at he
    exact he
  exact normal_triple_oddCore_nontrivial x (fun i => by
    change q (c i)^2=1
    rw [←map_pow,hcpow,map_one]) hnorm hnc hoddQ

/-- The original large source has no equivariant involution labels with
fixed ball two and moved sphere three. This is the radius-one exclusion
in Goldschmidt (6.8), with the neighbor product derived from the source. -/
theorem LargeTreeSource.radius_one_impossible
    {s : ℕ} (h : LargeTreeSource F s) {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s v) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := G) p) (hv : v.type=false)
    (side : Bool) (f : RankTwo.Vertex F → G)
    (ho : ∀ a, a.type=side → orderOf (f a)=2)
    (hc : ∀ a, a.type=side → f a ∈ RankTwo.stabilizer F a ∧
      ∀ g ∈ RankTwo.stabilizer F a, Commute (f a) g)
    (he : ∀ (g : G) a, a.type=side → f (g • a)=g*f a*g⁻¹)
    (hf : ∀ a, a.type=side → ∀ b, (RankTwo.graph F).dist a b≤2 → f a • b=b)
    (hm : ∀ a, a.type=side → ∀ b, (RankTwo.graph F).dist a b=3 → f a • b≠b) : False := by
  let d : RadiusOneData F := ⟨side,f,ho,hc,he,hf,hm,
    h.neighbor_product p hp hn hv side f ho hc he hf⟩
  exact d.impossible h.action.toCubicTreeAction h.not_cubic h.not_alternating
    (RankTwo.base F side) rfl

/-- Every centered interval of the original preferred track has radius at
least two. No label relation or radius-one recognition premise remains. -/
theorem LargeTreeSource.centralInterval_rightMargin_ne_one
    {s : ℕ} (h : LargeTreeSource F s) {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s v) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := G) p) (hv : v.type=false)
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (href : AdjacentInvolutionMovers (RankTwo.graph F) G → t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z) :
    d.rightMargin ≠ 1 := by
  intro hone
  let ht := h.action.toCubicTreeAction
  have hw := ht.centralInterval_length_eq_two h.five_le h.regular p hp hn
    h.not_cubic h.not_alternating t hfinite href hz d
  have he := ht.centralInterval_fixedLength_even h.five_le h.regular p hp hn
    h.not_cubic h.not_alternating t hfinite href hz d
  obtain ⟨hm,hL,hR⟩ := ht.centralInterval_centered_of_length_two
    h.five_le h.regular t hz d hw he
  let c := d.centralLeft+1
  have hc : ∀ g ∈ RankTwo.stabilizer F (t.vertex c), Commute z g :=
    ht.centralizes_vertex_of_two_centralEdges (by have := h.five_le; omega) h.regular t c
      (d.central (c-1) (by dsimp [c]; omega) (by dsimp [c]; omega))
      (d.central c (by dsimp [c]; omega) (by dsimp [c]; omega))
  obtain ⟨f,hz',ho,hcentral,hconj,hball,hsphere⟩ :=
    ht.exists_interval_orbit_labels h.regular t hz d c 1
      (by simpa only [hone] using hL) (by simpa only [hone] using hR) hc
  apply h.radius_one_impossible p hp hn hv (t.vertex c).type f ho hcentral hconj
  · intro a ha b hb
    exact hball a ha b hb (hb.trans (by have := h.five_le; omega))
  · intro a ha b hb
    exact hsphere a ha (by have := h.five_le; omega) b hb

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
