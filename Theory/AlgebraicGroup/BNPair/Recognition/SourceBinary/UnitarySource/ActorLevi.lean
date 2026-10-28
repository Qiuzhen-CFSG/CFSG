module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorPanels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootReflections

/-!
# The actual opposite Levi and reflection inside each root actor

Intersect an endpoint with its opposite under the longest Weyl element.
The two generating roots lie in this intersection. Increasing Bruhat
multiplication traps its intersection with B and B^s in H, and the split
root factorization then identifies its Borel part with X_i H. Thus
R_i ∩ U = X_i, without assuming U ∩ U^s is in the panel kernel.

The already constructed transitive action of R_i on the SAME panel gives
an element taking B to sB. The Levi factorization removes its root and
Cartan factors and produces an element of R_i ∩ sH. An odd power makes
this lift an involution. Finally, H normalizes R_i and is odd, so every
two-element of H R_i belongs to R_i; this will coordinate both lifts
inside one Sylow subgroup of N.

Source: Fong--Seitz I (5C) and the following choice of s_i, printed
pp.25--26; Carter 2.5.3--2.5.6. The ascent argument extends the checked
RootLocalCover argument to the whole opposite Levi. The normality and
module realizations in I (5I), (6A) remain separate source obligations.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem opposite_simple_mem (i : Fin 2) :
    longest Q * Q.simple i * longest Q ∈ Q.tits.S := by
  have hlen : Q.tits.wordLength (longest Q * Q.simple i * longest Q) = 1 := by
    rw [mul_assoc, length_longest_mul, wordLength_simple_mul_longest]
    have := rotationOrder_ge_two Q
    omega
  obtain ⟨l, hl, hS, he⟩ := Q.tits.wordLength_spec (longest Q * Q.simple i * longest Q)
  rw [hlen] at hl
  obtain ⟨s,rfl⟩ := List.length_eq_one_iff.mp hl
  have hs : s ∈ Q.tits.S := hS s (by simp)
  have he' : s = longest Q * Q.simple i * longest Q := by simpa using he
  exact he' ▸ hs

@[expose] def oppositeLevi (i : Fin 2) : Subgroup (X ⧸ Q.D) :=
  Q.tits.standardParabolic {Q.simple i} ⊓
    (Q.tits.standardParabolic {longest Q * Q.simple i * longest Q}).comap
      (MulAut.conj ((representative (longest Q) : X ⧸ Q.D)⁻¹)).toMonoidHom

private theorem simple_square (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem unipotentConjugate_le_endpoint (w : Weyl Q) :
    unipotentConjugate split w ≤ Q.tits.standardParabolic {w} := by
  let n := representative w
  have hn : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {w} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  intro x hx
  have h := (Q.tits.standardParabolic {w}).mul_mem
    ((Q.tits.standardParabolic {w}).mul_mem ((Q.tits.standardParabolic {w}).inv_mem hn)
      (Q.tits.B_le_standardParabolic _ (split.U_le hx))) hn
  change (n : X ⧸ Q.D)⁻¹*((n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹)*(n : X ⧸ Q.D) ∈ _ at h
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

theorem rootActor_le_oppositeLevi (i : Fin 2) : rootActor Q split i ≤ oppositeLevi Q i := by
  apply le_inf (rootActor_le_endpoint Q split i)
  let n := representative (longest Q)
  have hc : rightConjugate (rootActor Q split i) (n : X ⧸ Q.D) ≤
      Q.tits.standardParabolic {longest Q * Q.simple i * longest Q} := by
    change (simpleRoot Q split i ⊔ oppositeRoot Q split i).comap
      (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom ≤ _
    rw [← comap_sup_eq _ _ _ (MulAut.conj (n : X ⧸ Q.D)).surjective]
    have hXi : simpleRoot Q split i ≤ unipotentConjugate split (longest Q * Q.simple i) := inf_le_right
    apply sup_le
    · have h := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hXi
      change _ ≤ rightConjugate (unipotentConjugate split (longest Q * Q.simple i)) _ at h
      rw [unipotentConjugate_right split _ _ n (representative_spec _)] at h
      exact h.trans (unipotentConjugate_le_endpoint Q split _)
    · have h := comap_mono (f := (MulAut.conj
        (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) hXi
      change oppositeRoot Q split i ≤ rightConjugate
        (unipotentConjugate split (longest Q * Q.simple i)) _ at h
      rw [unipotentConjugate_right split _ _ _ (representative_spec _),
        mul_assoc, simple_square, mul_one] at h
      have h' := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) h
      change _ ≤ rightConjugate (unipotentConjugate split (longest Q)) _ at h'
      rw [unipotentConjugate_right split _ _ n (representative_spec _),
        longest_mul_self, unipotentConjugate_one] at h'
      exact h'.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  intro x hx
  apply hc
  change (n : X ⧸ Q.D)*((n : X ⧸ Q.D)⁻¹*x*((n : X ⧸ Q.D)⁻¹)⁻¹)*(n : X ⧸ Q.D)⁻¹ ∈ rootActor Q split i
  simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hx

theorem torus_le_oppositeLevi (i : Fin 2) : Q.tits.B ⊓ Q.tits.N ≤ oppositeLevi Q i := by
  apply le_inf (inf_le_left.trans (Q.tits.B_le_standardParabolic _))
  intro x hx
  have hc := (torus_conjugate (representative (longest Q))⁻¹).symm ▸ hx
  exact Q.tits.B_le_standardParabolic _ hc.1

theorem simple_lift_mem_oppositeLevi (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    (n : X ⧸ Q.D) ∈ oppositeLevi Q i := by
  refine ⟨Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
    (Q.tits.representative_mem_bruhatCell _ n hn), ?_⟩
  let m := representative (longest Q)
  have he : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      (m⁻¹*n*m) = longest Q * Q.simple i * longest Q := by
    rw [map_mul,map_mul,map_inv,representative_spec,hn,longest_inv]
  change (m : X ⧸ Q.D)⁻¹*(n : X ⧸ Q.D)*((m : X ⧸ Q.D)⁻¹)⁻¹ ∈
    Q.tits.standardParabolic {longest Q * Q.simple i * longest Q}
  rw [inv_inv]
  exact Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
    (Q.tits.representative_mem_bruhatCell _ (m⁻¹*n*m) he)

private theorem parabolic_inf_ascent_borel
    {s w : Weyl Q} (hs : s ∈ Q.tits.S)
    (hlen : Q.tits.wordLength w ≤ Q.tits.wordLength (s*w)) :
    Q.tits.standardParabolic {s} ⊓ borelConjugate w⁻¹ ≤ Q.tits.B := by
  intro x hx
  have hxcell : x ∈ (Q.tits.B : Set (X ⧸ Q.D)) ∪ Q.tits.bruhatCell s :=
    singleton_parabolic_cells hs ▸ hx.1
  rcases hxcell with hxB | hxS
  · exact hxB
  · let nw := representative w
    have hprod : x * (nw : X ⧸ Q.D) ∈ Q.tits.bruhatCell (s*w) :=
      Q.tits.bruhatCell_mul_bruhatCell_subset_of_wordLength_le hs w hlen
        ⟨x, hxS, nw, Q.tits.representative_mem_bruhatCell w nw (representative_spec _), rfl⟩
    have hx' := hx.2
    rw [borelConjugate_eq w⁻¹ nw⁻¹ (by rw [map_inv, representative_spec])] at hx'
    have hh := mul_mem_doubleCoset Q.tits.B Q.tits.N w Q.tits.B.one_mem hx'
      (Q.tits.representative_mem_bruhatCell w nw (representative_spec _))
    have hsame : x * (nw : X ⧸ Q.D) ∈ Q.tits.bruhatCell w := by
      change 1 * (nw : X ⧸ Q.D) * ((nw : X ⧸ Q.D)⁻¹ * x *
        ((nw : X ⧸ Q.D)⁻¹)⁻¹) ∈ Q.tits.bruhatCell w at hh
      simpa only [Subgroup.coe_inv, inv_inv, one_mul, mul_inv_cancel_left, mul_assoc] using hh
    have he := Q.tits.doubleCoset_index_unique hprod hsame
    exact False.elim ((Q.tits.involutions s hs).1
      (mul_right_cancel (he.trans (one_mul w).symm)))


include split in
theorem oppositeLevi_inf_two_borels_le_torus (i : Fin 2) :
    oppositeLevi Q i ⊓ (Q.tits.B ⊓ borelConjugate (Q.simple i)) ≤ Q.tits.B ⊓ Q.tits.N := by
  let n := representative (longest Q)
  have hi : (Q.simple i)⁻¹ = Q.simple i := inv_eq_of_mul_eq_one_right (simple_square Q i)
  have hw : (longest Q * Q.simple i * longest Q) * (longest Q * Q.simple i) = longest Q := by
    simp only [mul_assoc, ← mul_assoc (longest Q) (longest Q), longest_mul_self,
      one_mul, simple_square, mul_one]
  have hlen : Q.tits.wordLength (longest Q * Q.simple i) ≤
      Q.tits.wordLength ((longest Q * Q.simple i * longest Q) * (longest Q * Q.simple i)) := by
    rw [hw, wordLength_longest_mul_simple, wordLength_longest]
    exact Nat.sub_le _ _
  intro x hx
  let y := (n : X ⧸ Q.D)⁻¹*x*(n : X ⧸ Q.D)
  have hyP : y ∈ Q.tits.standardParabolic {longest Q * Q.simple i * longest Q} := by
    have hp := hx.1.2
    change (n : X ⧸ Q.D)⁻¹*x*((n : X ⧸ Q.D)⁻¹)⁻¹ ∈
      Q.tits.standardParabolic {longest Q * Q.simple i * longest Q} at hp
    simpa only [inv_inv] using hp
  have hyB : y ∈ borelConjugate (longest Q * Q.simple i)⁻¹ := by
    let ns := representative (Q.simple i)
    rw [mul_inv_rev, hi, longest_inv,
      borelConjugate_eq (Q.simple i * longest Q) (ns*n)
        (by rw [map_mul,representative_spec,representative_spec])]
    have hxB := hx.2.2
    change (ns : X ⧸ Q.D)*x*(ns : X ⧸ Q.D)⁻¹ ∈ Q.tits.B at hxB
    change ((ns : X ⧸ Q.D)*(n : X ⧸ Q.D))*
      ((n : X ⧸ Q.D)⁻¹*x*(n : X ⧸ Q.D))*
      ((ns : X ⧸ Q.D)*(n : X ⧸ Q.D))⁻¹ ∈ Q.tits.B
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hxB
  have hy := parabolic_inf_ascent_borel Q (opposite_simple_mem Q i) hlen ⟨hyP,hyB⟩
  rw [← borel_inf_opposite Q split]
  refine ⟨hx.2.1, ?_⟩
  rw [borelConjugate_eq (longest Q) n⁻¹ (by rw [map_inv,representative_spec,longest_inv])]
  change (n : X ⧸ Q.D)⁻¹*x*((n : X ⧸ Q.D)⁻¹)⁻¹ ∈ Q.tits.B
  simpa only [inv_inv] using hy

/-- The Borel intersection of the opposite Levi is exactly X_i H. -/
theorem oppositeLevi_borel_factorization (i : Fin 2) {x : X ⧸ Q.D}
    (hxJ : x ∈ oppositeLevi Q i) (hxB : x ∈ Q.tits.B) :
    ∃ a ∈ simpleRoot Q split i, ∃ h ∈ Q.tits.B ⊓ Q.tits.N, x = a*h := by
  have hB : (Q.tits.B : Set (X ⧸ Q.D)) =
      (split.U : Set (X ⧸ Q.D)) * (Q.tits.B ⊓ Q.tits.N : Set (X ⧸ Q.D)) := by
    nth_rw 1 [← split.factorization]
    exact coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans split.normalizes)
  have hxprod : x ∈ (split.U : Set (X ⧸ Q.D)) * (Q.tits.B ⊓ Q.tits.N : Set (X ⧸ Q.D)) := by
    rw [← hB]; exact hxB
  obtain ⟨u,hu,h,hh,rfl⟩ := hxprod
  have hu' : u ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
    rw [simpleRoot_mul_remainder]; exact hu
  obtain ⟨a,ha,v,hv,rfl⟩ := hu'
  have htail : v*h ∈ oppositeLevi Q i := by
    have he := (oppositeLevi Q i).mul_mem
      ((oppositeLevi Q i).inv_mem (rootActor_le_oppositeLevi Q split i (mem_sup_left ha))) hxJ
    simpa only [mul_assoc,inv_mul_cancel_left] using he
  have htB : v*h ∈ Q.tits.B := Q.tits.B.mul_mem (split.U_le hv.1) hh.1
  have htBs : v*h ∈ borelConjugate (Q.simple i) := by
    apply (borelConjugate (Q.simple i)).mul_mem
    · exact (comap_mono split.U_le) hv.2
    · have hh' : h ∈ (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) := hh
      exact ((torus_conjugate (representative (Q.simple i))).symm ▸ hh').1
  exact ⟨a,ha,v*h,oppositeLevi_inf_two_borels_le_torus Q split i ⟨htail,htB,htBs⟩,
    mul_assoc _ _ _⟩

/-- The root actor has its own full Borel, with the actual Cartan intersection. -/
theorem rootActor_borel_factorization (i : Fin 2) {x : X ⧸ Q.D}
    (hxR : x ∈ rootActor Q split i) (hxB : x ∈ Q.tits.B) :
    ∃ a ∈ simpleRoot Q split i, ∃ h ∈ rootActor Q split i ⊓ (Q.tits.B ⊓ Q.tits.N),
      x = a*h := by
  obtain ⟨a,ha,h,hh,he⟩ := oppositeLevi_borel_factorization Q split i
    (rootActor_le_oppositeLevi Q split i hxR) hxB
  refine ⟨a,ha,h,⟨?_,hh⟩,he⟩
  have ht := (rootActor Q split i).mul_mem
    ((rootActor Q split i).inv_mem (mem_sup_left ha)) hxR
  rwa [he,inv_mul_cancel_left] at ht

theorem rootActor_inf_unipotent (i : Fin 2) :
    rootActor Q split i ⊓ split.U = simpleRoot Q split i := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a,ha,h,hh,he⟩ := rootActor_borel_factorization Q split i hx.1 (split.U_le hx.2)
    have hhU : h ∈ split.U := by
      have ht := split.U.mul_mem (split.U.inv_mem (simpleRoot_le Q split i ha)) hx.2
      rwa [he,inv_mul_cancel_left] at ht
    have hh1 : h = 1 := by
      have hm : h ∈ split.U ⊓ Q.tits.N := ⟨hhU,hh.2.2⟩
      rwa [split.unipotent_inf_N,mem_bot] at hm
    simpa only [he,hh1,mul_one] using ha
  · exact le_inf le_sup_left (simpleRoot_le Q split i)

/-- The source R_i contains a representative of its marked simple Weyl class. -/
theorem exists_actor_weyl_lift (i : Fin 2) :
    ∃ n : Q.tits.N,
      QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i ∧
      (n : X ⧸ Q.D) ∈ rootActor Q split i := by
  let n := representative (Q.simple i)
  obtain ⟨r,hr⟩ := exists_actor_from_base Q split i (oppositePoint Q i)
  have he : QuotientGroup.mk (r.val : PanelEndpoint Q i) =
      (QuotientGroup.mk (ReeSource.reflectionLift Q i) : Panel Q i) := by
    rw [ReeSource.panelBase_eq_mk_one Q split i] at hr
    change QuotientGroup.mk ((r.val : PanelEndpoint Q i)*1) =
      (QuotientGroup.mk (ReeSource.reflectionLift Q i) : Panel Q i) at hr
    simpa only [mul_one] using hr
  have hb : (r.val : X ⧸ Q.D)⁻¹*(n : X ⧸ Q.D) ∈ Q.tits.B := by
    exact (QuotientGroup.eq.mp he : (r.val : PanelEndpoint Q i)⁻¹ * ReeSource.reflectionLift Q i ∈
      Q.tits.B.subgroupOf (PanelEndpoint Q i))
  have hj : (r.val : X ⧸ Q.D)⁻¹*(n : X ⧸ Q.D) ∈ oppositeLevi Q i :=
    (oppositeLevi Q i).mul_mem
      ((oppositeLevi Q i).inv_mem (rootActor_le_oppositeLevi Q split i r.property))
      (simple_lift_mem_oppositeLevi Q i n (representative_spec _))
  obtain ⟨a,ha,h,hh,hprod⟩ := oppositeLevi_borel_factorization Q split i hj hb
  let hN : Q.tits.N := ⟨h,hh.2⟩
  refine ⟨n*hN⁻¹, ?_, ?_⟩
  · have hhq : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) hN = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hh
    rw [map_mul,map_inv,hhq,inv_one,mul_one,representative_spec]
  · have heq : (n : X ⧸ Q.D)*h⁻¹ = (r.val : X ⧸ Q.D)*a := by
      calc
        (n : X ⧸ Q.D)*h⁻¹ = (r.val : X ⧸ Q.D)*((r.val : X ⧸ Q.D)⁻¹*n)*h⁻¹ := by group
        _ = (r.val : X ⧸ Q.D)*(a*h)*h⁻¹ := by rw [hprod]
        _ = (r.val : X ⧸ Q.D)*a := by group
    change (n : X ⧸ Q.D)*h⁻¹ ∈ rootActor Q split i
    rw [heq]
    exact (rootActor Q split i).mul_mem r.property (mem_sup_left ha)

/-- The source lift can be chosen involutory because H has odd order. -/
theorem exists_actor_involution_lift (i : Fin 2) :
    ∃ n : Q.tits.N,
      QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i ∧
      (n : X ⧸ Q.D) ∈ rootActor Q split i ∧ n^2 = 1 := by
  obtain ⟨n,hn,hr⟩ := exists_actor_weyl_lift Q split i
  let m := Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  obtain ⟨k,hk⟩ := split.odd.odd_of_left
  have hm : m = 2*k+1 := by dsimp only [m]; omega
  refine ⟨n^m, ?_, (rootActor Q split i).pow_mem hr m, ?_⟩
  · rw [map_pow,hn,hm,pow_add,pow_mul,(Q.tits.involutions _ (Q.simple_mem i)).2,one_pow,pow_one,one_mul]
  · apply Subtype.ext
    have ht : (n : X ⧸ Q.D)^2 ∈ Q.tits.B ⊓ Q.tits.N :=
      Q.tits.representative_sq_mem_intersection (Q.simple_mem i) n hn
    have he := congrArg Subtype.val
      (pow_card_eq_one' (x := (⟨(n : X ⧸ Q.D)^2,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N))))
    change ((n : X ⧸ Q.D)^m)^2 = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact he

/-- A constructed witness of the earlier-source RootReflection contract. -/
@[expose] def actorReflection (i : Fin 2) : HexagonStructure.RootReflection Q split i where
  val := (exists_actor_involution_lift Q split i).choose
  class_eq := (exists_actor_involution_lift Q split i).choose_spec.1
  mem_rankOne := (exists_actor_involution_lift Q split i).choose_spec.2.1

@[simp] theorem actorReflection_square (i : Fin 2) : (actorReflection Q split i).val^2 = 1 :=
  (exists_actor_involution_lift Q split i).choose_spec.2.2

/-- Every two-element of H R_i already belongs to R_i. -/
theorem mem_rootActor_of_two_power (i : Fin 2) {x : X ⧸ Q.D}
    (hx : x ∈ rootActor Q split i ⊔ (Q.tits.B ⊓ Q.tits.N))
    (k : ℕ) (hk : x^(2^k) = 1) : x ∈ rootActor Q split i := by
  let R := rootActor Q split i
  let H := Q.tits.B ⊓ Q.tits.N
  let J := R ⊔ H
  let R' := R.subgroupOf J
  let : R'.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le R.le_normalizer (torus_normalizes_rootActor Q split i))
  have hindex : R'.index = R.relIndex H := by
    have he := relIndex_sup_left (H.subgroupOf J) R'
    rw [← subgroupOf_sup le_sup_left le_sup_right,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_right] at he
    exact he
  let z : J ⧸ R' := QuotientGroup.mk' R' ⟨x,hx⟩
  have hz : z^(2^k) = 1 := by
    rw [← map_pow]
    exact congrArg (QuotientGroup.mk' R') (Subtype.ext hk)
  have hdiv : Nat.card (J ⧸ R') ∣ Nat.card H := by
    change R'.index ∣ Nat.card H
    rw [hindex]
    exact relIndex_dvd_card R H
  have hord : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes (split.odd.pow_left k)
    (orderOf_dvd_of_pow_eq_one hz)
    ((orderOf_dvd_natCard z).trans hdiv)
  exact ((QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hord) : (⟨x,hx⟩ : J) ∈ R')

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
