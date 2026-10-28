module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiKernelIntersections
public import Theory.Representation.Suzuki.FixedFreeSmallAction
/-!
# Disjoint rank-one Cartans in a regular Suzuki hexagon

The genuine involutory source reflection inverts H ∩ R_i. Hence a cyclic
subgroup of H ∩ R_i ∩ R_j is normalized by both simple lifts and by H,
so is normalized by N. Suzuki Sylow centralizers make a nonidentity element
fixed-point-free on both simple roots. N-normality and unique five-root
coordinates extend this to the entire opposite radical.

The literal radical has order q¹⁰. Root movement makes its Frattini action
nontrivial, yielding the lower bound q⁴ on the Frattini subgroup. The small
Suzuki fixed-point-free action theorem contradicts these two orders.
Thus the actual two rank-one Cartans have trivial intersection.

Source: Fong--Seitz I (6C), printed p.41, the rank-one Cartan intersection
preceding the derived-radical argument. The native parameter is positive;
small Suzuki and the subsequent commutator contradiction remain separate.
All roots, actors and conjugation words belong to the same marked quotient.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The involutory source reflection inverts its actual rank-one Cartan. -/
theorem suzuki_rankOne_cartan_inverted (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (s : RootReflection Q split j) {z : X ⧸ Q.D}
    (hzH : z ∈ Q.tits.B ⊓ Q.tits.N) (hzR : z ∈ rankOne Q split j) :
    let r := involutoryRootReflection Q split j s
    (r.val : X ⧸ Q.D)*z*(r.val : X ⧸ Q.D)⁻¹ = z⁻¹ := by
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_suzuki Q split j μ ν
  let r := involutoryRootReflection Q split j s
  let t : rankOne Q split j := ⟨r.val,r.mem_rankOne⟩
  have ht : IsInvolution t := ⟨fun he => involutoryRootReflection_ne_one Q split j s
    (congrArg Subtype.val he),Subtype.ext (involutoryRootReflection_sq Q split j s)⟩
  have htB : t ∉ normalizer (S : Set (rankOne Q split j)) := by
    intro htB
    rw [show (S : Set (rankOne Q split j)) =
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS] at htB
    exact Q.tits.representative_not_mem_B (Q.simple_mem j) r.val r.class_eq
      ((rankOne_borel_iff_root_normalizer Q split j hKj t).mpr htB)
  have he : BenderSuzuki.ZD.RankOneModelGeometry.twoPoint (normalizer (S : Set (rankOne Q split j))) t =
      (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) := by
    ext x
    change x ∈ normalizer (S : Set (rankOne Q split j)) ∧
      x ∈ BenderSuzuki.PFchapter1section1.rightConjugate (normalizer (S : Set (rankOne Q split j))) t ↔ _
    rw [BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.mem_rightConjugate]
    simp only [show (S : Set (rankOne Q split j)) =
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS,
      ← rankOne_borel_iff_root_normalizer Q split j hKj]
    constructor
    · intro hx
      apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split j
      refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split j x.property,hx.1,?_⟩
      rw [borelConjugate_eq _ r.val r.class_eq]
      exact hx.2
    · intro hx
      exact ⟨hx.1,((torus_conjugate r.val).symm ▸ hx).1⟩
  have hh := BenderSuzuki.ZD.RankOneModelGeometry.suzuki_twoPoint_geometry hm μ S t ht htB
  rw [he] at hh
  have hi := hh.2.2.1 (⟨z,hzR⟩ : rankOne Q split j) hzH
  have hr : (r.val : X ⧸ Q.D)⁻¹ = r.val :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
      (involutoryRootReflection_sq Q split j s))
  change (r.val : X ⧸ Q.D)*z*(r.val : X ⧸ Q.D)⁻¹ = z⁻¹
  have hv := congrArg Subtype.val hi
  change (r.val : X ⧸ Q.D)⁻¹*z*r.val = z⁻¹ at hv
  simpa only [hr] using hv

private theorem root_fixedFree_conjugates (i : Fin 2)
    (T : Subgroup (X ⧸ Q.D)) (hTN : Q.tits.N ≤ normalizer (T : Set (X ⧸ Q.D)))
    (hf : simpleRoot Q split i ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥) (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ := by
  let n := representative w
  have hh := congrArg (fun A => rightConjugate A (n : X ⧸ Q.D)) hf
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer T (hTN n.property))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) = ⊥ := by
    ext x
    change (n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹ = 1 ↔ x = 1
    exact (MulAut.conj (n : X ⧸ Q.D)).map_eq_one_iff
  exact hh.trans hb

private theorem normalizer_le_of_simple_lifts
    (i j : Fin 2) (hij : i ≠ j) (a b : Q.tits.N)
    (ha : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) a = Q.simple i)
    (hb : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) b = Q.simple j)
    (A : Subgroup (X ⧸ Q.D)) (hH : Q.tits.B ⊓ Q.tits.N ≤ A)
    (haA : (a : X ⧸ Q.D) ∈ A) (hbA : (b : X ⧸ Q.D) ∈ A) : Q.tits.N ≤ A := by
  classical
  let n (k : Fin 2) := if k = i then a else b
  have hn (k : Fin 2) : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (n k) = Q.simple k := by
    by_cases hk : k = i
    · simpa [n,hk] using ha
    · have hkj : k = j := by omega
      simpa [n,hkj,hij.symm] using hb
  have hnA (k : Fin 2) : (n k : X ⧸ Q.D) ∈ A := by
    dsimp only [n]
    split_ifs <;> assumption
  intro g hg
  let q := QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
  let gN : Q.tits.N := ⟨g,hg⟩
  obtain ⟨k,hk,hqk⟩ := UnitarySource.exists_weyl_lift_in Q n hn A hnA (q gN)
  have hdiff : gN*k⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (gN*k⁻¹) = 1
    rw [map_mul,map_inv,hqk,mul_inv_cancel]
  have hz := A.mul_mem (hH hdiff) hk
  change (g*(k : X ⧸ Q.D)⁻¹)*(k : X ⧸ Q.D) ∈ A at hz
  simpa only [inv_mul_cancel_right] using hz

/-- A cyclic subgroup of both rank-one Cartans is normalized by N.
The two specified source reflections invert it and H centralizes it. -/
theorem suzuki_cartan_intersection_zpowers_normalized (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n)
    {z : X ⧸ Q.D} (hzH : z ∈ Q.tits.B ⊓ Q.tits.N)
    (hzi : z ∈ rankOne Q split i) (hzj : z ∈ rankOne Q split j) :
    Q.tits.N ≤ normalizer (zpowers z : Set (X ⧸ Q.D)) := by
  let a := involutoryRootReflection Q split i (UnitarySource.actorReflection Q split i)
  let b := involutoryRootReflection Q split j (UnitarySource.actorReflection Q split j)
  have ha := suzuki_rankOne_cartan_inverted Q split i hKi hm μi νi
    (UnitarySource.actorReflection Q split i) hzH hzi
  have hb := suzuki_rankOne_cartan_inverted Q split j hKj hn μj νj
    (UnitarySource.actorReflection Q split j) hzH hzj
  have hnorm (t : X ⧸ Q.D) (ht : t*z*t⁻¹ = z⁻¹) :
      t ∈ normalizer (zpowers z : Set (X ⧸ Q.D)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (t*z*t⁻¹) = zpowers z
    rw [ht,zpowers_inv]
  let := split.abelian
  have hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (zpowers z : Set (X ⧸ Q.D)) :=
    ((Subgroup.le_centralizer (Q.tits.B ⊓ Q.tits.N)).trans
      (centralizer_le (zpowers_le.mpr hzH))).trans (_root_.centralizer_le_normalizer (zpowers z))
  exact normalizer_le_of_simple_lifts Q i j hij a.val b.val a.class_eq b.class_eq
    _ hH (hnorm _ ha) (hnorm _ hb)

/-- Unique five-root coordinates pass fixed-freeness on both root types
to the actual radical. -/
theorem radical_centralizer_eq_bot (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (T : Subgroup (X ⧸ Q.D))
    (hTH : T ≤ Q.tits.B ⊓ Q.tits.N)
    (hfi : ∀ w, rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hfj : ∀ w, rootAt Q split j w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥) :
    simpleRemainder Q split j ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j)
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  obtain ⟨⟨a,b,c,d,e⟩,he⟩ := (radicalCoordinates Q split hhex i j hij).surjective ⟨x,hx.1⟩
  have he' : (a : X ⧸ Q.D)*b*c*d*e = x := by
    simpa only [radicalCoordinates_apply] using congrArg Subtype.val he
  have htuple (t : X ⧸ Q.D) (ht : t ∈ T) :
      (A.normalizerMonoidHom ⟨t,torus_normalizes_simpleRoot Q split i (hTH ht)⟩ a,
       B.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ (hTH ht)⟩ b,
       C.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split i _ (hTH ht)⟩ c,
       D.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ (hTH ht)⟩ d,
       E.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split i _ (hTH ht)⟩ e) =
        (a,b,c,d,e) := by
    apply (radicalCoordinates Q split hhex i j hij).injective
    apply Subtype.ext
    simp only [radicalCoordinates_apply]
    change (t*a*t⁻¹)*(t*b*t⁻¹)*(t*c*t⁻¹)*(t*d*t⁻¹)*(t*e*t⁻¹) = (a : X ⧸ Q.D)*b*c*d*e
    calc
      _ = t*((a : X ⧸ Q.D)*b*c*d*e)*t⁻¹ := by group
      _ = _ := by
        rw [he', mem_centralizer_iff.mp hx.2 t ht, mul_inv_cancel_right]
  have ha : (a : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.1 : X ⧸ Q.D)) (htuple t ht))
  have ha1 : (a : X ⧸ Q.D) = 1 := mem_bot.mp
    ((by simpa only [rootAt_one] using hfi 1) ▸ ⟨a.property,ha⟩)
  have hb : (b : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.1 : X ⧸ Q.D)) (htuple t ht))
  have hb1 : (b : X ⧸ Q.D) = 1 := mem_bot.mp (hfj _ ▸ ⟨b.property,hb⟩)
  have hc : (c : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.2.1 : X ⧸ Q.D)) (htuple t ht))
  have hc1 : (c : X ⧸ Q.D) = 1 := mem_bot.mp (hfi _ ▸ ⟨c.property,hc⟩)
  have hd : (d : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.2.2.1 : X ⧸ Q.D)) (htuple t ht))
  have hd1 : (d : X ⧸ Q.D) = 1 := mem_bot.mp (hfj _ ▸ ⟨d.property,hd⟩)
  have he : (e : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.2.2.2 : X ⧸ Q.D)) (htuple t ht))
  have he1 : (e : X ⧸ Q.D) = 1 := mem_bot.mp (hfi _ ▸ ⟨e.property,he⟩)
  simpa only [ha1,hb1,hc1,hd1,he1,mul_one] using he'.symm

/-- The actual equal-parameter Suzuki radical admits no fixed-point-free
odd Cartan element in its rank-one actor. -/
theorem suzuki_radical_not_fixedFree (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m) (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    {z : X ⧸ Q.D} (hzH : z ∈ Q.tits.B ⊓ Q.tits.N)
    (hzj : z ∈ rankOne Q split j)
    (hf : simpleRemainder Q split j ⊓ centralizer ({z} : Set (X ⧸ Q.D)) = ⊥) : False := by
  let d := radicalSection Q split j hKj
  let ρ := d.numeratorAction.comp μj.symm.toMonoidHom
  let t := μj ⟨z,hzj⟩
  have ho : Odd (orderOf t) := by
    have he : orderOf t = orderOf (⟨z,hzH⟩ : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) := by
      rw [show orderOf t = orderOf (⟨z,hzj⟩ : rankOne Q split j) from
        orderOf_injective μj.toMonoidHom μj.injective _]
      rw [←orderOf_injective (rankOne Q split j).subtype (rankOne Q split j).subtype_injective,
        ←orderOf_injective (Q.tits.B ⊓ Q.tits.N).subtype (Q.tits.B ⊓ Q.tits.N).subtype_injective]
      rfl
    rw [he]
    exact (Nat.coprime_two_left.mp split.odd).of_dvd_nat (orderOf_dvd_natCard _)
  have hfree : ∀ x : d.numerator, ρ t x = x → x = 1 := by
    intro x hx
    have hv := congrArg Subtype.val hx
    change (d.numeratorAction (μj.symm (μj ⟨z,hzj⟩)) x : X ⧸ Q.D) = x at hv
    rw [MulEquiv.symm_apply_apply,d.numeratorAction_apply] at hv
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hf]
    exact ⟨x.property,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hv).symm⟩
  have hcard : Nat.card d.numerator = 2^(10*(2*m+1)) := by
    have hc := Nat.card_congr (radicalCoordinates Q split hhex i j hij).symm
    change Nat.card (simpleRemainder Q split j) = _
    rw [hc]
    simp only [Nat.card_prod,rootAt,card_rightConjugate,
      Nat.card_congr νi.toEquiv,Nat.card_congr νj.toEquiv,matrixRoot_card]
    simp only [←pow_add,←pow_mul]
    congr 1
    omega
  let f := frattiniSection Q split j d
  have hbound := suzuki_section_card_bound Q split j hm μj f
    (suzuki_frattini_radical_action_ne_one Q split j hhex i hij
      (UnitarySource.actorReflection Q split j) hKj νj)
  have hPhi : 2^(4*(2*m+1)) ≤ Nat.card (frattini d.numerator) := by
    apply hbound.trans
    calc
      Nat.card f.EffectiveCarrier ≤ Nat.card f.numerator :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ = Nat.card (frattini d.numerator) :=
        Nat.card_congr ((frattini d.numerator).equivMapOfInjective
          d.numerator.subtype d.numerator.subtype_injective).symm.toEquiv
  exact SuzukiFixedFreeAction.no_fixedFree_of_card_ten hm
    (split.isTwo.to_le (show d.numerator ≤ split.U from inf_le_left)) ρ t ho hfree hcard hPhi

/-- The two actual rank-one Cartans in a regular Suzuki hexagon have
trivial intersection, as asserted at the start of Fong--Seitz I p.41. -/
theorem suzuki_rankOne_cartans_disjoint (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i) ⊓
      ((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j) = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  apply mem_bot.mpr
  by_contra hz1
  let T := zpowers z
  have hTH : T ≤ Q.tits.B ⊓ Q.tits.N := zpowers_le.mpr hz.1.1
  have hTN := suzuki_cartan_intersection_zpowers_normalized Q split i j hij hKi hKj
    hm hm μi μj νi νj hz.1.1 hz.1.2 hz.2.2
  have hcen : centralizer (T : Set (X ⧸ Q.D)) = centralizer ({z} : Set (X ⧸ Q.D)) := by
    dsimp only [T]
    rw [zpowers_eq_closure,centralizer_closure]
  have hfi : simpleRoot Q split i ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ := by
    rw [hcen]
    exact suzuki_rankOne_cartan_root_fixedFree Q split i hm μi νi hz.1.1 hz.1.2 hz1
  have hfj : simpleRoot Q split j ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ := by
    rw [hcen]
    exact suzuki_rankOne_cartan_root_fixedFree Q split j hm μj νj hz.1.1 hz.2.2 hz1
  have hf := radical_centralizer_eq_bot Q split hhex i j hij T hTH
    (root_fixedFree_conjugates Q split i T hTN hfi)
    (root_fixedFree_conjugates Q split j T hTN hfj)
  rw [hcen] at hf
  exact suzuki_radical_not_fixedFree Q split hhex i j hij hKj hm μj νi νj hz.1.1 hz.2.2 hf

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
