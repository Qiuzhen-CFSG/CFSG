module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleSection
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The elementary normal closure of the binary middle root

Let V be the seven-root radical, J its five middle roots and A the middle
odd root. Since J is normal in V and centralizes A, the V-normal closure E
of A lies in Z(J). In degree one A has order two, so E is elementary
abelian. The perpendicular rank-one commutator and full Cartan normalization
make E invariant under the entire marked parabolic.

The already proved normality of C_V(A) identifies it with C_V(E). Thus the
literal quotient V/C_V(A) acts faithfully on E by conjugation. The conjugacy
orbit of the nonidentity element of A embeds in E minus its identity; hence
its size [V:C_V(A)] is strictly smaller than |E|. Since |E| divides 128,
indices four and sixteen force |E| at least eight and thirty-two respectively.

These are concrete normal-subgroup inputs to the remaining degree-one
argument in Fong--Seitz I (1973), (6G), printed p.50. They do not establish
whole-radical centrality or the terminal exclusion. Original-factor and
Chapter 12 applications are in LinearPairCubicClosureSource and
SourceSelection/LinearPairCubicClosureChapter12.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

private def relativeClosure {Y : Type*} [Group Y] (V A : Subgroup Y) : Subgroup Y :=
  (normalClosure (A.subgroupOf V : Set V)).map V.subtype

private theorem relativeClosure_le {Y : Type*} [Group Y] (V A K : Subgroup Y)
    (hn : V ≤ normalizer (K : Set Y)) (hAK : A ≤ K) : relativeClosure V A ≤ K := by
  let : (K.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer hn
  apply map_le_iff_le_comap.mpr
  change normalClosure (A.subgroupOf V : Set V) ≤ K.subgroupOf V
  exact normalClosure_le_normal (fun x hx => hAK hx)

private theorem le_relativeClosure {Y : Type*} [Group Y] (V A : Subgroup Y)
    (hAV : A ≤ V) : A ≤ relativeClosure V A := by
  intro a ha
  exact ⟨⟨a,hAV ha⟩,subset_normalClosure ha,rfl⟩

private theorem relativeClosure_normalizes {Y : Type*} [Group Y] (V A : Subgroup Y) :
    V ≤ normalizer (relativeClosure V A : Set Y) := by
  intro v hv
  apply le_normalizer_map V.subtype
  exact ⟨⟨v,hv⟩,by rw [normalizer_eq_top]; trivial,rfl⟩

private theorem relativeClosure_normalizers {Y : Type*} [Group Y] (V A : Subgroup Y) :
    normalizer (V : Set Y) ⊓ normalizer (A : Set Y) ≤
      normalizer (relativeClosure V A : Set Y) := by
  intro g hg
  let f : MulAut V := V.normalizerMonoidHom ⟨g,hg.1⟩
  have hA : f '' (A.subgroupOf V : Set V) = (A.subgroupOf V : Set V) := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact (mem_normalizer_iff.mp hg.2 (b : Y)).mp hb
    · intro ha
      refine ⟨f.symm a,?_,f.apply_symm_apply a⟩
      apply (mem_normalizer_iff.mp hg.2 (f.symm a : Y)).mpr
      change (f (f.symm a) : Y) ∈ A
      rwa [f.apply_symm_apply]
  have hN : (normalClosure (A.subgroupOf V : Set V)).map f.toMonoidHom =
      normalClosure (A.subgroupOf V : Set V) := by
    rw [map_normalClosure _ f.toMonoidHom f.surjective]
    change normalClosure (f '' (A.subgroupOf V : Set V)) = _
    rw [hA]
  rw [mem_normalizer_iff_map_conj_eq]
  change ((normalClosure (A.subgroupOf V : Set V)).map V.subtype).map
    (MulAut.conj g).toMonoidHom = _
  rw [map_map]
  change (normalClosure (A.subgroupOf V : Set V)).map
    (V.subtype.comp f.toMonoidHom) = _
  rw [←map_map,hN]
  rfl

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

@[expose] def middleRootClosure (i j : Fin 2) : Subgroup (X ⧸ Q.D) :=
  (normalClosure ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).subgroupOf
    (simpleRemainder Q split i) : Set (simpleRemainder Q split i))).map
      (simpleRemainder Q split i).subtype

private theorem middle_le_five (i j : Fin 2) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤ middleFive Q split i j :=
  le_sup_of_le_left (le_sup_of_le_left le_sup_right)

/-- The normal closure is relative to the radical and contains the literal middle root. -/
theorem middleRoot_le_closure (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤ middleRootClosure Q split i j :=
  le_relativeClosure _ _ ((middle_le_five Q split i j).trans
    (middleFive_le_remainder Q split hm i j hij))

theorem middleRootClosure_normalized (i j : Fin 2) :
    simpleRemainder Q split i ≤ normalizer (middleRootClosure Q split i j : Set (X ⧸ Q.D)) :=
  relativeClosure_normalizes _ _

/-- Every conjugate of the middle root lies in the center of the five-root subgroup. -/
theorem middleRootClosure_le_middle_center (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hJC : middleFive Q split i j ≤ middleRootCentralizer Q split i j) :
    middleRootClosure Q split i j ≤ middleFive Q split i j ⊓
      centralizer (middleFive Q split i j : Set (X ⧸ Q.D)) := by
  have hn := middleFive_normalized_by_remainder Q split hm i j hij hKj
  apply relativeClosure_le
  · exact (le_inf hn (hn.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  · exact le_inf (middle_le_five Q split i j)
      (le_centralizer_iff.mp (hJC.trans inf_le_right))

/-- A normal centralizer centralizes all radical conjugates of its defining root. -/
theorem middleRootClosure_centralizer (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hn : simpleRemainder Q split i ≤
      normalizer (middleRootCentralizer Q split i j : Set (X ⧸ Q.D))) :
    simpleRemainder Q split i ⊓ centralizer (middleRootClosure Q split i j : Set (X ⧸ Q.D)) =
      middleRootCentralizer Q split i j := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (middleRoot_le_closure Q split hm i j hij))
  · apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    apply relativeClosure_le _ _ _ (hn.trans (normalizer_le_normalizer_centralizer _))
    exact le_centralizer_iff.mp inf_le_right

/-- The normal closure is invariant under the whole marked parabolic.
The rank-one actor centralizes the generating middle root; the full Cartan
normalizes it. Together with the radical they generate the parabolic. -/
theorem middleRootClosure_parabolic_normalizes (i j : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (s : HexagonStructure.RootReflection Q split i)
    (hperp : ⁅rankOne Q split i,
      rightConjugate (rankOne Q split i)
        (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)⁆ = ⊥) :
    Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (middleRootClosure Q split i j : Set (X ⧸ Q.D)) := by
  let A := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let V := simpleRemainder Q split i
  let E := middleRootClosure Q split i j
  have hPA : rankOne Q split i ≤ centralizer (A : Set (X ⧸ Q.D)) :=
    (commutator_eq_bot_iff_le_centralizer.mp hperp).trans
      (centralizer_le (comap_mono (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)))
  have hPV := remainder_parabolic_normalizes Q split i hKi
  have hRN : rankOne Q split i ≤ normalizer (E : Set (X ⧸ Q.D)) :=
    (le_inf ((rankOne_le_parabolic Q split i).trans hPV)
      (hPA.trans (Subgroup.centralizer_le_normalizer _))).trans
        (relativeClosure_normalizers V A)
  have hHN : Q.tits.B ⊓ Q.tits.N ≤ normalizer (E : Set (X ⧸ Q.D)) :=
    (le_inf (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans hPV))
      (rootAt_torus_normalizes Q split i _)).trans (relativeClosure_normalizers V A)
  have hUN : split.U ≤ normalizer (E : Set (X ⧸ Q.D)) := by
    intro x hx
    have hp : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D))*
        (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
      (simpleRoot_mul_remainder Q split i).symm ▸ hx
    obtain ⟨a,ha,v,hv,rfl⟩ := hp
    exact mul_mem (hRN (mem_sup_left ha)) (middleRootClosure_normalized Q split i j hv)
  have hBN : Q.tits.B ≤ normalizer (E : Set (X ⧸ Q.D)) := by
    rw [←split.factorization]
    exact sup_le hUN hHN
  apply Q.tits.standardParabolic_le _ hBN
  intro w hw
  have hw' : w = Q.simple i := Set.mem_singleton_iff.mp hw
  subst w
  exact Q.tits.bruhatCell_subset_of_mem _ hBN
    (Q.tits.representative_mem_bruhatCell _ s.val s.class_eq) (hRN s.mem_rankOne)

/-- The normal closure of the degree-one middle root is elementary abelian. -/
theorem binary_middleRootClosure_elementary (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hJC : middleFive Q split i j ≤ middleRootCentralizer Q split i j) :
    IsElementaryAbelian 2 (middleRootClosure Q split i j) := by
  let V := simpleRemainder Q split i
  let A := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let N := normalClosure (A.subgroupOf V : Set V)
  have hE := middleRootClosure_le_middle_center Q split hm i j hij hKj hJC
  let : IsMulCommutative (middleRootClosure Q split i j) := ⟨⟨fun x y => Subtype.ext
    (mem_centralizer_iff.mp (hE y.property).2 _ (hE x.property).1)⟩⟩
  let : IsMulCommutative N := ⟨⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (s := middleRootClosure Q split i j)
      (mem_map_of_mem V.subtype x.property) (mem_map_of_mem V.subtype y.property)⟩⟩
  have hA : Nat.card A = 2 := by simpa only [A,rootAt,card_rightConjugate] using hi
  let : IsElementaryAbelian 2 A := by
    let : IsCyclic A := isCyclic_of_prime_card hA
    exact { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a => by
      simpa only [hA] using pow_card_eq_one' (x := a)) }
  let : IsElementaryAbelian 2 (A.subgroupOf V) := IsElementaryAbelian.subgroupOf ((middle_le_five Q split i j).trans
    (middleFive_le_remainder Q split hm i j hij))
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.normalClosure_of_isMulCommutative _
  exact IsElementaryAbelian.map V.subtype

private theorem orbit_index_lt_card {Y : Type*} [Group Y] [Finite Y]
    (A E : Subgroup Y) [E.Normal] (hAE : A ≤ E) (hA : Nat.card A = 2) :
    (centralizer (A : Set Y)).index < Nat.card E := by
  obtain ⟨a,ha,hau⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have hane : (a : Y) ≠ 1 := fun he => ha (Subtype.ext he)
  have hcentral : centralizer (A : Set Y) = centralizer ({(a : Y)} : Set Y) := by
    apply le_antisymm (centralizer_le (Set.singleton_subset_iff.mpr a.property))
    intro c hc
    apply mem_centralizer_iff.mpr
    intro x hx
    by_cases he : x = 1
    · simp only [he,one_mul,mul_one]
    · have hx' : (⟨x,hx⟩ : A) = a := hau _ (fun hh => he (congrArg Subtype.val hh))
      rw [show x = (a : Y) from congrArg Subtype.val hx']
      exact mem_centralizer_iff.mp hc _ (Set.mem_singleton _)
  let O := MulAction.orbit (ConjAct Y) (a : Y)
  let f : O → {z : E // z ≠ 1} := fun z => ⟨⟨z,by
    obtain ⟨g,hg⟩ := z.property
    rw [←hg]
    exact Subgroup.Normal.conj_mem (inferInstance : E.Normal) _ (hAE a.property) (ConjAct.ofConjAct g)⟩,by
      intro hz
      have hz1 : (z : Y) = 1 := congrArg (fun t : E => (t : Y)) hz
      obtain ⟨g,hg⟩ := z.property
      have hh : MulAut.conj (ConjAct.ofConjAct g) (a : Y) = 1 := by
        exact hg.trans hz1
      exact hane ((MulAut.conj _).injective (hh.trans (map_one _).symm))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : {z : E // z ≠ 1} => (z.val : Y)) hxy)
  have hstab : Nat.card (centralizer ({(a : Y)} : Set Y)) =
      Nat.card (MulAction.stabilizer (ConjAct Y) (a : Y)) := by
    rw [centralizer_eq_comap_stabilizer]
    rfl
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct Y) (a : Y))
  rw [Nat.card_prod,←hstab] at hc
  have hi := (centralizer ({(a : Y)} : Set Y)).index_mul_card
  have heq : (centralizer (A : Set Y)).index = Nat.card O := by
    rw [hcentral]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := centralizer ({(a : Y)} : Set Y)))
      (hi.trans hc.symm)
  rw [heq]
  apply lt_of_le_of_lt (Nat.card_le_card_of_injective f hf)
  let := Fintype.ofFinite E
  let := Fintype.ofFinite {z : E // z ≠ 1}
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_subtype_lt (p := fun z : E => z ≠ 1) (x := 1) (by simp))

/-- The nonidentity conjugacy orbit has exactly the centralizer index, so
that index is strictly smaller than the elementary normal closure. -/
theorem binary_middleRootClosure_card_gt_index (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nat.card (simpleRoot Q split i) = 2) :
    (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) <
      Nat.card (middleRootClosure Q split i j) := by
  let V := simpleRemainder Q split i
  let A := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let N := normalClosure (A.subgroupOf V : Set V)
  have hAV : A ≤ V := (middle_le_five Q split i j).trans
    (middleFive_le_remainder Q split hm i j hij)
  have hA : Nat.card (A.subgroupOf V) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAV).toEquiv]
    simpa only [A,rootAt,card_rightConjugate] using hi
  have hC : centralizer (A.subgroupOf V : Set V) =
      (middleRootCentralizer Q split i j).subgroupOf V := by
    ext v
    change (∀ a : V, a ∈ A.subgroupOf V → a*v = v*a) ↔
      (v : X ⧸ Q.D) ∈ V ∧ (v : X ⧸ Q.D) ∈ centralizer (A : Set (X ⧸ Q.D))
    constructor
    · intro hv
      refine ⟨v.property,mem_centralizer_iff.mpr ?_⟩
      intro a ha
      exact congrArg Subtype.val (hv ⟨a,hAV ha⟩ ha)
    · intro hv a ha
      exact Subtype.ext (mem_centralizer_iff.mp hv.2 _ ha)
  have hh := orbit_index_lt_card (A.subgroupOf V) N le_normalClosure hA
  rw [hC] at hh
  change ((middleRootCentralizer Q split i j).subgroupOf V).index < _
  have he : Nat.card N = Nat.card (middleRootClosure Q split i j) :=
    Nat.card_congr (equivMapOfInjective N V.subtype V.subtype_injective).toEquiv
  rwa [←he]

/-- The quotient by the middle-root centralizer acts faithfully on the
actual normal closure, with the literal conjugation formula. -/
theorem middleRootClosure_faithful_action (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hn : ((middleRootCentralizer Q split i j).subgroupOf
      (simpleRemainder Q split i)).Normal) :
    letI := hn
    ∃ φ : ((simpleRemainder Q split i) ⧸
        (middleRootCentralizer Q split i j).subgroupOf (simpleRemainder Q split i)) →*
          MulAut (middleRootClosure Q split i j),
      Function.Injective φ ∧
      ∀ (v : simpleRemainder Q split i) (z : middleRootClosure Q split i j),
        (φ (QuotientGroup.mk v) z : X ⧸ Q.D) =
          (v : X ⧸ Q.D)*(z : X ⧸ Q.D)*(v : X ⧸ Q.D)⁻¹ := by
  let := hn
  let V := simpleRemainder Q split i
  let E := middleRootClosure Q split i j
  let C := (middleRootCentralizer Q split i j).subgroupOf V
  let ψ : V →* MulAut E := E.normalizerMonoidHom.comp
    (inclusion (middleRootClosure_normalized Q split i j))
  have hnorm : V ≤ normalizer (middleRootCentralizer Q split i j : Set (X ⧸ Q.D)) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn
  have hcent := middleRootClosure_centralizer Q split hm i j hij hnorm
  have hker : ψ.ker = C := by
    ext v
    change ψ v = 1 ↔ (v : X ⧸ Q.D) ∈ middleRootCentralizer Q split i j
    rw [←hcent]
    constructor
    · intro hv
      refine ⟨v.property,mem_centralizer_iff.mpr ?_⟩
      intro z hz
      have he := congrArg (fun f : MulAut E => (f ⟨z,hz⟩ : X ⧸ Q.D)) hv
      change (v : X ⧸ Q.D)*z*(v : X ⧸ Q.D)⁻¹ = z at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hv
      ext z
      change (v : X ⧸ Q.D)*(z : X ⧸ Q.D)*(v : X ⧸ Q.D)⁻¹ = z
      rw [←mem_centralizer_iff.mp hv.2 _ z.property,mul_inv_cancel_right]
  let φ := QuotientGroup.lift C ψ (fun v hv => MonoidHom.mem_ker.mp (hker ▸ hv))
  refine ⟨φ,?_,fun v z => rfl⟩
  exact (QuotientGroup.injective_lift_iff C ψ hker.ge).mpr hker.symm

/-- In the two noncentral cases the actual elementary normal subgroup has
order at least eight or thirty-two, and its order divides 128. -/
theorem binary_middleRootClosure_card_bounds (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (hJC : middleFive Q split i j ≤ middleRootCentralizer Q split i j) :
    Nat.card (middleRootClosure Q split i j) ∣ 128 ∧
    ((middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 4 →
      8 ≤ Nat.card (middleRootClosure Q split i j)) ∧
    ((middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 16 →
      32 ≤ Nat.card (middleRootClosure Q split i j)) := by
  have hle := (middleRootClosure_le_middle_center Q split hm i j hij hKj hJC).trans inf_le_left
  have hd := card_dvd_of_le hle
  have hc : Nat.card (middleFive Q split i j) = 128 := by
    rw [middleFive_card Q split hm i j hij,hi,hj]
    norm_num
  rw [hc] at hd
  refine ⟨hd,?_,?_⟩
  all_goals
    intro hindex
    have hb := binary_middleRootClosure_card_gt_index Q split hm i j hij hi
    rw [hindex] at hb
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show Nat.card (middleRootClosure Q split i j) ∣ 2^7 from hd)
    rw [he] at hb ⊢
    interval_cases k <;> norm_num at *

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
