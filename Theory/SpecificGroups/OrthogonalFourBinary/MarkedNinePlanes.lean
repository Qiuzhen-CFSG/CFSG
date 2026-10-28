module
public import Theory.SpecificGroups.OrthogonalFourBinary.MarkedNineMovement
public import Theory.Representation.CyclicFixedRank
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import Theory.GroupTheory.PResidual.Quotient
/-!
# The two marked planes of the elementary-nine actor

The literal two-residual of an order-six point stabilizer is cyclic of order
three. Its fixed and moved spaces are complementary binary planes. The
72-isometry coordinate model proves that every order-four isometry exchanges
these planes and acts nontrivially on each plane through its square.

Consequently, the point stabilizer inside the prescribed cyclic-four subgroup
has order two, preserves both planes, and acts faithfully on the fixed plane.
The existing marked-vector witness retains its generation, Sylow intersection
and fixed-seed displacement bound together with this plane geometry.

Source: Aschbacher--Smith, Notation 15.1.16(b), and the elementary-nine uses in
15.1.24(3--4) and 15.1.25(4,6), printed pp.1092, 1101--1102. The cyclic-four
subgroup here is the image of the source `T`; its marked point stabilizer is
the image of the source `S = C_T(Z1)`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace OrthogonalFourBinary.MarkedNine
open TerminalLines SylowGeometry
set_option synthInstance.maxSize 10000

private theorem residual_six {K : Type*} [Group K] [Finite K]
    (hc : Nat.card K = 6) (a : K) (ha : orderOf a = 3) :
    pResidual 2 K = zpowers a := by
  have hca : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers,ha]
  have hi : (zpowers a).index = 2 := by
    have hh := (zpowers a).index_mul_card
    rw [hca,hc] at hh
    omega
  let _ := normal_of_index_eq_two hi
  apply le_antisymm
  · apply (pResidual_le_iff_isPGroup_quotient 2 (zpowers a)).mpr
    exact IsPGroup.of_card (n := 1) (by rw [pow_one, ← Subgroup.index_eq_card]; exact hi)
  · apply zpowers_le.mpr
    apply mem_pResidual_of_orderOf_coprime
    rw [ha]
    decide

private theorem rotation_eval : ∀ i : RotationCode, ∀ v : Space,
    rotation i v = rotEval i v := by decide +kernel

private def AxisRotation (i : RotationCode) : Prop :=
  i ≠ 1 ∧ (i.toAdd.1 = 0 ∨ i.toAdd.2 = 0)
private instance (i : RotationCode) : Decidable (AxisRotation i) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem axis_of_fixed : ∀ i : RotationCode, i ≠ 1 → ∀ z : Space,
    z ≠ 0 → rotEval i z = z → AxisRotation i := by decide +kernel
private theorem fixed_card : ∀ i : RotationCode, AxisRotation i →
    Fintype.card {v : Space // rotEval i v = v} = 4 := by decide +kernel

private def b0 : Space := ((1,0),(0,0))
private def b1 : Space := ((0,1),(0,0))
private def b2 : Space := ((0,0),(1,0))
private def b3 : Space := ((0,0),(0,1))
private def samples (f : Space → Space) := (f b0,f b1,f b2,f b3)
private theorem samples_injective (e f : Space ≃ₗ[F] Space)
    (h : samples e = samples f) : e = f := by
  have h0 := congrArg (fun x => x.1) h
  have h1 := congrArg (fun x => x.2.1) h
  have h2 := congrArg (fun x => x.2.2.1) h
  have h3 := congrArg (fun x => x.2.2.2) h
  apply LinearEquiv.ext
  intro w
  have hw : w = w.1.1 • b0 + w.1.2 • b1 + w.2.1 • b2 + w.2.2 • b3 := by
    exact (show ∀ w : Space,
      w = w.1.1 • b0 + w.1.2 • b1 + w.2.1 • b2 + w.2.2 • b3 by decide +kernel) w
  rw [hw]
  change e _ = f _
  simp only [map_add,map_smul]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg (w.1.1 • ·) h0) (congrArg (w.1.2 • ·) h1))
    (congrArg (w.2.1 • ·) h2)) (congrArg (w.2.2 • ·) h3)
private def FourCode (k : Code) : Prop :=
  samples (fun v => eval k (eval k (eval k (eval k v)))) = samples id ∧
    samples (fun v => eval k (eval k v)) ≠ samples id
private instance (k : Code) : Decidable (FourCode k) :=
  inferInstanceAs (Decidable (_ ∧ _))
private theorem fourCode_of_order (k : Code) (h : orderOf (codeMap k) = 4) : FourCode k := by
  constructor
  · have hh : codeMap k ^ 4 = 1 := h ▸ pow_orderOf_eq_one (codeMap k)
    have hv := congrArg (fun a : IsometryGroup => samples a.val) hh
    change samples (fun v => candidate k (candidate k (candidate k (candidate k v)))) = samples id at hv
    simpa only [candidate_eval] using hv
  · intro he
    have hh : codeMap k ^ 2 = 1 := by
      apply Subtype.ext
      apply samples_injective
      change samples (fun v => candidate k (candidate k v)) = samples id
      simpa only [candidate_eval] using he
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [h] at hd
    norm_num at hd

set_option maxRecDepth 10000 in
private theorem finite_exchange : ∀ k : Code, FourCode k →
    ∀ i : RotationCode, AxisRotation i → ∀ v : Space,
    (rotEval i v = v ↔ ∃ w : Space, rotEval i w - w = eval k v) ∧
    ((∃ w : Space, rotEval i w - w = v) ↔ rotEval i (eval k v) = eval k v) := by
  decide +kernel
private theorem finite_square_nontrivial : ∀ k : Code, FourCode k →
    ∀ i : RotationCode, AxisRotation i →
    ∃ v : Space, rotEval i v = v ∧ eval k (eval k v) ≠ v := by decide +kernel

private theorem cubic_model {D : Type*} [Group D]
    (f : D →* IsometryGroup) (a : D) (ha : orderOf (f a) = 3)
    (z : Space) (hz : z ≠ 0) (haz : (f a).val z = z) :
    Module.finrank F (fixedSpace (naturalRepresentation.comp f) (zpowers a)) = 2 := by
  have harot : f a ∈ rotations := by
    rw [← residual_eq_rotations]
    apply mem_pResidual_of_orderOf_coprime
    rw [ha]
    decide
  obtain ⟨i,hi⟩ := harot
  have hine : i ≠ 1 := by intro he; simp [←hi,he] at ha
  have hiz : rotEval i z = z := by
    rw [←hi] at haz
    change rotation i z = z at haz
    simpa only [rotation_eval] using haz
  have haxis := axis_of_fixed i hine z hz hiz
  have hc : Nat.card (fixedSpace (naturalRepresentation.comp f) (zpowers a)) = 4 := by
    let e : fixedSpace (naturalRepresentation.comp f) (zpowers a) ≃
        {v : Space // rotEval i v = v} :=
      (Equiv.refl Space).subtypeEquiv (fun v => by
        rw [mem_fixedSpace_zpowers_iff]
        change (f a).val v = v ↔ _
        rw [←hi]
        change rotation i v = v ↔ _
        rw [rotation_eval]
        rfl)
    rw [Nat.card_congr e,Nat.card_eq_fintype_card]
    exact fixed_card i haxis
  have hp := Module.natCard_eq_pow_finrank (K := F)
    (V := fixedSpace (naturalRepresentation.comp f) (zpowers a))
  rw [show Nat.card F = 2 by exact Nat.card_zmod _,hc] at hp
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hp.symm

private theorem cubic_exchange {D : Type*} [Group D]
    (f : D →* IsometryGroup) (a : D) (ha : orderOf (f a) = 3)
    (z : Space) (hz : z ≠ 0) (haz : (f a).val z = z)
    (r : D) (hr : orderOf (f r) = 4) :
    let W1 := fixedSpace (naturalRepresentation.comp f) (zpowers a)
    let W2 := subspaceCommutator (naturalRepresentation.comp f) ⊤ (zpowers a)
    (∀ v : Space, (f r).val v ∈ W2 ↔ v ∈ W1) ∧
    (∀ v : Space, (f r).val v ∈ W1 ↔ v ∈ W2) ∧
    ∃ v : Space, v ∈ W1 ∧ (f (r ^ 2)).val v ≠ v := by
  have harot : f a ∈ rotations := by
    rw [← residual_eq_rotations]
    apply mem_pResidual_of_orderOf_coprime
    rw [ha]
    decide
  obtain ⟨i,hi⟩ := harot
  have hine : i ≠ 1 := by intro he; simp [←hi,he] at ha
  have hiz : rotEval i z = z := by
    rw [←hi] at haz
    change rotation i z = z at haz
    simpa only [rotation_eval] using haz
  have haxis := axis_of_fixed i hine z hz hiz
  obtain ⟨k,hk⟩ := codeMap_bijective.surjective (f r)
  have hk4 : FourCode k := fourCode_of_order k (hk.symm ▸ hr)
  have hfixed (v : Space) :
      v ∈ fixedSpace (naturalRepresentation.comp f) (zpowers a) ↔ rotEval i v = v := by
    rw [mem_fixedSpace_zpowers_iff]
    change (f a).val v = v ↔ _
    rw [←hi]
    change rotation i v = v ↔ _
    rw [rotation_eval]
  have hmoved (v : Space) :
      v ∈ subspaceCommutator (naturalRepresentation.comp f) ⊤ (zpowers a) ↔
        ∃ w : Space, rotEval i w - w = v := by
    rw [Representation.CyclicFixedRank.commutator_eq_range]
    change (∃ w, (f a).val w - w = v) ↔ _
    rw [←hi]
    change (∃ w, rotation i w - w = v) ↔ _
    simp only [rotation_eval]
  have hact (v : Space) : (f r).val v = eval k v := by
    rw [←hk]
    exact candidate_eval k v
  refine ⟨?_,?_,?_⟩
  · intro v
    rw [hmoved,hact,hfixed]
    exact (finite_exchange k hk4 i haxis v).1.symm
  · intro v
    rw [hfixed,hact,hmoved]
    exact (finite_exchange k hk4 i haxis v).2.symm
  · obtain ⟨v,hv,hne⟩ := finite_square_nontrivial k hk4 i haxis
    refine ⟨v,(hfixed v).mpr hv,?_⟩
    rw [map_pow]
    change (f r).val ((f r).val v) ≠ v
    simpa only [hact] using hne

/-- The two-residual of the original order-six point stabilizer is cubic;
its fixed and moved spaces are complementary binary planes. -/
theorem pointStabilizer_residual_planes {D : Type*} [Group D] [Finite D]
    (f : D →* IsometryGroup) (hf : Function.Injective f)
    (z : Space) (hz : z ≠ 0) (hK : Nat.card (pointStabilizer f z) = 6) :
    let R := (pResidual 2 (pointStabilizer f z)).map (pointStabilizer f z).subtype
    let W1 := fixedSpace (naturalRepresentation.comp f) R
    let W2 := subspaceCommutator (naturalRepresentation.comp f) ⊤ R
    Nat.card R = 3 ∧ Module.finrank F W1 = 2 ∧ Module.finrank F W2 = 2 ∧
      IsCompl W1 W2 ∧ z ∈ W1 ∧
      subspaceCommutator (naturalRepresentation.comp f) W2 R = W2 ∧
      ∀ r : D, orderOf (f r) = 4 →
        (∀ v : Space, (f r).val v ∈ W2 ↔ v ∈ W1) ∧
        (∀ v : Space, (f r).val v ∈ W1 ↔ v ∈ W2) ∧
        ∃ v : Space, v ∈ W1 ∧ (f (r ^ 2)).val v ≠ v := by
  let K := pointStabilizer f z
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hK]; decide)
  have hres : (pResidual 2 K).map K.subtype = zpowers (a : D) := by
    rw [residual_six hK a ha]
    exact K.subtype.map_zpowers a
  dsimp only
  change Nat.card ((pResidual 2 K).map K.subtype) = 3 ∧ _
  rw [hres]
  have hac : orderOf (a : D) = 3 := (Subgroup.orderOf_coe a).trans ha
  have haf : orderOf (f (a : D)) = 3 := (orderOf_injective f hf _).trans hac
  have hcard : Nat.card (zpowers (a : D)) = 3 := by rw [Nat.card_zpowers,hac]
  have hodd : Odd (Nat.card (zpowers (a : D))) := by rw [hcard]; decide
  have hc : IsCompl (fixedSpace (naturalRepresentation.comp f) (zpowers (a : D)))
      (subspaceCommutator (naturalRepresentation.comp f) ⊤ (zpowers (a : D))) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd
        (ρ := naturalRepresentation.comp f) hodd)
  have hdim := cubic_model f (a : D) haf z hz a.property
  have hdim2 : Module.finrank F
      (subspaceCommutator (naturalRepresentation.comp f) ⊤ (zpowers (a : D))) = 2 := by
    have hd := Submodule.finrank_add_eq_of_isCompl hc
    have hall : Module.finrank F Space = 4 := by simp [Space,Plane,F]
    rw [hdim,hall] at hd
    change Module.finrank (ZMod 2) _ = 2
    omega
  exact ⟨hcard,hdim,hdim2,hc,
    (mem_fixedSpace_zpowers_iff _ _ _).mpr a.property,
    NormalOddSeed.odd_moved_self _ _ hodd,
    fun r hr => cubic_exchange f (a : D) haf z hz a.property r hr⟩

private theorem members_of_order_two {D : Type*} [Group D] [Finite D]
    (b : D) (hb : orderOf b = 2) {a : D} (ha : a ∈ zpowers b) :
    a = 1 ∨ a = b := by
  classical
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ha)
  have hn2 : n < 2 := by simpa [hb] using Finset.mem_range.mp hn
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

/-- The order-two point stabilizer in the cyclic-four actor preserves both
planes and has faithful action on the fixed plane. Every remaining cyclic-four
actor exchanges the two planes. This order-two subgroup is the image of the
source subgroup `C_T(Z1)`, as distinct from the whole cyclic-four image of `T`. -/
theorem marked_vector_plane_action {D : Type*} [Group D] [Finite D]
    (f : D →* IsometryGroup) (hf : Function.Injective f)
    (S : Subgroup D) [IsCyclic S] (hS : Nat.card S = 4)
    (z : Space) (hz : z ≠ 0)
    (hfix : ∀ a ∈ S, a ^ 2 = 1 → (f a).val z = z)
    (hK : Nat.card (pointStabilizer f z) = 6) :
    let R := (pResidual 2 (pointStabilizer f z)).map (pointStabilizer f z).subtype
    let W1 := fixedSpace (naturalRepresentation.comp f) R
    let W2 := subspaceCommutator (naturalRepresentation.comp f) ⊤ R
    let H := S ⊓ pointStabilizer f z
    Nat.card H = 2 ∧ H.relIndex S = 2 ∧
      H ≤ subspaceStabilizer (naturalRepresentation.comp f) W1 ∧
      H ≤ subspaceStabilizer (naturalRepresentation.comp f) W2 ∧
      subspaceKernel (naturalRepresentation.comp f) W1 H = ⊥ ∧
      (subspaceKernel (naturalRepresentation.comp f) W1 H).relIndex H = 2 ∧
      ∀ t ∈ S, t ∉ H →
        W1.map ((naturalRepresentation.comp f) t) = W2 ∧
        W2.map ((naturalRepresentation.comp f) t) = W1 := by
  classical
  let ρ := naturalRepresentation.comp f
  let K := pointStabilizer f z
  let R := (pResidual 2 K).map K.subtype
  let W1 := fixedSpace ρ R
  let W2 := subspaceCommutator ρ ⊤ R
  let H := S ⊓ K
  change Nat.card H = 2 ∧ H.relIndex S = 2 ∧
    H ≤ subspaceStabilizer ρ W1 ∧ H ≤ subspaceStabilizer ρ W2 ∧
    subspaceKernel ρ W1 H = ⊥ ∧ (subspaceKernel ρ W1 H).relIndex H = 2 ∧ _
  obtain ⟨r,hrgen⟩ := IsCyclic.exists_generator (α := S)
  have hr : orderOf (r : D) = 4 := (Subgroup.orderOf_coe r).trans
    ((orderOf_eq_card_of_forall_mem_zpowers hrgen).trans hS)
  have hr4 : (r : D) ^ 4 = 1 := hr ▸ pow_orderOf_eq_one (r : D)
  have hr2 : orderOf ((r : D)^2) = 2 := by norm_num [orderOf_pow,hr]
  have hr2H : (r : D)^2 ∈ H := by
    refine ⟨S.pow_mem r.property 2,?_⟩
    exact hfix _ (S.pow_mem r.property 2) (by simpa only [←pow_mul] using hr4)
  have hHcard : Nat.card H = 2 := by
    have h4 : Nat.card H ∣ 4 := by simpa [hS] using card_dvd_of_le (show H ≤ S from inf_le_left)
    have h6 : Nat.card H ∣ 6 := by simpa [K,hK] using card_dvd_of_le (show H ≤ K from inf_le_right)
    have h2 : 2 ∣ Nat.card H := by
      have hh := card_dvd_of_le (zpowers_le.mpr hr2H)
      simpa only [Nat.card_zpowers,hr2] using hh
    have hh := Nat.dvd_gcd h4 h6
    norm_num at hh
    exact Nat.dvd_antisymm hh h2
  have hHeq : zpowers ((r : D)^2) = H := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hr2H)
    rw [hHcard,Nat.card_zpowers,hr2]
  have hHindex : H.relIndex S = 2 := by
    have hcH : Nat.card (H.subgroupOf S) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe (show H ≤ S from inf_le_left)).toEquiv).trans hHcard
    have hh := (H.subgroupOf S).index_mul_card
    rw [hcH,hS] at hh
    change (H.subgroupOf S).index = 2
    omega
  have hex := (pointStabilizer_residual_planes f hf z hz hK).2.2.2.2.2.2 (r : D)
    ((orderOf_injective f hf _).trans hr)
  have hW1sq (v : Space) : ρ ((r : D)^2) v ∈ W1 ↔ v ∈ W1 := by
    change (f ((r : D)^2)).val v ∈ W1 ↔ _
    rw [map_pow]
    exact (hex.2.1 ((f r).val v)).trans (hex.1 v)
  have hW2sq (v : Space) : ρ ((r : D)^2) v ∈ W2 ↔ v ∈ W2 := by
    change (f ((r : D)^2)).val v ∈ W2 ↔ _
    rw [map_pow]
    exact (hex.1 ((f r).val v)).trans (hex.2.1 v)
  have hHmembers (a : D) (ha : a ∈ H) : a = 1 ∨ a = (r : D)^2 :=
    members_of_order_two _ hr2 (hHeq.symm ▸ ha)
  have hkbot : subspaceKernel ρ W1 H = ⊥ := by
    apply bot_unique
    intro a ha
    rcases hHmembers a ha.1 with rfl | rfl
    · exact mem_bot.mpr rfl
    · obtain ⟨v,hv,hne⟩ := hex.2.2
      exact (hne (ha.2 v hv)).elim
  refine ⟨hHcard,hHindex,?_,?_,hkbot,?_,?_⟩
  · intro a ha v
    rcases hHmembers a ha with rfl | rfl
    · simp
    · exact hW1sq v
  · intro a ha v
    rcases hHmembers a ha with rfl | rfl
    · simp
    · exact hW2sq v
  · rw [hkbot,relIndex_bot_left,hHcard]
  · intro t ht htH
    have ht4 : orderOf t = 4 := by
      have hd : orderOf t ∣ 4 := by
        rw [Subgroup.orderOf_coe (⟨t,ht⟩ : S), ← hS]
        exact orderOf_dvd_natCard (⟨t,ht⟩ : S)
      have hd' : orderOf t = 1 ∨ orderOf t = 2 ∨ orderOf t = 4 := by
        have hd2 : orderOf t ∣ 2 ^ 2 := hd
        have hm := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd2
        obtain ⟨k,hk,hke⟩ := hm
        interval_cases k <;> simp_all
      rcases hd' with h1 | h2 | h4
      · exfalso
        apply htH
        have ht1 := orderOf_eq_one_iff.mp h1
        subst t
        exact H.one_mem
      · exfalso
        exact htH ⟨ht,hfix t ht (h2 ▸ pow_orderOf_eq_one t)⟩
      · exact h4
    have hext := (pointStabilizer_residual_planes f hf z hz hK).2.2.2.2.2.2 t
      ((orderOf_injective f hf _).trans ht4)
    constructor
    · ext v
      obtain ⟨w,rfl⟩ := (f t).val.surjective v
      constructor
      · rintro ⟨u,hu,he⟩
        have huw : u = w := (f t).val.injective he
        exact (hext.1 w).mpr (huw ▸ hu)
      · intro hv
        exact ⟨w,(hext.1 w).mp hv,rfl⟩
    · ext v
      obtain ⟨w,rfl⟩ := (f t).val.surjective v
      constructor
      · rintro ⟨u,hu,he⟩
        have huw : u = w := (f t).val.injective he
        exact (hext.2.1 w).mpr (huw ▸ hu)
      · intro hv
        exact ⟨w,(hext.2.1 w).mp hv,rfl⟩

/-- The original marked-vector witness together with its literal residual
planes and the faithful action of the order-two point stabilizer. -/
theorem exists_marked_vector_with_planes {D : Type*} [Group D] [Finite D]
    (f : D →* IsometryGroup) (hf : Function.Injective f) (hc : Nat.card D = 36)
    (S : Subgroup D) [IsCyclic S] (hS : Nat.card S = 4) :
    ∃ z : Space, z ≠ 0 ∧
      (∀ a ∈ S, a ^ 2 = 1 → (f a).val z = z) ∧
      pointStabilizer f z ⊔ S = ⊤ ∧
      Nat.card (pointStabilizer f z) = 6 ∧
      (∃ P : Sylow 2 (pointStabilizer f z),
        (P : Subgroup (pointStabilizer f z)).map (pointStabilizer f z).subtype =
          S ⊓ pointStabilizer f z) ∧
      let R := (pResidual 2 (pointStabilizer f z)).map (pointStabilizer f z).subtype
      let W1 := fixedSpace (naturalRepresentation.comp f) R
      let W2 := subspaceCommutator (naturalRepresentation.comp f) ⊤ R
      let H := S ⊓ pointStabilizer f z
      fixedSpace (naturalRepresentation.comp f) S ≤ Submodule.span F {z} ⊔ W2 ∧
      Nat.card R = 3 ∧ Module.finrank F W1 = 2 ∧ Module.finrank F W2 = 2 ∧
      IsCompl W1 W2 ∧ z ∈ W1 ∧
      subspaceCommutator (naturalRepresentation.comp f) W2 R = W2 ∧
      Nat.card H = 2 ∧ H.relIndex S = 2 ∧
      H ≤ subspaceStabilizer (naturalRepresentation.comp f) W1 ∧
      H ≤ subspaceStabilizer (naturalRepresentation.comp f) W2 ∧
      subspaceKernel (naturalRepresentation.comp f) W1 H = ⊥ ∧
      (subspaceKernel (naturalRepresentation.comp f) W1 H).relIndex H = 2 ∧
      ∀ t ∈ S, t ∉ H →
        W1.map ((naturalRepresentation.comp f) t) = W2 ∧
        W2.map ((naturalRepresentation.comp f) t) = W1 := by
  obtain ⟨z,hz,hfix,hgen,hK,hSyl,hmoved⟩ := exists_marked_vector_with_movement f hf hc S hS
  obtain ⟨hR,hW1,hW2,hcompl,hzW1,hself,_⟩ := pointStabilizer_residual_planes f hf z hz hK
  exact ⟨z,hz,hfix,hgen,hK,hSyl,hmoved,hR,hW1,hW2,hcompl,hzW1,hself,
    marked_vector_plane_action f hf S hS z hz hfix hK⟩

end OrthogonalFourBinary.MarkedNine
