module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanKernels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.RootActors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootReflections

/-!
# Joint Cartan kernels on the same finite marked quotient

Earlier source root-reflection markings put a lift of each simple class
inside its actual root-generated rank-one subgroup. Ordered positive
products then prove that the two rank-one groups and H generate the
whole quotient. Thus their common Cartan kernel is central; faithfulness
of the full Borel kills it. Projection embeds H in the product of its
two actual faithful-panel images, giving the product-order divisibility
used in (6H)(a). No field parameters or torus-order equalities are assumed.

Raising a root reflection to the odd order of H constructs an involutory
lift in the same rank-one subgroup, preserving its Weyl class. The input
RootReflection is the earlier choice following Fong–Seitz I (5C), p.26;
its existence remains with the earlier rank-one source construction.
The joint-kernel and product-order argument is I (6H)(a), p.51.
The original/geometric marked application is in OriginalCartan.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Source (5C)'s root-group reflection marking, shared with the other source rows. -/
abbrev RootReflection (i : Fin 2) := HexagonStructure.RootReflection Q split i

private theorem normalizer_le_of_cartan_lifts (n : Fin 2 → Q.tits.N)
    (hn : ∀ i, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (n i) = Q.simple i)
    (A : Subgroup (X ⧸ Q.D)) (hH : Q.tits.B ⊓ Q.tits.N ≤ A)
    (hA : ∀ i, (n i : X ⧸ Q.D) ∈ A) : Q.tits.N ≤ A := by
  intro g hg
  let gN : Q.tits.N := ⟨g,hg⟩
  let q := QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
  obtain ⟨k,hk,hqk⟩ := UnitarySource.exists_weyl_lift_in Q n hn A hA (q gN)
  have hdiff : gN*k⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (gN*k⁻¹) = 1
    rw [map_mul, map_inv, hqk, mul_inv_cancel]
  have hz := A.mul_mem (hH hdiff) hk
  change (g*(k : X ⧸ Q.D)⁻¹)*(k : X ⧸ Q.D) ∈ A at hz
  simpa only [inv_mul_cancel_right] using hz

/-- Ordered positive roots and the two actual root-group reflections generate with H. -/
theorem rankOne_pair_sup_cartan (s : ∀ i, RootReflection Q split i) :
    (rankOneRootGroup Q split 0 ⊔ rankOneRootGroup Q split 1) ⊔
      (Q.tits.B ⊓ Q.tits.N) = ⊤ := by
  let A := (rankOneRootGroup Q split 0 ⊔ rankOneRootGroup Q split 1) ⊔
    (Q.tits.B ⊓ Q.tits.N)
  have hRi (i : Fin 2) : rankOneRootGroup Q split i ≤ A := by
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hN : Q.tits.N ≤ A := normalizer_le_of_cartan_lifts Q
    (fun i => (s i).val) (fun i => (s i).class_eq) A le_sup_right
    (fun i => hRi i (s i).mem_rankOne)
  have hU : split.U ≤ A := by
    apply RootGeneration.unipotent_le_of_orderedRoots_le Q split A false
    intro R hR
    obtain ⟨i,n,rfl⟩ := orderedRoots_are_simple_conjugates Q split false _ R hR
    intro x hx
    have hr : simpleRoot Q split i ≤ A := le_sup_left.trans (hRi i)
    have ht := A.mul_mem (A.mul_mem (A.inv_mem (hN n.property)) (hr hx)) (hN n.property)
    change (n : X ⧸ Q.D)⁻¹*((n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹)*(n : X ⧸ Q.D) ∈ A at ht
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using ht
  have hB : Q.tits.B ≤ A := by
    rw [← split.factorization]
    exact sup_le hU le_sup_right
  apply top_unique
  rw [← Q.tits.generate]
  exact (closure_le _).mpr (Set.union_subset hB hN)

/-- The common Cartan kernel lies in the ambient center, before faithfulness is used. -/
theorem joint_cartan_kernel_le_center (s : ∀ i, RootReflection Q split i) :
    (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q 0 ⊓ embeddedPanelKernel Q 1 ≤
      center (X ⧸ Q.D) := by
  let := split.abelian
  intro h hh
  have hC (i : Fin 2) : h ∈ centralizer (rankOneRootGroup Q split i : Set (X ⧸ Q.D)) := by
    have hk : h ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q i := by
      fin_cases i
      · exact hh.1
      · exact ⟨hh.1.1,hh.2⟩
    rw [← cartan_centralizer_rankOneRootGroup Q split i] at hk
    exact hk.2
  have hcentral (A : Subgroup (X ⧸ Q.D))
      (hA : h ∈ centralizer (A : Set (X ⧸ Q.D))) : A ≤ centralizer ({h} : Set (X ⧸ Q.D)) := by
    intro x hx
    rw [mem_centralizer_iff]
    rintro y rfl
    exact ((mem_centralizer_iff.mp hA) x hx).symm
  have hH : Q.tits.B ⊓ Q.tits.N ≤ centralizer ({h} : Set (X ⧸ Q.D)) :=
    hcentral _ (Subgroup.le_centralizer _ hh.1.1)
  have ht : (⊤ : Subgroup (X ⧸ Q.D)) ≤ centralizer ({h} : Set (X ⧸ Q.D)) := by
    rw [← rankOne_pair_sup_cartan Q split s]
    exact sup_le (sup_le (hcentral _ (hC 0)) (hcentral _ (hC 1))) hH
  rw [Subgroup.mem_center_iff]
  intro x
  exact ((mem_centralizer_iff.mp (ht (mem_top x))) h (Set.mem_singleton h)).symm

/-- Faithfulness of the entire Borel removes the joint Cartan kernel. -/
theorem joint_cartan_kernel_eq_bot (s : ∀ i, RootReflection Q split i)
    (hcore : Q.tits.B.normalCore = ⊥) :
    (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q 0 ⊓ embeddedPanelKernel Q 1 = ⊥ := by
  apply eq_bot_iff.mpr
  exact (joint_cartan_kernel_le_center Q split s).trans
    (split.center_eq_bot_of_borel_core hcore).le

/-- Both natural faithful-panel quotients retain the same Cartan elements. -/
def cartanPanelMap (i : Fin 2) :
    (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →* (Endpoint Q i ⧸ panelKernel Q i) :=
  (QuotientGroup.mk' (panelKernel Q i)).comp
    (inclusion (inf_le_left.trans (Q.tits.B_le_standardParabolic _)))

@[simp] theorem cartanPanelMap_apply (i : Fin 2)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    cartanPanelMap Q i h = QuotientGroup.mk' (panelKernel Q i)
      ⟨h,Q.tits.B_le_standardParabolic _ h.property.1⟩ := rfl

theorem cartanPanelMap_kernel (i : Fin 2) :
    (cartanPanelMap Q i).ker = (embeddedPanelKernel Q i).subgroupOf (Q.tits.B ⊓ Q.tits.N) := by
  ext h
  change (QuotientGroup.mk (⟨h,Q.tits.B_le_standardParabolic _ h.property.1⟩ : Endpoint Q i) = 1) ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hh
    exact ⟨⟨h,Q.tits.B_le_standardParabolic _ h.property.1⟩,hh,rfl⟩
  · rintro ⟨y,hy,he⟩
    have hye : y = ⟨h,Q.tits.B_le_standardParabolic _ h.property.1⟩ := Subtype.ext he
    rwa [hye] at hy

/-- The injection used for the product-order bound in (6H)(a). -/
theorem cartanPanelPair_injective (s : ∀ i, RootReflection Q split i)
    (hcore : Q.tits.B.normalCore = ⊥) :
    Function.Injective ((cartanPanelMap Q 0).prod (cartanPanelMap Q 1)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro h hh
  have hzero : cartanPanelMap Q 0 h = 1 := congrArg Prod.fst hh
  have hone : cartanPanelMap Q 1 h = 1 := congrArg Prod.snd hh
  have h0 : (h : X ⧸ Q.D) ∈ embeddedPanelKernel Q 0 := by
    change h ∈ (embeddedPanelKernel Q 0).subgroupOf (Q.tits.B ⊓ Q.tits.N)
    rw [← cartanPanelMap_kernel]
    exact hzero
  have h1 : (h : X ⧸ Q.D) ∈ embeddedPanelKernel Q 1 := by
    change h ∈ (embeddedPanelKernel Q 1).subgroupOf (Q.tits.B ⊓ Q.tits.N)
    rw [← cartanPanelMap_kernel]
    exact hone
  apply Subtype.ext
  exact (joint_cartan_kernel_eq_bot Q split s hcore).le ⟨⟨h.property,h0⟩,h1⟩

/-- The two actual Cartan images, with no model torus substituted for either. -/
def cartanImagePair : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) →*
    (cartanPanelMap Q 0).range × (cartanPanelMap Q 1).range :=
  (cartanPanelMap Q 0).rangeRestrict.prod (cartanPanelMap Q 1).rangeRestrict

theorem cartanImagePair_injective (s : ∀ i, RootReflection Q split i)
    (hcore : Q.tits.B.normalCore = ⊥) : Function.Injective (cartanImagePair Q) := by
  intro x y hxy
  apply cartanPanelPair_injective Q split s hcore
  exact Prod.ext (congrArg (fun p => p.1.val) hxy) (congrArg (fun p => p.2.val) hxy)

theorem cartan_card_dvd_product_images (s : ∀ i, RootReflection Q split i)
    (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ∣
      Nat.card (cartanPanelMap Q 0).range * Nat.card (cartanPanelMap Q 1).range := by
  rw [← Nat.card_prod]
  exact Subgroup.card_dvd_of_injective (cartanImagePair Q)
    (cartanImagePair_injective Q split s hcore)

/-- Odd-order Cartan correction produces an involution within the same root group.
This is the source choice following (5C), with no perfectness hypothesis. -/
def involutoryRootReflection (i : Fin 2) (s : RootReflection Q split i) :
    RootReflection Q split i where
  val := s.val ^ Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))
  class_eq := by
    rw [map_pow, s.class_eq]
    obtain ⟨k,hk⟩ := split.odd.odd_of_left
    rw [hk, pow_add, pow_mul, (Q.tits.involutions _ (Q.simple_mem i)).2,
      one_pow, pow_one, one_mul]
  mem_rankOne := pow_mem s.mem_rankOne _

theorem involutoryRootReflection_sq (i : Fin 2) (s : RootReflection Q split i) :
    ((involutoryRootReflection Q split i s).val : X ⧸ Q.D)^2 = 1 := by
  let t : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
    ⟨(s.val : X ⧸ Q.D)^2,
      Q.tits.representative_sq_mem_intersection (Q.simple_mem i) s.val s.class_eq⟩
  have he := congrArg Subtype.val (pow_card_eq_one' (x := t))
  change ((s.val : X ⧸ Q.D)^2)^Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = 1 at he
  change ((s.val : X ⧸ Q.D)^Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))^2 = 1
  simpa only [← pow_mul, Nat.mul_comm] using he

theorem involutoryRootReflection_ne_one (i : Fin 2) (s : RootReflection Q split i) :
    ((involutoryRootReflection Q split i s).val : X ⧸ Q.D) ≠ 1 := by
  intro he
  have hs : (involutoryRootReflection Q split i s).val = 1 := Subtype.ext he
  have hc := (involutoryRootReflection Q split i s).class_eq
  rw [hs, map_one] at hc
  exact (Q.tits.involutions _ (Q.simple_mem i)).1 hc.symm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
