module
public import Theory.GroupTheory.SubgroupTransport.IntervalCentralizers
public import Theory.GroupTheory.Commutator.CentralizingFactor
public import Theory.GroupAction.Defs
public import Theory.GroupTheory.SubgroupTransport.IntersectionSupplement

/-!
# Elementwise covering in an intersection diagram

Full Sylow-center covering restricts to the endpoint point cells because
the complementary factors centralize the chosen element. Intersecting the
remaining central factor with the middle point gives its neighboring
intersection. Literal partial-isomorphism transport propagates the covers;
the inverse isomorphism supplies the other neighboring quotient.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem 4.7(d), p.48.
This proves the restriction and transport, not an additional covering
hypothesis: its original-degree inputs are supplied by
`Glauberman.PushingUpSL2DegreePointCovering`.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- Both individual-element commutators cover C modulo C ∩ Z. The excluded
subgroups are the literal neighboring point cells. -/
@[expose] def PointCommutatorCovering (A A' B B' C Z : Subgroup G) : Prop :=
  (∀ x ∈ A, x ∉ A' → ∀ y ∈ B, y ∉ B' → ⁅x,y⁆ ≠ 1) ∧
  (∀ x ∈ A, x ∉ A' → ⁅zpowers x,B⁆ ⊔ (C ⊓ Z) = C) ∧
  (∀ y ∈ B, y ∉ B' → ⁅A,zpowers y⁆ ⊔ (C ⊓ Z) = C)

theorem PointCommutatorCovering.symm {A A' B B' C Z : Subgroup G}
    (h : PointCommutatorCovering A A' B B' C Z) :
    PointCommutatorCovering B B' A A' C Z := by
  refine ⟨?_,?_,?_⟩
  · intro y hy hy' x hx hx' he
    apply h.1 x hx hx' y hy hy'
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  · intro y hy hy'
    rw [commutator_comm]
    exact h.2.2 y hy hy'
  · intro x hx hx'
    rw [commutator_comm]
    exact h.2.1 x hx hx'

theorem PointCommutatorCovering.image (φ : S ≃* T)
    {A A' B B' C Z : Subgroup G} (h : PointCommutatorCovering A A' B B' C Z)
    (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S) :
    PointCommutatorCovering (image φ A) (image φ A') (image φ B) (image φ B')
      (image φ C) (image φ Z) := by
  refine ⟨?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩ hx' _ ⟨y,hy,rfl⟩ hy' he
    have hxy : ⁅(x : G),(y : G)⁆ ≠ 1 :=
      h.1 x hx (fun hh => hx' ((mem_image_iff φ A' x).mpr hh))
        y hy (fun hh => hy' ((mem_image_iff φ B' y).mpr hh))
    apply hxy
    have hh : ambientHom φ ⁅x,y⁆ = ambientHom φ 1 := by
      simpa only [map_commutatorElement,map_one] using he
    exact congrArg Subtype.val (ambientHom_injective φ hh)
  · rintro _ ⟨x,hx,rfl⟩ hx'
    have he := congrArg (Theory.GroupTheory.SubgroupTransport.image φ) (h.2.1 x hx (fun hh => hx' ((mem_image_iff φ A' x).mpr hh)))
    rw [image_sup φ _ _ ((commutator_le_sup _ _).trans
      (sup_le (zpowers_le.mpr x.property) hB)) (inf_le_left.trans hC),
      image_commutator φ _ _ (zpowers_le.mpr x.property) hB,image_zpowers,image_inf] at he
    exact he
  · rintro _ ⟨y,hy,rfl⟩ hy'
    have he := congrArg (Theory.GroupTheory.SubgroupTransport.image φ) (h.2.2 y hy (fun hh => hy' ((mem_image_iff φ B' y).mpr hh)))
    rw [image_sup φ _ _ ((commutator_le_sup _ _).trans
      (sup_le hA (zpowers_le.mpr y.property))) (inf_le_left.trans hC),
      image_commutator φ _ _ hA (zpowers_le.mpr y.property),image_zpowers,image_inf] at he
    exact he

private theorem covering_of_residual {D C Z : Subgroup G} (hD : D ≤ C)
    (h : ∀ z ∈ C, ∃ c ∈ D, z * c⁻¹ ∈ Z) : D ⊔ (C ⊓ Z) = C := by
  apply le_antisymm (sup_le hD inf_le_left)
  intro z hz
  obtain ⟨c,hc,hr⟩ := h z hz
  have hm := (D ⊔ (C ⊓ Z)).mul_mem
    (mem_sup_right (show z*c⁻¹ ∈ C ⊓ Z from ⟨C.mul_mem hz (C.inv_mem (hD hc)),hr⟩))
    (mem_sup_left hc)
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

/-- Restrict the original center covering to the left endpoint cells. -/
theorem intervalDiagram_initial_point_covering (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hQ : S ≤ normalizer (S ⊓ T : Set G))
    (hzS : centerIn S = intervalDiagram φ (3*v) v (2*v-1))
    (hzQ : centerIn (S ⊓ T) = intervalDiagram φ (3*v) v (2*v))
    (hzG : center G = intervalDiagram φ (3*v) (v+1) (2*v-1))
    (hcomm : ⁅intervalDiagram φ (3*v) 0 0,intervalDiagram φ (3*v) (2*v) (2*v)⁆ ≤
      intervalDiagram φ (3*v) v v)
    (hact : ∀ x ∈ S, x ∉ S ⊓ T → ∀ z ∈ centerIn S,
      ∃ y ∈ centerIn (S ⊓ T), z * ⁅x,y⁆⁻¹ ∈ center G)
    (hvec : ∀ y ∈ centerIn (S ⊓ T), y ∉ centerIn S → ∀ z ∈ centerIn S,
      ∃ x ∈ S, z * ⁅x,y⁆⁻¹ ∈ center G)
    (hnc : ∀ x ∈ S, x ∉ S ⊓ T → ∀ y ∈ centerIn (S ⊓ T),
      y ∉ centerIn S → ⁅x,y⁆ ≠ 1) :
    let X := intervalDiagram φ (3*v)
    PointCommutatorCovering (X 0 0) (X 1 1) (X (2*v) (2*v)) (X (2*v-1) (2*v-1))
      (X v v) (X (v+1) (v+1)) := by
  let X := intervalDiagram φ (3*v)
  have hAS : X 0 0 ≤ S := by
    exact (intervalCell_antitone φ (by omega) (by omega)).trans (intervalCell_initial_left φ).le
  have hBV : X (2*v) (2*v) ≤ centerIn (S ⊓ T) := by
    rw [hzQ]
    exact intervalDiagram_mono φ (by omega) le_rfl
  have hCZ : X v v ≤ centerIn S := by
    rw [hzS]
    exact intervalDiagram_mono φ le_rfl (by omega)
  have hxQ (x : G) (hx : x ∈ X 0 0) (hx' : x ∉ X 1 1) : x ∉ S ⊓ T := by
    intro h
    apply hx'
    have hh : x ∈ X 0 0 ⊓ (S ⊓ T) := ⟨hx,h⟩
    have he : X 0 0 ⊓ (S ⊓ T) = intervalCell φ 1 (3*v) := by
      rw [←intervalCell_intersection φ]
      change intervalCell φ 0 (3*v-0) ⊓ intervalCell φ 1 1 = _
      rw [Nat.sub_zero,intervalCell_inf,max_eq_right (by omega),max_eq_left (by omega)]
    exact (intervalCell_antitone φ le_rfl (by omega)) (he ▸ hh)
  have hyZ (y : G) (hy : y ∈ X (2*v) (2*v)) (hy' : y ∉ X (2*v-1) (2*v-1)) :
      y ∉ centerIn S := by
    intro hh
    apply hy'
    rw [hzS] at hh
    have hi : y ∈ X (2*v) (2*v) ⊓ X v (2*v-1) := ⟨hy,hh⟩
    rw [intervalDiagram_inf,max_eq_left (by omega),min_eq_right (by omega)] at hi
    exact intervalDiagram_mono φ (by omega) le_rfl hi
  have hinter : X v v ⊓ center G = X v v ⊓ X (v+1) (v+1) := by
    rw [hzG,intervalDiagram_inf,intervalDiagram_inf]
    congr 1
    omega
  have hVS : centerIn (S ⊓ T) ≤ S := inf_le_left.trans inf_le_left
  have hprodV : (centerIn (S ⊓ T) : Set G) =
      (X (2*v) (2*v) : Set G) * (centerIn S : Set G) := by
    have hjoin : X (2*v) (2*v) ⊔ centerIn S = centerIn (S ⊓ T) := by
      rw [hzS,hzQ]
      apply le_antisymm (sup_le (intervalDiagram_mono φ (by omega) le_rfl)
        (intervalDiagram_mono φ le_rfl (by omega)))
      apply intervalDiagram_le_of_points φ (3*v) hgen (by omega) (by omega)
      intro k hvk hk
      by_cases he : k = 2*v
      · subst k; exact le_sup_left
      · exact (intervalDiagram_mono φ hvk (by omega)).trans le_sup_right
    have hc : S ≤ centralizer (centerIn S : Set G) := le_centralizer_iff.mpr inf_le_right
    rw [←coe_mul_of_left_le_normalizer_right (X (2*v) (2*v)) (centerIn S)
      ((hBV.trans hVS).trans (hc.trans (centralizer_le_normalizer _))),hjoin]
  have hprodS : (S : Set G) = (X 0 0 : Set G) * (S ⊓ T : Set G) := by
    have hjoin : X 0 0 ⊔ (S ⊓ T) = S := by
      exact intervalCell_left_supplement φ (3*v) (by omega) (fun b _ hb => hgen 0 b (by omega))
    change (S : Set G) = (X 0 0 : Set G) * ((S ⊓ T : Subgroup G) : Set G)
    rw [←coe_mul_of_left_le_normalizer_right (X 0 0) (S ⊓ T) (hAS.trans hQ),hjoin]
  refine ⟨fun x hx hx' y hy hy' => hnc x (hAS hx) (hxQ x hx hx')
    y (hBV hy) (hyZ y hy hy'),?_,?_⟩
  · intro x hx hx'
    have hD : ⁅zpowers x,X (2*v) (2*v)⁆ ≤ X v v :=
      (commutator_mono (zpowers_le.mpr hx) le_rfl).trans hcomm
    have he := commutator_eq_of_product_centralizing_factor hprodV
      (show zpowers x ≤ centralizer (centerIn S : Set G) from
        (zpowers_le.mpr (hAS hx)).trans (le_centralizer_iff.mpr inf_le_right))
    rw [←hinter]
    apply covering_of_residual hD
    intro z hz
    obtain ⟨y,hy,hr⟩ := hact x (hAS hx) (hxQ x hx hx') z (hCZ hz)
    refine ⟨⁅x,y⁆,?_,hr⟩
    rw [←he]
    exact commutator_mem_commutator (mem_zpowers x) hy
  · intro y hy hy'
    have hD : ⁅X 0 0,zpowers y⁆ ≤ X v v :=
      (commutator_mono le_rfl (zpowers_le.mpr hy)).trans hcomm
    have he := commutator_eq_of_product_centralizing_factor
      (V := zpowers y) (X := S) (A := X 0 0) (Q := S ⊓ T) hprodS
      (show zpowers y ≤ centralizer (S ⊓ T : Set G) from
        (zpowers_le.mpr (hBV hy)).trans inf_le_right)
    rw [commutator_comm (zpowers y) S,commutator_comm (zpowers y) (X 0 0)] at he
    rw [←hinter]
    apply covering_of_residual hD
    intro z hz
    obtain ⟨x,hx,hr⟩ := hvec y (hBV hy) (hyZ y hy hy') z (hCZ hz)
    refine ⟨⁅x,y⁆,?_,hr⟩
    rw [←he]
    exact commutator_mem_commutator hx (mem_zpowers y)

/-- Transport each elementwise covering along the literal partial
isomorphism, keeping its specified neighboring point kernels. -/
theorem intervalDiagram_point_covering_shift (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (h : let X := intervalDiagram φ (3*v)
      PointCommutatorCovering (X 0 0) (X 1 1) (X (2*v) (2*v)) (X (2*v-1) (2*v-1))
        (X v v) (X (v+1) (v+1))) (i : ℕ) (hi : i ≤ v) :
    let X := intervalDiagram φ (3*v)
    PointCommutatorCovering (X i i) (X (i+1) (i+1))
      (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1))
      (X (i+v) (i+v)) (X (i+v+1) (i+v+1)) := by
  let X := intervalDiagram φ (3*v)
  induction i with
  | zero => simpa only [Nat.zero_add] using h
  | succ i ih =>
    have hS (j : ℕ) (hj : j < 3*v) : X j j ≤ S :=
      (intervalCell_antitone φ (by omega) (by omega)).trans (intervalCell_initial_left φ).le
    have hh := (ih (by omega)).image φ (hS i (by omega)) (hS (i+2*v) (by omega))
      (hS (i+v) (by omega))
    rw [image_intervalDiagram φ (show i < 3*v by omega),
      image_intervalDiagram φ (show i+1 < 3*v by omega),
      image_intervalDiagram φ (show i+2*v < 3*v by omega),
      image_intervalDiagram φ (show i+2*v-1 < 3*v by omega),
      image_intervalDiagram φ (show i+v < 3*v by omega),
      image_intervalDiagram φ (show i+v+1 < 3*v by omega)] at hh
    convert hh using 1 <;> congr 1 <;> omega

/-- Reflection is the literal reversal of interval endpoints. -/
theorem intervalDiagram_symm (φ : S ≃* T) (w i j : ℕ) (hi : i ≤ w) :
    intervalDiagram φ.symm w i j = intervalDiagram φ w (w-j) (w-i) := by
  simp only [intervalDiagram,intervalCell_symm,show w-(w-i)=i by omega]

/-- Right-hand covering follows by applying left-hand transport to the
inverse partial isomorphism and reversing the commutator. -/
theorem intervalDiagram_point_covering_reverse (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (h : let X := intervalDiagram φ.symm (3*v)
      PointCommutatorCovering (X 0 0) (X 1 1) (X (2*v) (2*v)) (X (2*v-1) (2*v-1))
        (X v v) (X (v+1) (v+1))) (i : ℕ) (hi : i ≤ v) :
    let X := intervalDiagram φ (3*v)
    PointCommutatorCovering (X i i) (X (i+1) (i+1))
      (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1))
      (X (i+v) (i+v)) (X (i+v-1) (i+v-1)) := by
  have hh := (intervalDiagram_point_covering_shift φ.symm v hv h (v-i) (by omega)).symm
  rw [intervalDiagram_symm φ (3*v) (v-i) (v-i) (by omega),
    intervalDiagram_symm φ (3*v) (v-i+1) (v-i+1) (by omega),
    intervalDiagram_symm φ (3*v) (v-i+2*v) (v-i+2*v) (by omega),
    intervalDiagram_symm φ (3*v) (v-i+2*v-1) (v-i+2*v-1) (by omega),
    intervalDiagram_symm φ (3*v) (v-i+v) (v-i+v) (by omega),
    intervalDiagram_symm φ (3*v) (v-i+v+1) (v-i+v+1) (by omega)] at hh
  convert hh using 1 <;> congr 1 <;> omega
end Theory.GroupTheory.SubgroupTransport
