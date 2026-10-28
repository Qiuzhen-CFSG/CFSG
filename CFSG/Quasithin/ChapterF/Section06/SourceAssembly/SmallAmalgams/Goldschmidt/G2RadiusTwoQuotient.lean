module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoConjugation
public import Theory.GroupTheory.SymmetricFourCoxeterRecognition

/-!
# The original six-label quotient is symmetric of degree four

The six source labels form three pairs modulo the neighboring four-group.
Their literal conjugation action gives the three Coxeter generators. The
alternative cubic relation would make a moved neighboring involution a sixth
power of the element moving it, which is impossible. The marked Coxeter
recognition therefore identifies the actual quotient with S₄ and gives the
source distance-three group order ninety-six.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.9),
printed pp.400–401.
-/

@[expose] public section
open Subgroup SimpleGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
namespace Frame
variable {β : RankTwo.Vertex F} {f : BranchFrame F β} (r : Frame f)

/-- The three neighboring source involutions are pairwise different. -/
theorem branch_labels_injective (c : CanonicalLabelSetup F s) (hβ : β.type ≠ c.side) :
    Function.Injective (fun i : Fin 3 => c.label (f.e i).val) := by
  intro i j he
  change c.label (f.e i).val = c.label (f.e j).val at he
  by_contra hn
  obtain ⟨k, hki, hkj⟩ := (by decide :
    ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j) i j hn
  have hne {i j : Fin 3} (hh : i ≠ j) : (f.e i).val ≠ (f.e j).val :=
    fun hi => hh (f.e.injective (Subtype.ext hi))
  have hp := c.neighbor_product β (f.e i).val (f.e j).val (f.e k).val
    (f.e i).property (f.e j).property (f.e k).property
    (hne hn) (hne hki.symm) (hne hkj.symm) (branch_type c hβ i)
  rw [he, c.label_mul_self (branch_type c hβ j), one_mul] at hp
  have ho := c.order_two (f.e k).val (branch_type c hβ k)
  simp only [hp, orderOf_one] at ho
  omega

/-- The pair product centralizes the original normal four-group. -/
theorem pair_product_mem_centralizer (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) (hβ : β.type ≠ c.side) (i : Fin 3) :
    c.label (r.u (i,0)) * c.label (r.u (i,1)) ∈
      centralizer (c.neighborLabelGroup β : Set G) := by
  let a : RankTwo.stabilizer F β := ⟨_,
    c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (i,0))⟩
  let b : RankTwo.stabilizer F β := ⟨_,
    c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (i,1))⟩
  have ha : f.branchAction a = Equiv.swap (i+1) (i+2) := r.label_branch_action c hr hs h hβ (i,0)
  have hb : f.branchAction b = Equiv.swap (i+1) (i+2) := r.label_branch_action c hr hs h hβ (i,1)
  have hab : f.branchAction (a*b) = 1 := by rw [map_mul, ha, hb, Equiv.swap_mul_self]
  rw [CanonicalLabelSetup.neighborLabelGroup, centralizer_closure]
  apply mem_centralizer_iff.mpr
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj⟩ := f.e.surjective ⟨w,hw⟩
  have hjv : (f.e j).val = w := congrArg Subtype.val hj
  rw [← hjv]
  have hfix := f.branchAction_eval (a*b) j
  rw [hab, Equiv.Perm.one_apply] at hfix
  have he := c.conjugate (a*b).val (f.e j).val (branch_type c hβ j)
  rw [← hfix] at he
  change c.label (f.e j).val =
    (c.label (r.u (i,0)) * c.label (r.u (i,1))) * c.label (f.e j).val *
      (c.label (r.u (i,0)) * c.label (r.u (i,1)))⁻¹ at he
  change c.label (f.e j).val * (c.label (r.u (i,0)) * c.label (r.u (i,1))) = _
  calc
    _ = ((c.label (r.u (i,0)) * c.label (r.u (i,1))) * c.label (f.e j).val *
      (c.label (r.u (i,0)) * c.label (r.u (i,1)))⁻¹) *
        (c.label (r.u (i,0)) * c.label (r.u (i,1))) := congrArg (fun z => z * _) he
    _ = _ := by group

/-- Products from the first and third branches move the middle neighboring label. -/
theorem outer_product_not_commute_middle (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) (hβ : β.type ≠ c.side) (b d : ZMod 2) :
    ¬ Commute (c.label (r.u (0,b)) * c.label (r.u (2,d))) (c.label (f.e 1).val) := by
  let a : RankTwo.stabilizer F β := ⟨_,
    c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (0,b))⟩
  let z : RankTwo.stabilizer F β := ⟨_,
    c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (2,d))⟩
  have ha : f.branchAction a = Equiv.swap (0+1) (0+2) := r.label_branch_action c hr hs h hβ (0,b)
  have hz : f.branchAction z = Equiv.swap (2+1) (2+2) := r.label_branch_action c hr hs h hβ (2,d)
  have heval : f.branchAction (a*z) 1 = 0 := by rw [map_mul, ha, hz]; decide
  have hmove := f.branchAction_eval (a*z) 1
  rw [heval] at hmove
  have he := c.conjugate (a*z).val (f.e 1).val (branch_type c hβ 1)
  rw [← hmove] at he
  intro hc
  change c.label (f.e 0).val =
    (c.label (r.u (0,b)) * c.label (r.u (2,d))) * c.label (f.e 1).val *
      (c.label (r.u (0,b)) * c.label (r.u (2,d)))⁻¹ at he
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one] at he
  have hh : (0 : Fin 3) = 1 := branch_labels_injective c hβ he
  contradiction


/-- Either ordering of a branch pair has the same nontrivial square and
centralizes the original four-group. -/
theorem pair_product_structure (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) (hβ : β.type ≠ c.side) (i : Fin 3)
    (b d : ZMod 2) (hbd : b ≠ d) :
    (c.label (r.u (i,b)) * c.label (r.u (i,d))) ^ 2 = c.label (f.e i).val ∧
      c.label (r.u (i,b)) * c.label (r.u (i,d)) ∈
        centralizer (c.neighborLabelGroup β : Set G) := by
  have hsq : (c.label (r.u (i,0)) * c.label (r.u (i,1))) ^ 2 = c.label (f.e i).val := by
    simpa only [commutatorElement_def, c.label_inv (r.vertex_type c h hβ (i,0)),
      c.label_inv (r.vertex_type c h hβ (i,1)), pow_two, mul_assoc] using
      r.pair_commutator c hr hs h hβ i
  have hc := r.pair_product_mem_centralizer c hr hs h hβ i
  have he : c.label (r.u (i,1)) * c.label (r.u (i,0)) =
      (c.label (r.u (i,0)) * c.label (r.u (i,1)))⁻¹ := by
    rw [mul_inv_rev, c.label_inv (r.vertex_type c h hβ (i,0)),
      c.label_inv (r.vertex_type c h hβ (i,1))]
  fin_cases b <;> fin_cases d
  · exact (hbd rfl).elim
  · exact ⟨hsq, hc⟩
  · change (c.label (r.u (i,1)) * c.label (r.u (i,0))) ^ 2 = c.label (f.e i).val ∧
      c.label (r.u (i,1)) * c.label (r.u (i,0)) ∈ centralizer (c.neighborLabelGroup β : Set G)
    rw [he, inv_pow, hsq, c.label_inv (branch_type c hβ i)]
    exact ⟨rfl, (centralizer _).inv_mem hc⟩
  · exact (hbd rfl).elim

end Frame
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels

open Subgroup SimpleGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
namespace Frame
variable {β : RankTwo.Vertex F} {f : BranchFrame F β} (r : Frame f)
variable (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
variable (h : CubicTreeAction F) (hβ : β.type ≠ c.side)

abbrev second := c.radiusTwoSecondGroup β
def four (_hr : c.radius = 2) (_hs : 4 ≤ s) (_h : CubicTreeAction F)
    (_hβ : β.type ≠ c.side) : Subgroup (second c (β := β)) :=
  (c.neighborLabelGroup β).subgroupOf (second c (β := β))

local instance four_normal : (four c hr hs h hβ (β := β)).Normal :=
  c.radiusTwo_neighborLabelGroup_normal hr (by omega) h hβ

abbrev Quotient := second c (β := β) ⧸ four c hr hs h hβ (β := β)

noncomputable def reflection (x : Fin 3 × ZMod 2) : Quotient c hr hs h hβ (β := β) :=
  QuotientGroup.mk' (four c hr hs h hβ (β := β)) ⟨c.label (r.u x), r.mem_second c h hβ x⟩

theorem reflection_square (x : Fin 3 × ZMod 2) :
    r.reflection c hr hs h hβ x ^ 2 = 1 := by
  rw [reflection, ← map_pow]
  have he : (⟨c.label (r.u x), r.mem_second c h hβ x⟩ : second c (β := β)) ^ 2 = 1 :=
    Subtype.ext (by simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using c.label_mul_self (r.vertex_type c h hβ x))
  rw [he, map_one]

theorem reflection_pair_commute (i : Fin 3) :
    Commute (r.reflection c hr hs h hβ (i,0)) (r.reflection c hr hs h hβ (i,1)) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [reflection, reflection, ← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  change ⁅c.label (r.u (i,0)), c.label (r.u (i,1))⁆ ∈ c.neighborLabelGroup β
  rw [r.pair_commutator c hr hs h hβ]
  exact subset_closure ⟨(f.e i).val, (f.e i).property, rfl⟩

theorem reflection_pair_ne (i : Fin 3) :
    r.reflection c hr hs h hβ (i,0) ≠ r.reflection c hr hs h hβ (i,1) := by
  intro he
  apply r.pair_product_not_mem_neighborLabelGroup c hr hs h hβ i
  have hh : r.reflection c hr hs h hβ (i,0) * r.reflection c hr hs h hβ (i,1) = 1 := by
    rw [he, ← pow_two, r.reflection_square c hr hs h hβ]
  rw [reflection, reflection, ← map_mul] at hh
  have hm := (QuotientGroup.eq_one_iff (N := four c hr hs h hβ (β := β)) _).mp hh
  exact hm


/-- Conjugating the selected cosets uses precisely the existing sphere action. -/
theorem reflection_conjugate (g : second c (β := β)) (x : Fin 3 × ZMod 2) :
    QuotientGroup.mk' (four c hr hs h hβ (β := β)) g * r.reflection c hr hs h hβ x *
      (QuotientGroup.mk' (four c hr hs h hβ (β := β)) g)⁻¹ =
        r.reflection c hr hs h hβ
          (f.sphereAction h (Subgroup.inclusion
            (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) x) := by
  simp only [reflection, ← map_inv, ← map_mul]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (g.val * c.label (r.u x) * g.val⁻¹) /
    c.label (r.u (f.sphereAction h _ x)) ∈ c.neighborLabelGroup β
  rw [div_eq_mul_inv]
  exact r.conjugate_label_difference_mem c hr (by omega) h hβ
    (Subgroup.inclusion (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) x

/-- The six marked quotient involutions generate the literal source quotient. -/
theorem reflection_generates :
    closure (Set.range (r.reflection c hr hs h hβ)) = ⊤ := by
  let t : Fin 3 × ZMod 2 → second c (β := β) :=
    fun x => ⟨c.label (r.u x), r.mem_second c h hβ x⟩
  have ht : closure (Set.range t) = ⊤ := by
    apply top_unique
    intro k _
    have hle : second c (β := β) ≤ (closure (Set.range t)).map (second c (β := β)).subtype := by
      change c.radiusTwoSecondGroup β ≤ _
      rw [r.six_generators c hr hs h hβ]
      apply (closure_le _).mpr
      rintro _ ⟨x,rfl⟩
      exact ⟨t x,subset_closure ⟨x,rfl⟩,rfl⟩
    obtain ⟨l,hl,he⟩ := hle k.property
    exact (Subtype.ext he : l=k) ▸ hl
  have he := congrArg (Subgroup.map (QuotientGroup.mk' (four c hr hs h hβ (β := β)))) ht
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)] at he
  exact he


/-- The three source reflections already generate the quotient. -/
theorem reflection_three_generates :
    closure ({r.reflection c hr hs h hβ (0,0), r.reflection c hr hs h hβ (2,0),
      r.reflection c hr hs h hβ (0,1)} : Set (Quotient c hr hs h hβ (β := β))) = ⊤ := by
  let K := closure ({r.reflection c hr hs h hβ (0,0), r.reflection c hr hs h hβ (2,0),
    r.reflection c hr hs h hβ (0,1)} : Set (Quotient c hr hs h hβ (β := β)))
  have hzero (b : ZMod 2) : r.reflection c hr hs h hβ (0,b) ∈ K := by
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
    · exact subset_closure (Or.inl rfl)
    · exact subset_closure (Or.inr (Or.inr rfl))
  have htwo : r.reflection c hr hs h hβ (2,0) ∈ K := subset_closure (by simp)
  have step (x y : Fin 3 × ZMod 2) (hx : r.reflection c hr hs h hβ x ∈ K)
      (hy : r.reflection c hr hs h hβ
        (f.sphereAction h ⟨c.label (r.u x),
          c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ x)⟩ y) ∈ K) :
      r.reflection c hr hs h hβ y ∈ K := by
    have he := r.reflection_conjugate c hr hs h hβ ⟨_, r.mem_second c h hβ x⟩ y
    change r.reflection c hr hs h hβ x * r.reflection c hr hs h hβ y *
      (r.reflection c hr hs h hβ x)⁻¹ = _ at he
    change r.reflection c hr hs h hβ x * r.reflection c hr hs h hβ y *
      (r.reflection c hr hs h hβ x)⁻¹ =
        r.reflection c hr hs h hβ (f.sphereAction h ⟨c.label (r.u x),
          c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ x)⟩ y) at he
    rw [← he] at hy
    have hk := K.mul_mem (K.mul_mem (K.inv_mem hx) hy) hx
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hk
  have hone (b : ZMod 2) : r.reflection c hr hs h hβ (1,b) ∈ K := by
    apply step (2,0) (1,b) htwo
    have he := f.sphereAction_block h
      ⟨c.label (r.u (2,0)), c.radiusTwo_second_le_stabilizer hr (by omega) β
        (r.mem_second c h hβ (2,0))⟩ (1,b)
    rw [r.label_branch_action c hr hs h hβ] at he
    have hp : (f.sphereAction h ⟨c.label (r.u (2,0)),
        c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (2,0))⟩ (1,b)).1 = 0 :=
      he.trans (by change Equiv.swap (0 : Fin 3) 1 1 = 0; decide)
    convert hzero (f.sphereAction h ⟨c.label (r.u (2,0)),
      c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (2,0))⟩ (1,b)).2 using 1
    rw [← hp]
  have htwoall (b : ZMod 2) : r.reflection c hr hs h hβ (2,b) ∈ K := by
    apply step (0,0) (2,b) (hzero 0)
    have he := f.sphereAction_block h
      ⟨c.label (r.u (0,0)), c.radiusTwo_second_le_stabilizer hr (by omega) β
        (r.mem_second c h hβ (0,0))⟩ (2,b)
    rw [r.label_branch_action c hr hs h hβ] at he
    have hp : (f.sphereAction h ⟨c.label (r.u (0,0)),
        c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (0,0))⟩ (2,b)).1 = 1 :=
      he.trans (by change Equiv.swap (1 : Fin 3) 2 2 = 1; decide)
    convert hone (f.sphereAction h ⟨c.label (r.u (0,0)),
      c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (0,0))⟩ (2,b)).2 using 1
    rw [← hp]
  apply top_unique
  rw [← r.reflection_generates c hr hs h hβ]
  apply (closure_le _).mpr
  rintro _ ⟨⟨i,b⟩,rfl⟩
  fin_cases i
  · exact hzero b
  · exact hone b
  · exact htwoall b


private theorem reflection_cube_ne_pair (b d u v : ZMod 2) (huv : u ≠ v) :
    (r.reflection c hr hs h hβ (0,b) * r.reflection c hr hs h hβ (2,d)) ^ 3 ≠
      r.reflection c hr hs h hβ (1,u) * r.reflection c hr hs h hβ (1,v) := by
  intro he
  let a : second c (β := β) := ⟨_, r.mem_second c h hβ (0,b)⟩
  let z : second c (β := β) := ⟨_, r.mem_second c h hβ (2,d)⟩
  let x : second c (β := β) := ⟨_, r.mem_second c h hβ (1,u)⟩
  let y : second c (β := β) := ⟨_, r.mem_second c h hβ (1,v)⟩
  have hq : QuotientGroup.mk' (four c hr hs h hβ (β := β)) ((a*z)^3) =
      QuotientGroup.mk' (four c hr hs h hβ (β := β)) (x*y) := by
    rw [map_pow,map_mul,map_mul]
    exact he
  have hn := QuotientGroup.eq_iff_div_mem.mp hq
  change ((c.label (r.u (0,b)) * c.label (r.u (2,d))) ^ 3) /
    (c.label (r.u (1,u)) * c.label (r.u (1,v))) ∈ c.neighborLabelGroup β at hn
  let n := ((c.label (r.u (0,b)) * c.label (r.u (2,d))) ^ 3) /
    (c.label (r.u (1,u)) * c.label (r.u (1,v)))
  have hnm : n ∈ c.neighborLabelGroup β := hn
  let := c.radiusTwo_neighborLabelGroup_isKleinFour hr (by omega) h β hβ
  have hn2 : n ^ 2 = 1 := by
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self (⟨n,hnm⟩ : c.neighborLabelGroup β))
  obtain ⟨ht2, htN⟩ := r.pair_product_structure c hr hs h hβ 1 u v huv
  have hnt : Commute n (c.label (r.u (1,u)) * c.label (r.u (1,v))) :=
    mem_centralizer_iff.mp htN n hnm
  have hnprod : (c.label (r.u (0,b)) * c.label (r.u (2,d))) ^ 3 =
      n * (c.label (r.u (1,u)) * c.label (r.u (1,v))) := by
    dsimp only [n]
    rw [div_mul_cancel]
  have hsix : (c.label (r.u (0,b)) * c.label (r.u (2,d))) ^ 6 = c.label (f.e 1).val := by
    rw [show 6 = 3*2 from rfl, pow_mul, hnprod, hnt.mul_pow, hn2, ht2, one_mul]
  exact r.outer_product_not_commute_middle c hr hs h hβ b d
    (hsix ▸ (Commute.refl (c.label (r.u (0,b)) * c.label (r.u (2,d)))).pow_right 6)

/-- Both outer-branch relations are cubic: the alternative branch member
would force a moved neighboring involution to be a sixth power. -/
theorem reflection_outer_cube (b d : ZMod 2) :
    (r.reflection c hr hs h hβ (0,b) * r.reflection c hr hs h hβ (2,d)) ^ 3 = 1 := by
  let a : RankTwo.stabilizer F β := ⟨c.label (r.u (0,b)),
    c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (0,b))⟩
  let z : RankTwo.stabilizer F β := ⟨c.label (r.u (2,d)),
    c.radiusTwo_second_le_stabilizer hr (by omega) β (r.mem_second c h hβ (2,d))⟩
  let U := f.sphereAction h a (2,d)
  let V := f.sphereAction h z (0,b)
  have hU : U.1 = 1 := by
    rw [f.sphereAction_block, r.label_branch_action c hr hs h hβ]
    change Equiv.swap (1 : Fin 3) 2 2 = 1
    decide
  have hV : V.1 = 1 := by
    rw [f.sphereAction_block, r.label_branch_action c hr hs h hβ]
    change Equiv.swap (0 : Fin 3) 1 0 = 1
    decide
  have hu : U = (1,U.2) := Prod.ext hU rfl
  have hv : V = (1,V.2) := Prod.ext hV rfl
  have hconjA := r.reflection_conjugate c hr hs h hβ ⟨_, r.mem_second c h hβ (0,b)⟩ (2,d)
  have hconjZ := r.reflection_conjugate c hr hs h hβ ⟨_, r.mem_second c h hβ (2,d)⟩ (0,b)
  change r.reflection c hr hs h hβ (0,b) * r.reflection c hr hs h hβ (2,d) *
    (r.reflection c hr hs h hβ (0,b))⁻¹ = r.reflection c hr hs h hβ U at hconjA
  change r.reflection c hr hs h hβ (2,d) * r.reflection c hr hs h hβ (0,b) *
    (r.reflection c hr hs h hβ (2,d))⁻¹ = r.reflection c hr hs h hβ V at hconjZ
  have hinv (x : Fin 3 × ZMod 2) : (r.reflection c hr hs h hβ x)⁻¹ = r.reflection c hr hs h hβ x := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, r.reflection_square c hr hs h hβ]
  have hcub : (r.reflection c hr hs h hβ (0,b) * r.reflection c hr hs h hβ (2,d)) ^ 3 =
      r.reflection c hr hs h hβ (1,U.2) * r.reflection c hr hs h hβ (1,V.2) := by
    rw [← hu, ← hv, ← hconjA, ← hconjZ, hinv, hinv]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have he : U.2 = V.2 := by
    by_contra hn
    exact r.reflection_cube_ne_pair c hr hs h hβ b d U.2 V.2 hn hcub
  rw [hcub, he, ← pow_two, r.reflection_square c hr hs h hβ]


/-- The original quotient by the neighboring four-group is S₄, with the
three source generators retained. -/
theorem reflection_quotient_symmetric_four :
    ∃ e : Quotient c hr hs h hβ (β := β) ≃* Equiv.Perm (Fin 4),
      e (r.reflection c hr hs h hβ (0,0)) = Equiv.swap 0 1 ∧
      e (r.reflection c hr hs h hβ (2,0)) = Equiv.swap 1 2 ∧
      e (r.reflection c hr hs h hβ (0,1)) = Equiv.swap 2 3 := by
  have hc : (r.reflection c hr hs h hβ (2,0) * r.reflection c hr hs h hβ (0,1)) ^ 3 = 1 := by
    have hh := congrArg (fun x => (r.reflection c hr hs h hβ (0,1))⁻¹ * x *
      r.reflection c hr hs h hβ (0,1)) (r.reflection_outer_cube c hr hs h hβ 1 0)
    simpa [pow_succ, mul_assoc] using hh
  exact Theory.GroupTheory.SymmetricFourCoxeterRecognition.exists_marked_equiv
    _ _ _ (r.reflection_square c hr hs h hβ (0,0)) (r.reflection_square c hr hs h hβ (2,0))
    (r.reflection_square c hr hs h hβ (0,1)) (r.reflection_outer_cube c hr hs h hβ 0 0) hc
    (r.reflection_pair_commute c hr hs h hβ 0) (r.reflection_three_generates c hr hs h hβ)
    (r.reflection_pair_ne c hr hs h hβ 0)

include r hr hs h hβ
/-- The source second local group has its original order ninety-six. -/
theorem second_card : Nat.card (c.radiusTwoSecondGroup β) = 96 := by
  obtain ⟨e, _⟩ := r.reflection_quotient_symmetric_four c hr hs h hβ
  have hq : Nat.card (Quotient c hr hs h hβ (β := β)) = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hN : Nat.card (four c hr hs h hβ (β := β)) = 4 := by
    change Nat.card ((c.neighborLabelGroup β).subgroupOf (c.radiusTwoSecondGroup β)) = 4
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (c.radiusTwo_neighborLabelGroup_le_second h hβ)).toEquiv]
    let := c.radiusTwo_neighborLabelGroup_isKleinFour hr (by omega) h β hβ
    exact IsKleinFour.card_four
  have hc := (four c hr hs h hβ (β := β)).index_mul_card
  rw [Subgroup.index_eq_card, hq, hN] at hc
  exact hc.symm

end Frame
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
/-- The literal second source group in (6.9) has order ninety-six. -/
theorem CanonicalLabelSetup.radiusTwo_second_card
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {β : RankTwo.Vertex F} (hβ : β.type ≠ c.side) :
    Nat.card (c.radiusTwoSecondGroup β) = 96 := by
  obtain ⟨f⟩ := h.exists_branchFrame β
  exact (RadiusTwoSixLabels.frame h f).second_card c hr hs h hβ
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
