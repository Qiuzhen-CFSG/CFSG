module
public import Theory.SpecificGroups.G2.TernaryBorelTwists
public import Mathlib.Tactic.ReduceModChar

/-!
# Intrinsic radicals and torus rigidity in the ternary Borel

Cubing in the six-root coordinates shows that the elements of exponent
three form exactly the union of the two parabolic radicals. Thus every
Borel automorphism permutes these radicals. Excluding their exchange
forces both radicals to be invariant. If such an automorphism normalizes
the split torus, its actions on the two simple-root quotients force it to
fix the torus pointwise.

These restrictions apply to the actual whole-middle discrepancy in
G2Recognition.MaximalMiddleRigidity. They do not yet extend that discrepancy
to either endpoint. Source: Aschbacher–Smith I.4.5, p.417, via F.4.26,
p.288. The imported root coordinates retain the ATLAS attribution and
license in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Atlas.G2.TernaryBorel

/-- Cubing on all six coordinates, including both central coordinates. -/
theorem unipotent_cube (v : Fin 6 → ZMod 3) :
    unipotentProduct v ^ 3 = unipotentProduct ![-v 4^2*v 5,0,-v 4*v 5^2,0,0,0] := by
  rw [pow_succ,pow_two,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> dsimp [unipotentProductParameters] <;> ring_nf <;> reduce_mod_char
  all_goals try simp only [ZMod.pow_card]
  all_goals ring

/-- The exponent-three elements are exactly the union of the two radicals. -/
theorem cube_eq_one_iff_radicals (x : Model (ZMod 3)) (hx : x∈U) :
    x^3=1 ↔ x∈TernaryLevi.radical false ∨ x∈TernaryLevi.radical true := by
  change x∈unipotent at hx
  rw [unipotent_eq_range] at hx
  obtain ⟨v,rfl⟩ := hx
  have hmem (i : Fin 6) (hi : i=4 ∨ i=5) :
      unipotentProduct v∈fiveRootSubgroup i hi ↔ v i=0 := by
    constructor
    · rintro ⟨w,hw,he⟩
      exact (congrFun (unipotentProduct_injective he) i) ▸ hw
    · intro hv
      exact ⟨v,hv,rfl⟩
  change unipotentProduct v ^ 3=1 ↔
    unipotentProduct v∈fiveRootSubgroup 5 (Or.inr rfl) ∨
    unipotentProduct v∈fiveRootSubgroup 4 (Or.inl rfl)
  rw [hmem,hmem,unipotent_cube,←unipotentProduct_zero,unipotentProduct_injective.eq_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    have hz : v 4^2*v 5=0 := by simpa using h0
    rcases mul_eq_zero.mp hz with he | hf
    · exact Or.inr (pow_eq_zero_iff (by decide : 2≠0) |>.mp he)
    · exact Or.inl hf
  · rintro (hf | he)
    · simp [hf]
    · simp [he]

theorem middle_cube_eq_one_iff (x : B) (hx : x∈U.subgroupOf B) :
    x^3=1 ↔ x∈middleRadical false ∨ x∈middleRadical true := by
  rw [←Subtype.coe_inj]
  exact cube_eq_one_iff_radicals x hx

/-- Every automorphism of the whole Borel permutes its two exponent-three radicals. -/
theorem automorphism_radical_cases (δ : MulAut B) (side : Bool) :
    (middleRadical side).map δ.toMonoidHom=middleRadical false ∨
    (middleRadical side).map δ.toMonoidHom=middleRadical true := by
  have hu := automorphism_unipotent δ
  have hsubset : ((middleRadical side).map δ.toMonoidHom:Set B)⊆
      (middleRadical false:Set B)∪middleRadical true := by
    rintro _ ⟨x,hx,rfl⟩
    have hxU : x∈U.subgroupOf B := by
      cases side
      · exact fiveRootSubgroup_le_unipotent 5 (Or.inr rfl) hx
      · exact fiveRootSubgroup_le_unipotent 4 (Or.inl rfl) hx
    have hcube : x^3=1 := (middle_cube_eq_one_iff x hxU).mpr (by
      cases side
      · exact Or.inl hx
      · exact Or.inr hx)
    have hδU : δ x∈U.subgroupOf B := hu ▸ mem_map_of_mem δ.toMonoidHom hxU
    apply (middle_cube_eq_one_iff (δ x) hδU).mp
    rw [←map_pow,hcube,map_one]
  have hc : Nat.card ((middleRadical side).map δ.toMonoidHom)=243 := by
    rw [card_map_of_injective δ.injective,middleRadical_card]
  exact (SubgroupClass.subset_union.mp hsubset).imp
    (fun h => eq_of_le_of_card_ge h (by rw [hc,middleRadical_card]))
    (fun h => eq_of_le_of_card_ge h (by rw [hc,middleRadical_card]))

/-- Once exchange is excluded, both entire radicals are individually invariant. -/
theorem automorphism_radicals_fixed (δ : MulAut B)
    (hne : (middleRadical false).map δ.toMonoidHom≠middleRadical true) :
    ∀ side,(middleRadical side).map δ.toMonoidHom=middleRadical side := by
  have hleft := (automorphism_radical_cases δ false).resolve_right hne
  intro side
  cases side
  · exact hleft
  · rcases automorphism_radical_cases δ true with hr | hr
    · have he : middleRadical true=middleRadical false :=
        map_injective δ.injective (hr.trans hleft.symm)
      have hE : (⟨rootE 1,mem_sup_left (subset_closure (by simp))⟩:B)∈middleRadical false :=
        ⟨![0,0,0,0,1,0],rfl,by simp [unipotentProduct]⟩
      rw [←he] at hE
      obtain ⟨v,hv,hh⟩ := hE
      have hnorm : rootE (1:ZMod 3)=unipotentProduct ![0,0,0,0,1,0] := by
        simp [unipotentProduct]
      change unipotentProduct v=rootE 1 at hh
      rw [hnorm] at hh
      have h4 := congrFun (unipotentProduct_injective hh) 4
      change v 4=1 at h4
      exact (zero_ne_one (hv.symm.trans h4)).elim
    · exact hr
end Atlas.G2.TernaryBorel

namespace Atlas.G2.TernaryBorel
/-- Six-root coordinates in the literal whole-middle carrier. -/
def positive (v : Fin 6 → ZMod 3) : B :=
  ⟨unipotentProduct v,mem_sup_left (unipotentProduct_mem v)⟩

def diagonal (l m : (ZMod 3)ˣ) : B :=
  ⟨torus l m,mem_sup_right ⟨(l,m),rfl⟩⟩

@[simp] theorem positive_mul (v w : Fin 6 → ZMod 3) :
    positive v*positive w=positive (unipotentProductParameters v w) :=
  Subtype.ext (unipotentProduct_mul v w)
@[simp] theorem positive_inv (v : Fin 6 → ZMod 3) :
    (positive v)⁻¹=positive (unipotentInverseParameters v) :=
  Subtype.ext (unipotentProduct_inv v)

theorem positive_injective : Function.Injective positive :=
  fun _ _ h => unipotentProduct_injective (congrArg Subtype.val h)

theorem diagonal_positive (l m : (ZMod 3)ˣ) (v : Fin 6 → ZMod 3) :
    diagonal l m*positive v*(diagonal l m)⁻¹=positive (torusUnipotentParameters l m v) :=
  Subtype.ext (torus_unipotentProduct l m v)

theorem positive_mem_radical (v : Fin 6 → ZMod 3) (side : Bool) :
    positive v∈middleRadical side ↔ v (if side then 4 else 5)=0 := by
  cases side <;> constructor
  all_goals first
  | rintro ⟨w,hw,he⟩; exact (congrFun (unipotentProduct_injective he) _) ▸ hw
  | intro h; exact ⟨v,h,rfl⟩

theorem exists_positive_image (δ : MulAut B) (v : Fin 6 → ZMod 3) :
    ∃ w,δ (positive v)=positive w := by
  have hm : δ (positive v)∈U.subgroupOf B :=
    automorphism_unipotent δ ▸ mem_map_of_mem δ.toMonoidHom (unipotentProduct_mem v)
  change (δ (positive v):Model (ZMod 3))∈unipotent at hm
  rw [unipotent_eq_range] at hm
  obtain ⟨w,hw⟩ := hm
  exact ⟨w,Subtype.ext hw.symm⟩

private theorem simple_images (δ : MulAut B)
    (hfixed : ∀ side,(middleRadical side).map δ.toMonoidHom=middleRadical side) :
    ∃ v w, δ (positive ![0,0,0,0,1,0])=positive v ∧
      δ (positive ![0,0,0,0,0,1])=positive w ∧ v 4≠0 ∧ w 5≠0 := by
  obtain ⟨v,hv⟩ := exists_positive_image δ ![0,0,0,0,1,0]
  obtain ⟨w,hw⟩ := exists_positive_image δ ![0,0,0,0,0,1]
  have hiff (x : B) (side : Bool) : δ x∈middleRadical side ↔ x∈middleRadical side := by
    nth_rw 1 [←hfixed side]
    exact mem_map_iff_mem (f:=δ.toMonoidHom) δ.injective
  refine ⟨v,w,hv,hw,?_,?_⟩
  · intro h
    have hm : δ (positive ![0,0,0,0,1,0])∈middleRadical true := by
      rw [hv,positive_mem_radical]; exact h
    have hh := (positive_mem_radical ![0,0,0,0,1,0] true).mp ((hiff _ _).mp hm)
    exact one_ne_zero hh
  · intro h
    have hm : δ (positive ![0,0,0,0,0,1])∈middleRadical false := by
      rw [hw,positive_mem_radical]; exact h
    have hh := (positive_mem_radical ![0,0,0,0,0,1] false).mp ((hiff _ _).mp hm)
    exact one_ne_zero hh

private def testDiagonal (s : Bool) : B :=
  diagonal (if s then -1 else 1) (if s then 1 else -1)

private theorem test_E (s : Bool) :
    testDiagonal s*positive ![0,0,0,0,1,0]*(testDiagonal s)⁻¹=
      if s then (positive ![0,0,0,0,1,0])⁻¹ else positive ![0,0,0,0,1,0] := by
  cases s <;> simp only [testDiagonal,Bool.false_eq_true,if_false,if_true,
    diagonal_positive,positive_inv]
  all_goals congr 1; decide +kernel
private theorem test_F (s : Bool) :
    testDiagonal s*positive ![0,0,0,0,0,1]*(testDiagonal s)⁻¹=
      (positive ![0,0,0,0,0,1])⁻¹ := by
  cases s <;> simp only [testDiagonal,Bool.false_eq_true,if_false,if_true,
    diagonal_positive,positive_inv]
  all_goals congr 1; decide +kernel

/-- A radical-preserving torus-normalizing discrepancy fixes every torus element. -/
theorem automorphism_torus_pointwise (δ : MulAut B)
    (hA : (A.subgroupOf B).map δ.toMonoidHom=A.subgroupOf B)
    (hfixed : ∀ side,(middleRadical side).map δ.toMonoidHom=middleRadical side) :
    ∀ x∈A.subgroupOf B,δ x=x := by
  obtain ⟨v,w,hv,hw,hv4,hw5⟩ := simple_images δ hfixed
  have htest (s : Bool) : δ (testDiagonal s)=testDiagonal s := by
    have ht : δ (testDiagonal s)∈A.subgroupOf B :=
      hA ▸ mem_map_of_mem δ.toMonoidHom ⟨(_, _),rfl⟩
    obtain ⟨⟨l,m⟩,hh⟩ := ht
    have hd : δ (testDiagonal s)=diagonal l m := Subtype.ext hh.symm
    have he := congrArg δ (test_E s)
    have hf := congrArg δ (test_F s)
    simp only [map_mul,map_inv,apply_ite] at he hf
    simp only [hd,hv,hw,diagonal_positive] at he hf
    simp only [positive_inv] at he hf
    have he4 : torusUnipotentParameters l m v 4=if s then -v 4 else v 4 := by
      cases s <;> simp only [Bool.false_eq_true,if_false,if_true] at he <;> simpa [unipotentInverseParameters] using
        congrFun (positive_injective he) 4
    have hf5 : torusUnipotentParameters l m w 5= -w 5 := by
      simpa [unipotentInverseParameters] using congrFun (positive_injective hf) 5
    have heq : (m:ZMod 3)^2/(l:ZMod 3)=(if s then -1 else 1) := by
      apply mul_right_cancel₀ hv4
      cases s <;> simpa [torusUnipotentParameters] using he4
    have hfq : (l:ZMod 3)/(m:ZMod 3)= -1 := by
      apply mul_right_cancel₀ hw5
      simpa [torusUnipotentParameters] using hf5
    have hparams : l=(if s then -1 else 1) ∧ m=(if s then 1 else -1) := by
      exact (by decide +kernel : ∀ (s : Bool) (l m : (ZMod 3)ˣ),
        (m:ZMod 3)^2/(l:ZMod 3)=(if s then -1 else 1) →
        (l:ZMod 3)/(m:ZMod 3)= -1 →
        l=(if s then -1 else 1) ∧ m=(if s then 1 else -1)) s l m heq hfq
    rw [hd,hparams.1,hparams.2]
    rfl
  rintro x ⟨⟨l,m⟩,hx⟩
  have hxd : x=diagonal l m := Subtype.ext hx.symm
  rw [hxd]
  have units_cases (z : (ZMod 3)ˣ) : z=1 ∨ z= -1 := (by decide : ∀ z : (ZMod 3)ˣ,z=1 ∨ z= -1) z
  rcases units_cases l with rfl | rfl <;> rcases units_cases m with rfl | rfl
  · have hone : diagonal 1 1=1 := Subtype.ext (torusHom.map_one)
    rw [hone,map_one]
  · exact htest false
  · exact htest true
  · have hprod : diagonal (-1) (-1)=testDiagonal true*testDiagonal false := by
      apply Subtype.ext
      change torus (-1) (-1)=torus (-1) 1*torus 1 (-1)
      have h := torusHom.map_mul ((-1:(ZMod 3)ˣ),1) (1,(-1))
      change torus ((-1)*1) (1*(-1))=torus (-1) 1*torus 1 (-1) at h
      simpa only [mul_one,one_mul] using h
    rw [hprod,map_mul,htest,htest]
end Atlas.G2.TernaryBorel
