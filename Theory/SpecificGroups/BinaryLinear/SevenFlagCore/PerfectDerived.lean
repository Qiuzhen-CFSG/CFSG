module
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore
import all Theory.SpecificGroups.BinaryLinear.SevenFlagCore
public import Mathlib.GroupTheory.IsPerfect
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs

/-!
# Central derived two-cores of perfect small binary Sylow-normalized groups

This is an internal continuation of `SevenFlagCore`: its private coordinate
machinery is imported intentionally, leaving the frozen public boundary
unchanged. In the adjacent three-block flags, the scalar between the two
singleton blocks is an abelian quotient and hence vanishes on a perfect
subgroup. Its two-core is then abelian. In the middle flag the derived
core lies in the corner fixed by the whole flag stabilizer.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement Classical
namespace BinaryLinear.SevenFlagCore
open OuterCyclic InvariantNodeActions SmallParabolicLevi
variable {m : ℕ}

private theorem strict_pair_zero (c : Fin (m+1) → Fin (m+1))
    (A B : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2))
    (hA : Strict c A) (hB : Strict c B)
    (hp : ∀ i k j, c i < c k → c k < c j → A i k = 0 ∨ B k j = 0) : A*B = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : c k ≤ c i
  · rw [hA i k ha,zero_mul]
  by_cases hb : c j ≤ c k
  · rw [hB k j hb,mul_zero]
  rcases hp i k j (lt_of_not_ge ha) (lt_of_not_ge hb) with hz | hz
  · rw [hz,zero_mul]
  · rw [hz,mul_zero]

private theorem commute_of_zero_differences (g h : LinearGroup (m+1))
    (hgh : (matrix g-1)*(matrix h-1)=0) (hhg : (matrix h-1)*(matrix g-1)=0) :
    Commute g h := by
  apply (slEquivLinear (m+1)).symm.injective
  apply Subtype.ext
  change matrixHom (g*h) = matrixHom (h*g)
  rw [map_mul,map_mul]
  change matrix g*matrix h = matrix h*matrix g
  have hg : matrix g = 1+(matrix g-1) := by noncomm_ring
  have hh : matrix h = 1+(matrix h-1) := by noncomm_ring
  calc
    _ = 1+(matrix g-1)+(matrix h-1) := by
      conv_lhs => rw [hg,hh]
      simp only [add_mul,mul_add,one_mul,mul_one,hgh]
      abel
    _ = matrix h*matrix g := by
      conv_rhs => rw [hh,hg]
      simp only [add_mul,mul_add,one_mul,mul_one,hhg]
      abel

private theorem kernel_commutator_matrix (c : Fin (m+1) → Fin (m+1))
    (hc : ∀ i, (c i).val ≤ 2) (g h : (diagonalAction c).ker) :
    matrix ⁅g.val.val,h.val.val⁆ = 1+
      ((matrix g.val.val-1)*(matrix h.val.val-1)-(matrix h.val.val-1)*(matrix g.val.val-1)) := by
  let M := matrixHom (m := m)
  let a := M g.val.val-1
  let b := M h.val.val-1
  have tz (x y z : (diagonalAction c).ker) :
      (M x.val.val-1)*(M y.val.val-1)*(M z.val.val-1)=0 :=
    strict_triple_zero c hc _ _ _ (strict_difference c x.val x.property)
      (strict_difference c y.val y.property) (strict_difference c z.val z.property)
  have invprod (x : (diagonalAction c).ker) : M x.val.val*M x⁻¹.val.val=1 := by
    change M x.val.val*M x.val.val⁻¹=1
    rw [←map_mul,mul_inv_cancel,map_one]
  have he : a*b-b*a=M g.val.val*M h.val.val-M h.val.val*M g.val.val := by
    dsimp [a,b]
    noncomm_ring
  have hr (x : (diagonalAction c).ker) : (a*b-b*a)*M x.val.val=a*b-b*a := by
    have h1 := tz g h x
    have h2 := tz h g x
    change a*b*(M x.val.val-1)=0 at h1
    change b*a*(M x.val.val-1)=0 at h2
    rw [mul_sub,mul_one,sub_eq_zero] at h1 h2
    rw [sub_mul,h1,h2]
  change M ⁅g.val.val,h.val.val⁆=1+(a*b-b*a)
  calc
    _ = (a*b-b*a)*M g⁻¹.val.val*M h⁻¹.val.val+1 := by
      rw [he,sub_mul,sub_mul,commutatorElement_def,map_mul,map_mul,map_mul]
      have hh : M h.val.val*M g.val.val*M g⁻¹.val.val*M h⁻¹.val.val=1 := by
        rw [mul_assoc (M h.val.val) (M g.val.val),invprod,mul_one,invprod]
      rw [hh,sub_add_cancel]
      rfl
    _ = _ := by rw [hr,hr]; exact add_comm _ _

private theorem singleton_diagonal (c : Fin (m+1) → Fin (m+1))
    (g : triangularGroup c) (i : Fin (m+1))
    (hi : ∀ j, c j=c i → j=i) : matrix g.val i i=1 := by
  let v : BlockSpace c (c i) := fun _ => 1
  have hv : v ≠ 0 := by intro he; have := congrFun he ⟨i,rfl⟩; exact one_ne_zero this
  have hsum : ∀ r : Block c (c i), diagonalFactor c (c i) g v r = matrix g.val i i := by
    intro r
    have hr : r.val=i := hi r.val r.property
    change (∑ j : Block c (c i),matrix g.val r.val j.val*v j)=_
    rw [hr]
    rw [Finset.sum_eq_single (⟨i,rfl⟩ : Block c (c i))]
    · simp [v]
    · intro j _ hji
      exact (hji (Subtype.ext (hi j.val j.property))).elim
    · simp
  have hn : matrix g.val i i ≠ 0 := by
    intro hz
    apply hv
    apply (diagonalFactor c (c i) g).injective
    ext r
    rw [hsum,hz,map_zero]
    rfl
  exact (by decide : ∀ x : ZMod 2,x≠0→x=1) _ hn

private theorem cut_pair_first : cutLabel ({0,1} : Set (Fin 4)) = ![0,1,2,2,2] := by
  ext i
  fin_cases i <;> simp [cutLabel,show (Finset.univ : Finset (Fin 4))={0,1,2,3} from by decide,
    Finset.filter_insert,Finset.filter_singleton]
private theorem cut_pair_middle : cutLabel ({0,3} : Set (Fin 4)) = ![0,1,1,1,2] := by
  ext i
  fin_cases i <;> simp [cutLabel,show (Finset.univ : Finset (Fin 4))={0,1,2,3} from by decide,
    Finset.filter_insert,Finset.filter_singleton]
private theorem cut_pair_last : cutLabel ({2,3} : Set (Fin 4)) = ![0,0,0,1,2] := by
  ext i
  fin_cases i <;> simp [cutLabel,show (Finset.univ : Finset (Fin 4))={0,1,2,3} from by decide,
    Finset.filter_insert,Finset.filter_singleton]

private def adjacentLabel (last : Bool) : Fin 5 → Fin 5 :=
  if last then ![0,0,0,1,2] else ![0,1,2,2,2]
private def scalarRow (last : Bool) : Fin 5 := if last then 3 else 0
private def scalarCol (last : Bool) : Fin 5 := if last then 4 else 1

private theorem adjacent_diagonal (last : Bool) (g : triangularGroup (adjacentLabel last)) :
    matrix g.val (scalarRow last) (scalarRow last)=1 ∧
    matrix g.val (scalarCol last) (scalarCol last)=1 := by
  constructor <;> apply singleton_diagonal
  all_goals cases last <;> decide

private def scalarHom (last : Bool) : triangularGroup (adjacentLabel last) →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (matrix g.val (scalarRow last) (scalarCol last))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change matrixHom 1 (scalarRow last) (scalarCol last)=0
    rw [map_one]
    cases last <;> decide
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change matrixHom (g.val*h.val) (scalarRow last) (scalarCol last)=_
    rw [map_mul,Matrix.mul_apply]
    have hg := adjacent_diagonal last g
    have hh := adjacent_diagonal last h
    have ht (x : triangularGroup (adjacentLabel last)) (i j : Fin 5)
        (hc : adjacentLabel last j < adjacentLabel last i) : matrix x.val i j=0 := x.property hc
    cases last
    · have h20 := ht h 2 1 (by decide)
      have h30 := ht h 3 1 (by decide)
      have h40 := ht h 4 1 (by decide)
      change matrix g.val 0 0=1 ∧ matrix g.val 1 1=1 at hg
      change matrix h.val 0 0=1 ∧ matrix h.val 1 1=1 at hh
      simp [scalarRow,scalarCol,Fin.sum_univ_succ,h20,h30,h40,hg.1,hh.2,add_comm]
    · have h30 := ht g 3 0 (by decide)
      have h31 := ht g 3 1 (by decide)
      have h32 := ht g 3 2 (by decide)
      change matrix g.val 3 3=1 ∧ matrix g.val 4 4=1 at hg
      change matrix h.val 3 3=1 ∧ matrix h.val 4 4=1 at hh
      simp [scalarRow,scalarCol,Fin.sum_univ_succ,h30,h31,h32,hg.1,hh.2,add_comm]

private theorem perfect_hom_trivial {A : Type*} [Group A] [Group.IsPerfect A]
    {E : Type*} [CommGroup E] (f : A →* E) (a : A) : f a=1 := by
  have hh : _root_.commutator A ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top] at hh
  exact hh (mem_top a)

private theorem adjacent_kernel_commute (last : Bool)
    (B : Subgroup (triangularGroup (adjacentLabel last))) [Group.IsPerfect B]
    (g h : (diagonalAction (adjacentLabel last)).ker)
    (hg : g.val ∈ B) (hh : h.val ∈ B) : Commute g.val.val h.val.val := by
  have hs (x : (diagonalAction (adjacentLabel last)).ker) (hx : x.val ∈ B) :
      (matrix x.val.val-1) (scalarRow last) (scalarCol last)=0 := by
    have hz := perfect_hom_trivial ((scalarHom last).comp B.subtype) ⟨x.val,hx⟩
    change Multiplicative.ofAdd (matrix x.val.val (scalarRow last) (scalarCol last))=1 at hz
    have he : matrix x.val.val (scalarRow last) (scalarCol last)=0 := congrArg Multiplicative.toAdd hz
    change matrix x.val.val (scalarRow last) (scalarCol last)-(1 : Matrix _ _ (ZMod 2)) _ _=0
    rw [he]
    cases last <;> decide
  have hprod (x y : (diagonalAction (adjacentLabel last)).ker) (hx : x.val ∈ B) (hy : y.val ∈ B) :
      (matrix x.val.val-1)*(matrix y.val.val-1)=0 := by
    apply strict_pair_zero _ _ _ (strict_difference _ x.val x.property) (strict_difference _ y.val y.property)
    intro i k j hik hkj
    have hpos : (i=scalarRow last ∧ k=scalarCol last) ∨ (k=scalarRow last ∧ j=scalarCol last) := by
      revert hik hkj
      cases last <;> revert i k j <;> decide
    rcases hpos with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (hs x hx)
    · exact Or.inr (hs y hy)
  exact commute_of_zero_differences _ _ (hprod g h hg hh) (hprod h g hh hg)


private theorem middle_corner_commutes (g : triangularGroup (![0,1,1,1,2] : Fin 5 → Fin 5))
    (a : ZMod 2) : matrix g.val*(1+Matrix.single 0 4 a)=(1+Matrix.single 0 4 a)*matrix g.val := by
  have hg0 : matrix g.val 0 0=1 := singleton_diagonal _ g 0 (by decide)
  have hg4 : matrix g.val 4 4=1 := singleton_diagonal _ g 4 (by decide)
  have hcol (i : Fin 5) : matrix g.val i 0 = if i=0 then 1 else 0 := by
    by_cases hi : i=0
    · subst i; simp [hg0]
    · rw [if_neg hi]
      exact g.property (by revert hi; revert i; decide)
  have hrow (j : Fin 5) : matrix g.val 4 j = if j=4 then 1 else 0 := by
    by_cases hj : j=4
    · subst j; simp [hg4]
    · rw [if_neg hj]
      exact g.property (by revert hj; revert j; decide)
  rw [mul_add,add_mul,mul_one,one_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Matrix.single_apply,hcol,hrow]

private theorem middle_kernel_commutator_commutes
    (g h : (diagonalAction (![0,1,1,1,2] : Fin 5 → Fin 5)).ker)
    (k : triangularGroup (![0,1,1,1,2] : Fin 5 → Fin 5)) :
    Commute ⁅g.val.val,h.val.val⁆ k.val := by
  let A := matrix g.val.val-1
  let B := matrix h.val.val-1
  let D := A*B-B*A
  have hprod (X Y : Matrix (Fin 5) (Fin 5) (ZMod 2))
      (hx : Strict (![0,1,1,1,2] : Fin 5 → Fin 5) X)
      (hy : Strict (![0,1,1,1,2] : Fin 5 → Fin 5) Y)
      (i j : Fin 5) (hij : ¬(i=0 ∧ j=4)) : (X*Y) i j=0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro r _
    have hz : (![0,1,1,1,2] : Fin 5 → Fin 5) r ≤ (![0,1,1,1,2] : Fin 5 → Fin 5) i ∨
        (![0,1,1,1,2] : Fin 5 → Fin 5) j ≤ (![0,1,1,1,2] : Fin 5 → Fin 5) r := by
      revert hij
      revert i j r
      decide
    rcases hz with hz | hz
    · rw [hx i r hz,zero_mul]
    · rw [hy r j hz,mul_zero]
  have hD : D=Matrix.single 0 4 (D 0 4) := by
    ext i j
    by_cases hij : i=0 ∧ j=4
    · obtain ⟨rfl,rfl⟩ := hij
      simp
    · have hab := hprod A B (strict_difference _ g.val g.property)
        (strict_difference _ h.val h.property) i j hij
      have hba := hprod B A (strict_difference _ h.val h.property)
        (strict_difference _ g.val g.property) i j hij
      change (A*B) i j-(B*A) i j=_
      rw [hab,hba,sub_self,Matrix.single_apply]
      split_ifs with he
      · exact (hij ⟨he.1.symm,he.2.symm⟩).elim
      · rfl
  apply (slEquivLinear 5).symm.injective
  apply Subtype.ext
  change matrixHom (⁅g.val.val,h.val.val⁆*k.val)=matrixHom (k.val*⁅g.val.val,h.val.val⁆)
  rw [map_mul,map_mul]
  change matrix ⁅g.val.val,h.val.val⁆*matrix k.val=matrix k.val*matrix ⁅g.val.val,h.val.val⁆
  rw [kernel_commutator_matrix _ (by decide)]
  change (1+D)*matrix k.val=matrix k.val*(1+D)
  rw [hD]
  exact (middle_corner_commutes k _).symm


private theorem small_flag_kernel_commute (cuts : Set (Fin m)) (hc : cuts.toFinset.card ≤ 1)
    (g h : (diagonalAction (cutLabel cuts)).ker) : Commute g.val.val h.val.val := by
  have hlo (i : Fin (m+1)) : (cutLabel cuts i).val ≤ 1 := by
    change (Finset.univ.filter (fun k : Fin m => k ∈ cuts ∧ k.val < i.val)).card ≤ 1
    apply (Finset.card_le_card (t := cuts.toFinset) ?_).trans hc
    intro k hk
    exact Set.mem_toFinset.mpr (Finset.mem_filter.mp hk).2.1
  have hp (x y : (diagonalAction (cutLabel cuts)).ker) :
      (matrix x.val.val-1)*(matrix y.val.val-1)=0 := by
    apply strict_pair_zero _ _ _ (strict_difference _ x.val x.property) (strict_difference _ y.val y.property)
    intro i k j hi hj
    have hh := hlo j
    change (cutLabel cuts i).val < (cutLabel cuts k).val at hi
    change (cutLabel cuts k).val < (cutLabel cuts j).val at hj
    omega
  exact commute_of_zero_differences _ _ (hp g h) (hp h g)

private theorem four_cut_small : ∀ s : Finset (Fin 3), 7∣leviOrder s → s.card≤1 := by decide +kernel
private theorem five_cut_patterns : ∀ s : Finset (Fin 4), 7∣leviOrder s →
    s.card≤1 ∨ s={0,1} ∨ s={0,3} ∨ s={2,3} := by decide +kernel

private theorem perfect_flag_kernel_derived_commutes (hm : m=3 ∨ m=4)
    (cuts : Set (Fin m)) (h7 : 7∣leviOrder cuts.toFinset)
    (B : Subgroup (triangularGroup (cutLabel cuts))) [Group.IsPerfect B]
    (g h : (diagonalAction (cutLabel cuts)).ker) (hg : g.val∈B) (hh : h.val∈B)
    (k : B) : Commute ⁅g.val.val,h.val.val⁆ k.val.val := by
  revert B g h
  rcases hm with rfl | rfl
  · intro B hperfect g h hg hh k
    let := hperfect
    rw [(small_flag_kernel_commute cuts (four_cut_small _ h7) g h).commutator_eq]
    exact Commute.one_left _
  · rcases five_cut_patterns _ h7 with hs | hs | hs | hs
    · intro B hperfect g h hg hh k
      let := hperfect
      rw [(small_flag_kernel_commute cuts hs g h).commutator_eq]
      exact Commute.one_left _
    · have he : cuts=({0,1} : Set (Fin 4)) := by
        ext i
        simpa only [Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
          Set.mem_singleton_iff] using (Iff.of_eq (congrArg (fun s : Finset (Fin 4) => i∈s) hs))
      rw [he,cut_pair_first]
      intro B hperfect g h hg hh k
      let := hperfect
      rw [(@adjacent_kernel_commute false B hperfect g h hg hh).commutator_eq]
      exact Commute.one_left _
    · have he : cuts=({0,3} : Set (Fin 4)) := by
        ext i
        simpa only [Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
          Set.mem_singleton_iff] using (Iff.of_eq (congrArg (fun s : Finset (Fin 4) => i∈s) hs))
      rw [he,cut_pair_middle]
      intro B hperfect g h hg hh k
      let := hperfect
      exact middle_kernel_commutator_commutes g h k.val
    · have he : cuts=({2,3} : Set (Fin 4)) := by
        ext i
        simpa only [Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
          Set.mem_singleton_iff] using (Iff.of_eq (congrArg (fun s : Finset (Fin 4) => i∈s) hs))
      rw [he,cut_pair_last]
      intro B hperfect g h hg hh k
      let := hperfect
      rw [(@adjacent_kernel_commute true B hperfect g h hg hh).commutator_eq]
      exact Commute.one_left _

/-- A perfect subgroup normalized by a full binary Sylow in dimension four
or five centralizes the derived subgroup of its own two-core. -/
theorem normalized_perfect_twoCore_derived_central {n : ℕ} (hn : n=4 ∨ n=5)
    (S : Sylow 2 (LinearGroup n)) (B : Subgroup (LinearGroup n)) [Group.IsPerfect B]
    (hSB : (S : Subgroup _) ≤ normalizer (B : Set (LinearGroup n))) (h7 : 7 ∣ Nat.card B) :
    ⁅⁅B.pCoreIn 2,B.pCoreIn 2⁆,B⁆ = ⊥ := by
  let J : Subgroup (LinearGroup n) := B ⊔ (S : Subgroup _)
  have hBJ : B ≤ J := le_sup_left
  have hSJ : (S : Subgroup _) ≤ J := le_sup_right
  have hJB : J ≤ normalizer (B : Set (LinearGroup n)) := sup_le B.le_normalizer hSB
  have hc : B.pCoreIn 2 ≤ J.pCoreIn 2 := pCoreIn_mono_of_normalizes hBJ hJB
  have hJ7 : 7 ∣ Nat.card J := h7.trans (card_dvd_of_le hBJ)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨b,cuts,_,hJ⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S J hSJ
  let P := cutStabilizer b cuts
  have hBP : B ≤ P := by simpa only [hJ] using hBJ
  have hcP : B.pCoreIn 2 ≤ P.pCoreIn 2 := by simpa only [hJ] using hc
  have hP7 : 7 ∣ Nat.card P := by simpa only [hJ] using hJ7
  have h7q : 7 ∣ Nat.card (P ⧸ pCore 2 P) := by
    obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := P)).exists_card_eq
    rw [←(pCore 2 P).card_mul_index,hr] at hP7
    exact ((by decide : Nat.Coprime 7 2).pow_right r).dvd_of_dvd_mul_left hP7
  change 7 ∣ Nat.card (cutStabilizer b cuts ⧸ pCore 2 (cutStabilizer b cuts)) at h7q
  rw [quotient_card] at h7q
  let e := flagCoordinates b cuts
  let D := (B.subgroupOf P).map e.toMonoidHom
  let : Group.IsPerfect (B.subgroupOf P) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBP).symm.toMonoidHom) (subgroupOfEquivOfLe hBP).symm.surjective
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (e.toMonoidHom.subgroupMap_surjective _)
  have hecore : (pCore 2 P).map e.toMonoidHom = (diagonalAction (cutLabel cuts)).ker := by
    rw [pCore_map_iso,ker_diagonalAction_eq_twoCore _ (cutLabel_monotone cuts)]
  have hker (x : P) (hx : x.val ∈ P.pCoreIn 2) : e x ∈ (diagonalAction (cutLabel cuts)).ker := by
    rw [←hecore]
    apply mem_map_of_mem
    obtain ⟨y,hy,he⟩ := hx
    exact (show y=x from Subtype.ext he) ▸ hy
  rw [commutator_eq_bot_iff_le_centralizer]
  apply commutator_le.mpr
  intro g hg h hh k hk
  let gP : P := ⟨g,hBP (B.pCoreIn_le 2 hg)⟩
  let hP : P := ⟨h,hBP (B.pCoreIn_le 2 hh)⟩
  let kP : P := ⟨k,hBP hk⟩
  have hgD : e gP ∈ D := mem_map_of_mem _ (B.pCoreIn_le 2 hg)
  have hhD : e hP ∈ D := mem_map_of_mem _ (B.pCoreIn_le 2 hh)
  have hkD : e kP ∈ D := mem_map_of_mem _ hk
  have hm := perfect_flag_kernel_derived_commutes (by omega : m=3 ∨ m=4) cuts h7q D
    ⟨e gP,hker gP (hcP hg)⟩ ⟨e hP,hker hP (hcP hh)⟩ hgD hhD ⟨e kP,hkD⟩
  have ht : Commute ⁅e gP,e hP⁆ (e kP) := Subtype.ext hm.eq
  have hp : Commute ⁅gP,hP⁆ kP := e.injective (by simpa only [map_mul,map_commutatorElement] using ht.eq)
  exact congrArg Subtype.val hp.symm.eq

end BinaryLinear.SevenFlagCore
