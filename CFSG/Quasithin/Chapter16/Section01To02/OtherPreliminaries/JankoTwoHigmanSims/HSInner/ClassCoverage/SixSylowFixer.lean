module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementAction
public import Theory.GroupTheory.DihedralPresentation
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComponentRecognition
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Enumeration
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Marking
/-!
# A central-class involution in the marked HS component Sylow fixer

Two explicit words generate a Sylow two-subgroup of the actual A₆ subgroup
D. Reusing the checked 1440-element enumeration of H, commuting on only
two letters leaves four candidates. Every nonidentity candidate or its
product with t fixes a letter, so involution-class coverage places that
involution in the central class. All finite equalities are kernel checked.

These marked calculations retain the original t, H and D. They supply
the intrinsic selection step for the Higman–Sims case of E.6.23.
Source: GLS3 Table 5.3m; Aschbacher–Smith E.6.23, p.254, and 16.1.5(10),
p.1172. Discovery data are retained with the source campaign evidence.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.SylowFixerCertificate
open Sporadic.LeechRelated.HS Theory.GroupTheory Subgroup
set_option maxRecDepth 10000

def sylowWord : Fin 2 → List (Fin 4) := ![[1], [0, 0, 1, 2, 2]]
def sylowGenerator (i : Fin 2) : Carrier := evalWord dLetter (sylowWord i)
def sylowCode : Fin 2 → ℕ := ![1303627481187934755557311436521888720965161342890626410385963713835903024646672517184280584537585760380646457107253893970740224765622675922813131290643543237820228330339564597743451780278643407120247992268914872, 90782189218292970200228989724885074110386095086977505591089329928007724536254654244129964960920912679006510076128756582790361644967420487353817545559345020753075765104357992645673271066026296138812823109681373]
def sylowValue (i : Fin 2) (p : Fin 100) : Fin 100 :=
  ⟨(sylowCode i >>> (7 * p.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

theorem value_spec : ∀ i p, inclusion (sylowGenerator i) p = sylowValue i p := by
  apply Certificate.allFin
  decide +kernel

theorem candidate_screen : ∀ i : Fin 1440,
    (∀ j : Fin 2, ∀ p : Fin 2,
      ComplementCertificate.value i (sylowValue j ⟨p.val, by omega⟩) =
        sylowValue j (ComplementCertificate.value i ⟨p.val, by omega⟩)) →
      i = 0 ∨ i = 51 ∨ i = 600 ∨ i = 1302 := by
  apply Certificate.allFin
  decide +kernel
theorem complement_fixer_cases (x : Carrier) (hx : x ∈ H)
    (hc : ∀ i, Commute x (sylowGenerator i)) :
    x = 1 ∨ x = ComplementCertificate.element 51 ∨
      x = ComplementCertificate.element 600 ∨ x = ComplementCertificate.element 1302 := by
  obtain ⟨i, rfl⟩ := ComplementCertificate.element_cover x hx
  have hi := candidate_screen i (by
    intro j p
    have he := congrArg (fun x : Carrier => inclusion x ⟨p.val, by omega⟩) (hc j).eq
    simpa only [map_mul, Equiv.Perm.mul_apply, ComplementCertificate.value_spec, value_spec] using he)
  rcases hi with rfl | rfl | rfl | rfl
  · exact Or.inl ComplementCertificate.element_zero
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem complement_nontrivial_fixer_has_fixed_letter (x : Carrier) (hx : x ∈ H)
    (hc : ∀ i, Commute x (sylowGenerator i)) (hne : x ≠ 1) :
    inclusion x 1 = 1 ∨ inclusion (x * t) 1 = 1 := by
  rcases complement_fixer_cases x hx hc with he | rfl | rfl | rfl
  · exact (hne he).elim
  · right; decide +kernel
  · right; decide +kernel
  · left; decide +kernel

theorem generator_square : ∀ i, sylowGenerator i ^ 2 = 1 := by
  intro i
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ i : Fin 2, ∀ p : Fin 100,
      inclusion (sylowGenerator i ^ 2) p = p := by
    apply Certificate.allFin
    decide +kernel
  exact h i

theorem product_four : (sylowGenerator 1 * sylowGenerator 0) ^ 4 = 1 := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  apply Certificate.allFin
  decide +kernel

def baseGroup : Subgroup Carrier := closure {sylowGenerator 0, sylowGenerator 1}

theorem baseGroup_le_D : baseGroup ≤ D := by
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact dWord_mem _
  · rw [Set.mem_singleton_iff.mp hx]
    exact dWord_mem _

def smallElement (i : Fin 8) : Carrier :=
  (sylowGenerator 1 * sylowGenerator 0) ^ (i.val / 2) * sylowGenerator 0 ^ (i.val % 2)

theorem smallElement_mem (i : Fin 8) : smallElement i ∈ baseGroup := by
  have h0 : sylowGenerator 0 ∈ baseGroup := subset_closure (by simp)
  have h1 : sylowGenerator 1 ∈ baseGroup := subset_closure (by simp)
  exact baseGroup.mul_mem (baseGroup.pow_mem (baseGroup.mul_mem h1 h0) _)
    (baseGroup.pow_mem h0 _)

theorem smallElement_injective : Function.Injective smallElement := by
  have h : Function.Injective (fun i : Fin 8 =>
      (inclusion (smallElement i) 0, inclusion (smallElement i) 1)) := by
    decide +kernel
  intro i j he
  exact h (congrArg (fun x : Carrier => (inclusion x 0, inclusion x 1)) he)

theorem baseGroup_card : Nat.card baseGroup = 8 := by
  apply le_antisymm
  · exact (closure_pair_finite_card_le_of_involutions (by decide : 0 < 4)
      (sylowGenerator 0) (sylowGenerator 1) (generator_square 0) (generator_square 1)
      product_four).2
  · let f : Fin 8 → baseGroup := fun i => ⟨smallElement i, smallElement_mem i⟩
    have hi : Function.Injective f := fun i j he => smallElement_injective (congrArg Subtype.val he)
    simpa using Nat.card_le_card_of_injective f hi

noncomputable def baseSylow : Sylow 2 D := by
  have hp : Nat.card (baseGroup.subgroupOf D) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe baseGroup_le_D).toEquiv).trans baseGroup_card
  have hD : Nat.card D = 360 := by
    obtain ⟨e⟩ := D_equiv_A6
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (alternatingGroup (Fin 6)) = 360
    rw [nat_card_alternatingGroup]
    norm_num
  refine (IsPGroup.of_card (show Nat.card (baseGroup.subgroupOf D) = 2 ^ 3 from hp)).toSylow ?_
  have hh := (baseGroup.subgroupOf D).card_mul_index
  rw [hp, hD] at hh
  have hi : (baseGroup.subgroupOf D).index = 45 := by omega
  rw [hi]
  decide

theorem central_class_of_fixed_letter (x : Carrier) (hx : orderOf x = 2)
    (p : Fin 100) (hp : inclusion x p = p) :
    IsConj EvenLocalCandidates.e0 x := by
  rcases involution_classes x hx with h | h
  · exact h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    have he : t * g⁻¹ = g⁻¹ * x := by rw [← hg]; group
    have hh := congrArg (fun y : Carrier => inclusion y p) he
    simp only [map_mul, Equiv.Perm.mul_apply, hp] at hh
    exact (t_fixedPointFree _ hh).elim

theorem t_not_mem_H : t ∉ H := by
  intro ht
  have hc : t ∈ centralizer (D : Set Carrier) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mp (D_le_centralizer hd)
  have ht1 : t = 1 := mem_bot.mp (H_inf_centralizer_D ▸ ⟨ht, hc⟩)
  have hh := t_order
  rw [ht1, orderOf_one] at hh
  contradiction

theorem complement_fixer_central_class (x : Carrier) (hx : x ∈ H)
    (hc : ∀ i, Commute x (sylowGenerator i)) (hx2 : orderOf x = 2) :
    IsConj EvenLocalCandidates.e0 x ∨ IsConj EvenLocalCandidates.e0 (x * t) := by
  have hn : x ≠ 1 := by intro he; rw [he, orderOf_one] at hx2; contradiction
  rcases complement_nontrivial_fixer_has_fixed_letter x hx hc hn with hp | hp
  · exact Or.inl (central_class_of_fixed_letter x hx2 1 hp)
  · right
    have ht2 : (x * t) ^ 2 = 1 := by
      rw [(show Commute x t from mem_centralizer_singleton_iff.mp (H_le_centralizer hx)).mul_pow,
        (orderOf_eq_prime_iff.mp hx2).1, (orderOf_eq_prime_iff.mp t_order).1, one_mul]
    have hxt : x * t ≠ 1 := by
      intro he
      have ht : t = x⁻¹ := eq_inv_iff_mul_eq_one.mpr ((mem_centralizer_singleton_iff.mp (H_le_centralizer hx)).symm.trans he)
      exact t_not_mem_H (ht.symm ▸ H.inv_mem hx)
    exact central_class_of_fixed_letter (x * t) (orderOf_eq_prime ht2 hxt) 1 hp

/-- Each certified Sylow generator belongs to the exact alternating subgroup D. -/
theorem sylowGenerator_mem_D (i : Fin 2) : sylowGenerator i ∈ D := dWord_mem _

/-- The original carrier words belong to the published Sylow subgroup of D. -/
theorem sylowGenerator_mem_baseSylow (i : Fin 2) :
    (⟨sylowGenerator i, sylowGenerator_mem_D i⟩ : D) ∈ baseSylow := by
  change sylowGenerator i ∈ baseGroup
  fin_cases i
  · exact subset_closure (by simp)
  · exact subset_closure (by simp)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.SylowFixerCertificate
