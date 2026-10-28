module
public import Theory.Mathieu.M12.ExceptionalParabolics
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Recognition of the split M₁₂ parabolic from source relations

The fifteen power and conjugation relations of Goldschmidt's split endpoint
bound every generated finite realization by 192. Four successive normalized
subgroup products supply the bound. Applied to the paired generators in a
direct product, it identifies two order-192 realizations without presupposing
an isomorphism or a complete multiplication table.

The five concrete M₁₂ generators satisfy these relations and generate its
natural-four normalizer, as shown using the existing word certificate.
The final theorem recognizes an abstract endpoint from its source generators,
relations, and order. Source: Goldschmidt, *Automorphisms of trivalent graphs*
(1980), (3.6), (3.8), pp.389–390, and the final paragraph of (6.12), p.406.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
open Subgroup

/-- The five generators and actions defining the split endpoint in Gol80 (3.8).
Conjugation is written on the left throughout. -/
structure SplitRelations {G : Type*} [Group G] (a b x s t : G) : Prop where
  a_four : a ^ 4 = 1
  b_four : b ^ 4 = 1
  ab : Commute a b
  x_three : x ^ 3 = 1
  s_two : s ^ 2 = 1
  t_two : t ^ 2 = 1
  sx : s * x * s⁻¹ = x⁻¹
  tx : Commute t x
  ts : Commute t s
  xa : x * a * x⁻¹ = b
  xb : x * b * x⁻¹ = (a * b)⁻¹
  sa : s * a * s⁻¹ = b
  sb : s * b * s⁻¹ = a
  ta : t * a * t⁻¹ = a⁻¹
  tb : t * b * t⁻¹ = b⁻¹

variable {G : Type*} [Group G] [Finite G]

private theorem card_join_le (A B : Subgroup G) (hn : B ≤ normalizer A) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hn]
  exact Nat.le_mul_of_pos_left _ Nat.card_pos

private theorem normalizes_pair {g a b : G}
    (ha : g * a * g⁻¹ ∈ closure ({a,b} : Set G))
    (hb : g * b * g⁻¹ ∈ closure ({a,b} : Set G)) :
    g ∈ normalizer (closure ({a,b} : Set G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro w ⟨u, hu, rfl⟩
    rcases hu with rfl | rfl
    · exact ha
    · exact hb
  · exact (card_map_of_injective (MulAut.conj g).injective).ge

private theorem normalizes_zpowers {g a : G} (h : g * a * g⁻¹ ∈ zpowers a) :
    g ∈ normalizer (zpowers a : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr h
  · exact (card_map_of_injective (MulAut.conj g).injective).ge

omit [Finite G] in
private theorem card_cyclic_le {g : G} {n : ℕ} (hn : 0 < n) (hg : g ^ n = 1) :
    Nat.card (zpowers g) ≤ n := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one hg)

/-- Every finite realization of the split endpoint relations has order at most
192 on its generated subgroup. No uniqueness or faithfulness is assumed. -/
theorem SplitRelations.card_le {a b x s t : G} (r : SplitRelations a b x s t) :
    Nat.card (closure ({a,b,x,s,t} : Set G)) ≤ 192 := by
  let J := closure ({a,b} : Set G)
  let D := closure ({x,s} : Set G)
  have hJ : J = zpowers a ⊔ zpowers b := by
    dsimp only [J]
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hD : D = zpowers x ⊔ zpowers s := by
    dsimp only [D]
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hbN : b ∈ normalizer (zpowers a : Set G) := normalizes_zpowers (by
    rw [r.ab.symm.eq, mul_inv_cancel_right]
    exact mem_zpowers a)
  have hsN : s ∈ normalizer (zpowers x : Set G) := normalizes_zpowers (by
    rw [r.sx]
    exact inv_mem (mem_zpowers x))
  have hJcard : Nat.card J ≤ 16 := by
    rw [hJ]
    exact (card_join_le _ _ (zpowers_le.mpr hbN)).trans
      ((Nat.mul_le_mul (card_cyclic_le (by decide) r.a_four)
        (card_cyclic_le (by decide) r.b_four)).trans (by decide))
  have hDcard : Nat.card D ≤ 6 := by
    rw [hD]
    exact (card_join_le _ _ (zpowers_le.mpr hsN)).trans
      ((Nat.mul_le_mul (card_cyclic_le (by decide) r.x_three)
        (card_cyclic_le (by decide) r.s_two)).trans (by decide))
  have htN : t ∈ normalizer (D : Set G) := normalizes_pair (by
    rw [r.tx.eq, mul_inv_cancel_right]
    exact subset_closure (by simp)) (by
    rw [r.ts.eq, mul_inv_cancel_right]
    exact subset_closure (by simp))
  have hDTcard : Nat.card (D ⊔ zpowers t : Subgroup G) ≤ 12 :=
    (card_join_le _ _ (zpowers_le.mpr htN)).trans
      ((Nat.mul_le_mul hDcard (card_cyclic_le (by decide) r.t_two)).trans (by decide))
  have hxJ : x ∈ normalizer (J : Set G) := normalizes_pair (by
    rw [r.xa]; exact subset_closure (by simp)) (by
    rw [r.xb]; exact inv_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp))))
  have hsJ : s ∈ normalizer (J : Set G) := normalizes_pair (by
    rw [r.sa]; exact subset_closure (by simp)) (by
    rw [r.sb]; exact subset_closure (by simp))
  have htJ : t ∈ normalizer (J : Set G) := normalizes_pair (by
    rw [r.ta]; exact inv_mem (subset_closure (by simp))) (by
    rw [r.tb]; exact inv_mem (subset_closure (by simp)))
  have hn : D ⊔ zpowers t ≤ normalizer (J : Set G) := by
    refine sup_le ((closure_le _).mpr ?_) (zpowers_le.mpr htJ)
    rintro w (rfl | rfl)
    · exact hxJ
    · exact hsJ
  have he : closure ({a,b,x,s,t} : Set G) = J ⊔ (D ⊔ zpowers t) := by
    dsimp only [J, D]
    rw [zpowers_eq_closure, ← Subgroup.closure_union, ← Subgroup.closure_union]
    congr 1
    ext w
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [he]
  exact (card_join_le _ _ hn).trans
    ((Nat.mul_le_mul hJcard hDTcard).trans (by decide))

variable {H : Type*} [Group H] [Finite H]

omit [Finite G] [Finite H] in
theorem SplitRelations.prod {a b x s t : G} {a' b' x' s' t' : H}
    (r : SplitRelations a b x s t) (q : SplitRelations a' b' x' s' t') :
    SplitRelations (a,a') (b,b') (x,x') (s,s') (t,t') where
  a_four := Prod.ext r.a_four q.a_four
  b_four := Prod.ext r.b_four q.b_four
  ab := Prod.ext r.ab.eq q.ab.eq
  x_three := Prod.ext r.x_three q.x_three
  s_two := Prod.ext r.s_two q.s_two
  t_two := Prod.ext r.t_two q.t_two
  sx := Prod.ext r.sx q.sx
  tx := Prod.ext r.tx.eq q.tx.eq
  ts := Prod.ext r.ts.eq q.ts.eq
  xa := Prod.ext r.xa q.xa
  xb := Prod.ext r.xb q.xb
  sa := Prod.ext r.sa q.sa
  sb := Prod.ext r.sb q.sb
  ta := Prod.ext r.ta q.ta
  tb := Prod.ext r.tb q.tb

/-- Two groups of order192 generated by the split endpoint relations are
isomorphic. The order bound is applied in their direct product. -/
theorem SplitRelations.equiv_of_card {a b x s t : G} {a' b' x' s' t' : H}
    (r : SplitRelations a b x s t) (q : SplitRelations a' b' x' s' t')
    (hgen : closure ({a,b,x,s,t} : Set G) = ⊤)
    (hgen' : closure ({a',b',x',s',t'} : Set H) = ⊤)
    (hcard : Nat.card G = 192) (hcard' : Nat.card H = 192) :
    Nonempty (G ≃* H) := by
  let D := closure ({(a,a'),(b,b'),(x,x'),(s,s'),(t,t')} : Set (G × H))
  let f : D →* G := (MonoidHom.fst G H).domRestrict D
  let g : D →* H := (MonoidHom.snd G H).domRestrict D
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    dsimp only [f]
    rw [MonoidHom.domRestrict_range]
    dsimp only [D]
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_fst, Prod.fst] using hgen
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    dsimp only [g]
    rw [MonoidHom.domRestrict_range]
    dsimp only [D]
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_snd, Prod.snd] using hgen'
  have hd : Nat.card D ≤ 192 := (r.prod q).card_le
  let ef := MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (by simpa only [hcard] using hd))
  let eg := MulEquiv.ofBijective g (hg.bijective_of_nat_card_le (by simpa only [hcard'] using hd))
  exact ⟨ef.symm.trans eg⟩

private theorem leftJ_mem : leftJ ∈ secondParabolic :=
  core_le_secondParabolic ((mem_core _).mpr ⟨.xa 0,.a 0,by decide +kernel⟩)

private theorem leftI_mem : leftI ∈ secondParabolic :=
  core_le_secondParabolic ((mem_core _).mpr ⟨.a 1,.a 0,by decide +kernel⟩)

private theorem rightI_mem : rightI ∈ secondParabolic :=
  core_le_secondParabolic ((mem_core _).mpr ⟨.a 0,.a 1,by decide +kernel⟩)

/-- First order-four source generator. -/
def splitA : secondParabolic := ⟨leftJ,leftJ_mem⟩

/-- Second order-four source generator. -/
def splitB : secondParabolic :=
  ⟨movingActor * leftJ * movingActor⁻¹,
    mul_mem (mul_mem movingActor_mem leftJ_mem) (inv_mem movingActor_mem)⟩

/-- The cubic complement actor. -/
def splitX : secondParabolic := ⟨movingActor,movingActor_mem⟩

/-- The reflection interchanging the two order-four generators. -/
def splitS : secondParabolic :=
  ⟨leftI ^ 2 * movingActor * rightI,
    mul_mem (mul_mem (pow_mem leftI_mem _) movingActor_mem) rightI_mem⟩

/-- The central complement involution inverting the order-four subgroup. -/
def splitT : secondParabolic :=
  ⟨leftJ * leftI * rightI, mul_mem (mul_mem leftJ_mem leftI_mem) rightI_mem⟩

theorem split_relations : SplitRelations splitA splitB splitX splitS splitT where
  a_four := by apply Subtype.ext; decide +kernel
  b_four := by apply Subtype.ext; decide +kernel
  ab := by change splitA * splitB = splitB * splitA; apply Subtype.ext; decide +kernel
  x_three := by apply Subtype.ext; decide +kernel
  s_two := by apply Subtype.ext; decide +kernel
  t_two := by apply Subtype.ext; decide +kernel
  sx := by apply Subtype.ext; decide +kernel
  tx := by change splitT * splitX = splitX * splitT; apply Subtype.ext; decide +kernel
  ts := by change splitT * splitS = splitS * splitT; apply Subtype.ext; decide +kernel
  xa := by apply Subtype.ext; decide +kernel
  xb := by apply Subtype.ext; decide +kernel
  sa := by apply Subtype.ext; decide +kernel
  sb := by apply Subtype.ext; decide +kernel
  ta := by apply Subtype.ext; decide +kernel
  tb := by apply Subtype.ext; decide +kernel

private def splitGenerator (i : Fin 5) : secondParabolic :=
  ![splitA,splitB,splitX,splitS,splitT] i

private def splitEvaluate : List (Fin 5) → secondParabolic
  | [] => 1
  | i :: w => splitGenerator i * splitEvaluate w

private def oldGeneratorWord (i : Fin 5) : List (Fin 5) :=
  ![[0,3,2,1,1,4], [0], [3,2,1,1], [0,1,1], [2]] i

private theorem oldGenerator_eq_word (i : Fin 5) :
    SylowEnumeration.localGenerator i = (splitEvaluate (oldGeneratorWord i) : M12) := by
  fin_cases i <;> decide +kernel

/-- The five source generators account for every element of the actual second
parabolic, using its existing short-word certificate. -/
theorem split_generation :
    closure ({splitA,splitB,splitX,splitS,splitT} : Set secondParabolic) = ⊤ := by
  let C := closure ({splitA,splitB,splitX,splitS,splitT} : Set secondParabolic)
  have hs (i : Fin 5) : splitGenerator i ∈ C := by
    fin_cases i <;> exact subset_closure (by simp [splitGenerator])
  have hw (w : List (Fin 5)) : splitEvaluate w ∈ C := by
    induction w with
    | nil => exact C.one_mem
    | cons i w ih => exact C.mul_mem (hs i) ih
  have ho (i : Fin 5) : SylowEnumeration.localGenerator i ∈ C.map secondParabolic.subtype := by
    rw [oldGenerator_eq_word]
    exact mem_map.mpr ⟨_,hw _,rfl⟩
  have hold (w : List (Fin 5)) : SylowEnumeration.localWord w ∈ C.map secondParabolic.subtype := by
    induction w with
    | nil => exact (C.map secondParabolic.subtype).one_mem
    | cons i w ih => exact (C.map secondParabolic.subtype).mul_mem (ho i) ih
  apply top_unique
  intro g _
  have hm : (g : M12).val ∈ SylowEnumeration.wordCarrier :=
    (SylowEnumeration.mem_wordCarrier_iff _).mpr
      ⟨(SylowEnumeration.mem_M12_iff_preservesBlocks _).mp g.val.property,
        (SylowEnumeration.mem_secondParabolic_iff _).mp g.property⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  have hi' : SylowEnumeration.wordElement i = (g : M12) := Subtype.ext hi
  have hg : (g : M12) ∈ C.map secondParabolic.subtype := hi' ▸ hold _
  obtain ⟨u, hu, he⟩ := mem_map.mp hg
  exact (Subtype.ext he : u = g) ▸ hu

/-- Recognition of the opposite source endpoint by its standard split
extension generators and order. -/
theorem secondParabolic_equiv_of_split_relations
    {G : Type*} [Group G] [Finite G] (a b x s t : G)
    (r : SplitRelations a b x s t)
    (hgen : closure ({a,b,x,s,t} : Set G) = ⊤) (hcard : 192 ≤ Nat.card G) :
    Nonempty (G ≃* secondParabolic) := by
  have hbound : Nat.card G ≤ 192 := by
    simpa only [hgen, card_top] using r.card_le
  exact r.equiv_of_card split_relations hgen split_generation
    (Nat.le_antisymm hbound hcard) card_secondParabolic

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
