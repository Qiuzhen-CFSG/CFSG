module
public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Theory.SpecificGroups.DihedralProduct.CentralEnlargementModel
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# The sixteen maximum elementary subgroups of four dihedral factors

Every elementary subgroup projects into one of the two elementary four-groups
in each dihedral factor. The sixteen coordinate products have order 256 and
exhaust the maximum family. Their intersections with the four canonical
central enlargements each have order 32 and generate the original subgroup.

Source application: Aschbacher--Smith, quasithin 10.2.1, printed p.743.
-/

public section
open Subgroup SymmetricFourWreath DihedralProductCanonical
namespace DihedralFourChoices
abbrev Model := Fin 4 → D
@[expose] def choice (b : Fin 4 → Bool) : Subgroup Model :=
  Subgroup.pi Set.univ (fun i => plane (b i))
@[simp] theorem mem_choice {b : Fin 4 → Bool} {x : Model} :
    x ∈ choice b ↔ ∀ i, x i ∈ plane (b i) := by
  simp only [choice, mem_pi, Set.mem_univ, forall_const]

private def piSubgroupEquiv {ι : Type*} (H : ι → Subgroup D) :
    Subgroup.pi Set.univ H ≃* (∀ i, H i) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => x i, fun i _ => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem card_choice (b : Fin 4 → Bool) : Nat.card (choice b) = 256 := by
  rw [choice, Nat.card_congr (piSubgroupEquiv _).toEquiv, Nat.card_pi]
  simp only [card_plane, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

instance choice_elementary (b : Fin 4 → Bool) : IsElementaryAbelian 2 (choice b) where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨x.1 i, mem_choice.mp x.2 i⟩ : plane (b i)) ⟨y.1 i, mem_choice.mp y.2 i⟩)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Subtype.ext
    funext i
    exact elemPow_eq_one_of_isElementaryAbelian (x.1 i) (mem_choice.mp x.2 i))

private theorem elementary_plane (A : Subgroup D) (hA : IsElementaryAbelian 2 A) :
    ∃ i, A ≤ plane i := by
  by_cases ht : A ≤ plane true
  · exact ⟨true,ht⟩
  obtain ⟨x,hx,hxt⟩ := SetLike.not_le_iff_exists.mp ht
  refine ⟨false,?_⟩
  intro y hy
  have hlocal : ∀ x y : D, x^2=1 → y^2=1 → x*y=y*x → x∉plane true → y∈plane false := by
    decide +kernel
  let : IsElementaryAbelian 2 A := hA
  exact hlocal x y (elemPow_eq_one_of_isElementaryAbelian x hx)
    (elemPow_eq_one_of_isElementaryAbelian y hy)
    (congrArg Subtype.val (hA.is_comm.comm (⟨x,hx⟩ : A) ⟨y,hy⟩)) hxt

theorem elementary_le_choice (V : Subgroup Model) (hV : IsElementaryAbelian 2 V) :
    ∃ b, V ≤ choice b := by
  have hex i := elementary_plane (V.map (Pi.evalMonoidHom (fun _ : Fin 4 => D) i))
    (hV.map _)
  choose b hb using hex
  exact ⟨b, fun x hx => mem_choice.mpr fun i => hb i (mem_map_of_mem _ hx)⟩

theorem elementary_card_le (V : Subgroup Model) (hV : IsElementaryAbelian 2 V) :
    Nat.card V ≤ 256 := by
  obtain ⟨b,hb⟩ := elementary_le_choice V hV
  exact (card_le_of_le hb).trans (card_choice b).le

theorem eq_choice_of_card (V : Subgroup Model) (hV : IsElementaryAbelian 2 V)
    (hc : Nat.card V = 256) : ∃ b, V = choice b := by
  obtain ⟨b,hb⟩ := elementary_le_choice V hV
  exact ⟨b,eq_of_le_of_card_ge hb (by rw [card_choice,hc])⟩

theorem choice_max (b : Fin 4 → Bool) :
    choice b ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup Model) := by
  refine ⟨le_top,inferInstance,?_⟩
  intro W hW hWe
  simpa only [card_choice] using elementary_card_le W hWe

theorem max_iff_choice (V : Subgroup Model) :
    V ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup Model) ↔
      ∃ b, V = choice b := by
  constructor
  · intro hV
    obtain ⟨b,hb⟩ := elementary_le_choice V hV.2.1
    exact ⟨b,eq_of_le_of_card_ge hb (hV.2.2 _ le_top inferInstance)⟩
  · rintro ⟨b,rfl⟩
    exact choice_max b

private theorem plane_injective : Function.Injective plane := by
  intro b c he
  have hbc : ∀ b c : Bool, (∀ x : D, x ∈ plane b ↔ x ∈ plane c) → b = c := by
    decide +kernel
  exact hbc b c (SetLike.ext_iff.mp he)

theorem choice_injective : Function.Injective choice := by
  intro b c he
  funext i
  apply plane_injective
  ext x
  have hx := SetLike.ext_iff.mp he (Pi.mulSingle i x)
  simpa only [choice, mulSingle_mem_pi, Set.mem_univ, true_implies] using hx

private theorem center_le_plane (b : Bool) : center D ≤ plane b := by
  change ∀ x : D, x ∈ center D → x ∈ plane b
  cases b <;> decide +kernel

@[simp] theorem mem_choice_inf_gamma {b : Fin 4 → Bool} {i : Fin 4} {x : Model} :
    x ∈ choice b ⊓ gamma i ↔ x i ∈ plane (b i) ∧ x ∈ gamma i := by
  constructor
  · rintro ⟨hx,hg⟩
    exact ⟨mem_choice.mp hx i,hg⟩
  · rintro ⟨hx,hg⟩
    refine ⟨mem_choice.mpr ?_,hg⟩
    intro j
    by_cases hji : j=i
    · simpa only [hji] using hx
    · exact center_le_plane (b j) (hg j hji)

private def choiceGammaEquiv (b : Fin 4 → Bool) (i : Fin 4) :
    (choice b ⊓ gamma i : Subgroup Model) ≃* plane (b i) × Remainder i where
  toFun x := (⟨x.val i,(mem_choice_inf_gamma.mp x.property).1⟩,
    fun j => ⟨x.val j,x.property.2 j j.property⟩)
  invFun p := ⟨fun j => if h : j=i then p.1.val else (p.2 ⟨j,h⟩).val,
    mem_choice_inf_gamma.mpr ⟨by simp,by
      intro j hji
      simp only [dif_neg hji]
      exact (p.2 ⟨j,hji⟩).property⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases hji : j=i <;> simp [hji]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext; simp
    · funext j
      apply Subtype.ext
      simp [j.property]
  map_mul' _ _ := rfl

theorem card_choice_inf_gamma (b : Fin 4 → Bool) (i : Fin 4) :
    Nat.card (choice b ⊓ gamma i : Subgroup Model) = 32 := by
  rw [Nat.card_congr (choiceGammaEquiv b i).toEquiv,Nat.card_prod,card_plane,remainder_card]

private theorem single_mem_gamma (i : Fin 4) (x : D) :
    (Pi.mulSingle i x : Model) ∈ gamma i := by
  intro j hji
  simp [hji]

theorem iSup_choice_inf_gamma (b : Fin 4 → Bool) :
    (⨆ i, choice b ⊓ gamma i) = choice b := by
  apply le_antisymm (iSup_le fun i => inf_le_left)
  change Subgroup.pi Set.univ (fun i => plane (b i)) ≤ _
  apply pi_le_iff.mpr
  intro i
  rintro x ⟨d,hd,rfl⟩
  apply (le_iSup (fun i => choice b ⊓ gamma i) i)
  exact mem_choice_inf_gamma.mpr ⟨by simpa using hd,single_mem_gamma i d⟩

theorem choice_inf_gamma_eq_iff (b c : Fin 4 → Bool) (i : Fin 4) :
    choice b ⊓ gamma i = choice c ⊓ gamma i ↔ b i = c i := by
  constructor
  · intro he
    apply plane_injective
    ext x
    have hx := SetLike.ext_iff.mp he (Pi.mulSingle i x)
    simpa only [mem_choice_inf_gamma,Pi.mulSingle_eq_same,single_mem_gamma,and_true] using hx
  · intro he
    ext x
    simp only [mem_choice_inf_gamma,he]

theorem card_inf_gamma_of_elementary_order (V : Subgroup Model)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 256) (i : Fin 4) :
    Nat.card (V ⊓ gamma i : Subgroup Model) = 32 := by
  obtain ⟨b,rfl⟩ := eq_choice_of_card V hV hc
  exact card_choice_inf_gamma b i

theorem iSup_inf_gamma_of_elementary_order (V : Subgroup Model)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 256) :
    (⨆ i, V ⊓ gamma i) = V := by
  obtain ⟨b,rfl⟩ := eq_choice_of_card V hV hc
  exact iSup_choice_inf_gamma b

theorem card_maximum_family :
    Nat.card {V : Subgroup Model // V ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤} = 16 := by
  let f : (Fin 4 → Bool) → {V : Subgroup Model // V ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤} :=
    fun b => ⟨choice b,choice_max b⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b c he
      exact choice_injective (congrArg Subtype.val he)
    · rintro ⟨V,hV⟩
      obtain ⟨b,hb⟩ := (max_iff_choice V).mp hV
      exact ⟨b,Subtype.ext hb.symm⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_fun]
  norm_num

variable {H : Type*} [Group H]
private theorem map_transported_gamma (e : H ≃* Model) (i : Fin 4) :
    (transportedGamma e i).map e.toMonoidHom = gamma i := by
  rw [transportedGamma,map_map]
  have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Model := by ext; simp
  rw [he,map_id]

theorem card_inf_transportedGamma (e : H ≃* Model) (V : Subgroup H)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 256) (i : Fin 4) :
    Nat.card (V ⊓ transportedGamma e i : Subgroup H) = 32 := by
  have hc' : Nat.card (V.map e.toMonoidHom) = 256 := by
    rw [card_map_of_injective e.injective,hc]
  have hh := card_inf_gamma_of_elementary_order (V.map e.toMonoidHom) (hV.map _) hc' i
  rw [←map_transported_gamma e i,←map_inf _ _ _ e.injective,
    card_map_of_injective e.injective] at hh
  exact hh

theorem iSup_inf_transportedGamma (e : H ≃* Model) (V : Subgroup H)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 256) :
    (⨆ i, V ⊓ transportedGamma e i) = V := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_iSup]
  simp_rw [map_inf _ _ e.toMonoidHom e.injective,map_transported_gamma]
  apply iSup_inf_gamma_of_elementary_order _ (hV.map _)
  rw [card_map_of_injective e.injective,hc]

end DihedralFourChoices
