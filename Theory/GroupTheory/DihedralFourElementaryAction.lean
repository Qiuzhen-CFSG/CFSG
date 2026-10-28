module
public import Theory.GroupTheory.DihedralFourElementaryChoices

/-!
# The two invariant maximum elementary subgroups

An actor transitive on the four canonical dihedral enlargements and fixing
one maximum elementary subgroup fixes exactly that choice and its coordinate
complement. Equality of the local intersections transports through every
automorphism, so transitivity makes agreement with the fixed choice constant.

Source application: Aschbacher--Smith, quasithin 10.2.1, printed p.743.
-/

public section
open Subgroup DihedralProductCanonical
namespace DihedralFourChoices

private theorem local_equality_map (f : MulAut Model)
    (b c b' c' : Fin 4 → Bool)
    (hb : (choice b).map f.toMonoidHom = choice b')
    (hc : (choice c).map f.toMonoidHom = choice c') (i : Fin 4) :
    b i = c i ↔ b' (factorAction f i) = c' (factorAction f i) := by
  rw [←choice_inf_gamma_eq_iff,←choice_inf_gamma_eq_iff]
  constructor
  · intro he
    have hh := congrArg (Subgroup.map f.toMonoidHom) he
    simpa only [map_inf _ _ f.toMonoidHom f.injective,hb,hc,map_gamma_factorAction] using hh
  · intro he
    apply map_injective (f := f.toMonoidHom) f.injective
    simpa only [map_inf _ _ f.toMonoidHom f.injective,hb,hc,map_gamma_factorAction] using he

private theorem bool_eq_not_of_ne (a b : Bool) (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

private theorem map_complement_of_fixed (f : MulAut Model) (b : Fin 4 → Bool)
    (hb : (choice b).map f.toMonoidHom = choice b) :
    (choice (fun i => !(b i))).map f.toMonoidHom = choice (fun i => !(b i)) := by
  obtain ⟨c,hc⟩ := eq_choice_of_card ((choice (fun i => !(b i))).map f.toMonoidHom)
    (IsElementaryAbelian.map f.toMonoidHom) (by
      rw [card_map_of_injective f.injective,card_choice])
  rw [hc]
  congr 1
  funext j
  obtain ⟨i,rfl⟩ := (factorAction f).surjective j
  have hne : b (factorAction f i) ≠ c (factorAction f i) := by
    intro he
    have hh := (local_equality_map f b (fun i => !(b i)) b c hb hc i).mpr he
    exact (Bool.not_eq_self (b i)).mp hh.symm
  exact bool_eq_not_of_ne _ _ hne

/-- A transitive actor fixing one largest elementary subgroup fixes precisely
it and its coordinatewise complementary choice. The actor is allowed to mix
central coordinates; only its literal action on the canonical enlargements is used. -/
theorem two_fixed_choices {H : Type*} [Group H] (φ : H →* MulAut Model)
    (htrans : ∀ i j : Fin 4, ∃ h : H, factorAction (φ h) i = j)
    (V : Subgroup Model) (hV : V ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤)
    (hfix : ∀ h : H, V.map (φ h).toMonoidHom = V) :
    ∃ A : Subgroup Model, A ≠ V ∧
      A ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤ ∧
      (∀ h : H, A.map (φ h).toMonoidHom = A) ∧
      (∀ W ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup Model),
        (∀ h : H, W.map (φ h).toMonoidHom = W) → W = V ∨ W = A) := by
  obtain ⟨b,rfl⟩ := (max_iff_choice V).mp hV
  refine ⟨choice (fun i => !(b i)),?_,choice_max _,?_,?_⟩
  · intro he
    have hh := congrFun (choice_injective he) 0
    exact (Bool.not_eq_self (b 0)).mp hh
  · intro h
    exact map_complement_of_fixed (φ h) b (hfix h)
  · intro W hW hWfix
    obtain ⟨c,rfl⟩ := (max_iff_choice W).mp hW
    by_cases he : b 0 = c 0
    · left
      apply congrArg choice
      funext j
      obtain ⟨h,hh⟩ := htrans 0 j
      have heq := (local_equality_map (φ h) b c b c (hfix h) (hWfix h) 0).mp he
      simpa only [hh] using heq.symm
    · right
      apply congrArg choice
      funext j
      obtain ⟨h,hh⟩ := htrans 0 j
      apply bool_eq_not_of_ne
      intro hej
      apply he
      apply (local_equality_map (φ h) b c b c (hfix h) (hWfix h) 0).mpr
      simpa only [hh] using hej

end DihedralFourChoices
