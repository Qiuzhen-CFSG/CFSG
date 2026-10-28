module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Nonstandard
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.WingClassification

/-!
# Maximum small movers in an arbitrary Sp4(4) radical

Every small mover in a subgroup T of the standard Sylow group is either
trivial, a full transvection root, a large subgroup of the plane radical,
or one of the five plane-fixing subgroups in the point radical. Two distinct
maximum-order movers force T to equal the point radical: the mixed
commutator calculation excludes every element outside it, and two distinct
plane groups generate it. Hence the maximum family then has exactly five
members and generates T.

In the unique-member case the source exclusion of products of transvection
roots, together with nontriviality, forces order at least sixteen. The
chosen parabolic marking is kept separate, since arbitrary fixed labels do
not satisfy the source's maximizing choice.

Source: Meierfrankenfeld–Stellmacher (1993), (5.0), (5.1), and (5.4), printed
pp.912–915. No normality, F4-linearity, or full-Sylow assumption is made on T.
-/

@[expose] public section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

def Small (E : Subgroup (unipotent (F := F))) : Prop :=
  movingIndex E ≤ Nat.card E ∧ movingIndex E ≤ 16

def Maximal (T : Subgroup (unipotent (F := F))) : Set (Subgroup (unipotent (F := F))) :=
  {E | E ≤ T ∧ Small E ∧ ∀ A, A ≤ T → Small A → Nat.card A ≤ Nat.card E}

noncomputable def join (T : Subgroup (unipotent (F := F))) : Subgroup (unipotent (F := F)) :=
  sSup (Maximal T)

theorem small_finitePlane (hF : Nat.card F=4) (l : F) : Small (finitePlane l) := by
  norm_num [Small,movingIndex_finitePlane hF,card_finitePlane,hF]

theorem small_of_le_wing_of_large (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hwing : E ≤ wing true) (hlarge : 16≤Nat.card E) :
    Small E := by
  have hm := movingIndex_le_field_sq_of_le_wing E hwing
  norm_num [hF] at hm
  exact ⟨hm.trans hlarge,hm⟩

theorem small_classification_nonstandard (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hE : Small E) :
    E ≤ wing true ∨ ∃ l : F, E=finitePlane l := by
  by_cases hwing : E ≤ wing true
  · exact Or.inl hwing
  · exact Or.inr (eq_finitePlane_of_small_not_le_wing hF E hE.1 hE.2 hwing)

omit [CharP F 2] [Finite F] in
theorem maximal_card_eq {T E A : Subgroup (unipotent (F := F))}
    (hE : E ∈ Maximal T) (hA : A ∈ Maximal T) : Nat.card E=Nat.card A :=
  le_antisymm (hA.2.2 E hE.1 hE.2.1) (hE.2.2 A hA.1 hA.2.1)

omit [CharP F 2] in
theorem maximal_eq_of_le {T E A : Subgroup (unipotent (F := F))}
    (hE : E ∈ Maximal T) (hA : A ≤ T) (hsmall : Small A) (hle : E ≤ A) : E=A :=
  eq_of_le_of_card_ge hle (hE.2.2 A hA hsmall)

theorem le_point_wing_of_maximal_finitePlane (hF : Nat.card F=4)
    (T : Subgroup (unipotent (F := F))) (l : F) (hmax : finitePlane l ∈ Maximal T) :
    T ≤ wing false := by
  apply le_point_wing_of_plane_and_card_bound T l hmax.1
  by_contra hn
  have hlarge : 16 ≤ Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) := by
    have hn' : ¬ Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) ≤ 16 := by
      simpa only [hF,show (4:ℕ)^2=16 by norm_num] using hn
    omega
  have hs := small_of_le_wing_of_large hF (T ⊓ wing true) inf_le_right hlarge
  have hbound := hmax.2.2 _ inf_le_left hs
  rw [card_finitePlane] at hbound
  exact hn hbound

theorem maximal_large_wing_eq_inf (hF : Nat.card F=4)
    {T E : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hwing : E ≤ wing true) (hlarge : 16≤Nat.card E) : E=T ⊓ wing true := by
  have hle : E ≤ T ⊓ wing true := le_inf hE.1 hwing
  have hc : 16≤Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) :=
    hlarge.trans (card_le_of_le hle)
  exact maximal_eq_of_le hE inf_le_left (small_of_le_wing_of_large hF _ inf_le_right hc) hle

theorem small_plane (hF : Nat.card F=4) (s : Option F) : Small (plane s) := by
  cases s with
  | none =>
    apply small_of_le_wing_of_large hF _
    · exact center_le_wings.trans inf_le_right
    · rw [card_plane,hF]; norm_num
  | some s => exact small_finitePlane hF s

theorem small_card_le_sixteen_in_point_wing (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hsmall : Small E) (hpoint : E ≤ wing false) :
    Nat.card E ≤ 16 := by
  rcases small_classification_nonstandard hF E hsmall with hwing | ⟨l,rfl⟩
  · have hcenter : E ≤ center (unipotent (F := F)) := (wings_inf (F := F)) ▸ le_inf hpoint hwing
    have hc := card_le_of_le hcenter
    norm_num [card_center,hF] at hc
    exact hc
  · norm_num [card_finitePlane,hF]

theorem maximal_point_wing_iff (hF : Nat.card F=4) (E : Subgroup (unipotent (F := F))) :
    E ∈ Maximal (wing false) ↔ ∃ s : Option F, E=plane s := by
  constructor
  · intro hE
    have hplane := small_plane hF none
    have hlarge : 16 ≤ Nat.card E := by
      have hh := hE.2.2 (plane none) (plane_le_wing none) hplane
      norm_num [plane,card_center,hF] at hh
      exact hh
    rcases small_classification_nonstandard hF E hE.2.1 with hwing | ⟨l,rfl⟩
    · refine ⟨none,eq_of_le_of_card_ge ?_ ?_⟩
      · change E ≤ center (unipotent (F := F))
        exact (wings_inf (F := F)) ▸ le_inf hE.1 hwing
      · simpa [plane,card_center,hF] using hlarge
    · exact ⟨some l,rfl⟩
  · rintro ⟨s,rfl⟩
    refine ⟨plane_le_wing s,small_plane hF s,?_⟩
    intro A hA hsmall
    rw [card_plane,hF]
    norm_num
    exact small_card_le_sixteen_in_point_wing hF A hsmall hA

theorem maximal_point_wing_eq_range (hF : Nat.card F=4) :
    Maximal (wing (F := F) false)=Set.range plane := by
  ext E
  simp only [maximal_point_wing_iff hF,Set.mem_range]
  exact exists_congr (fun _ => eq_comm)

theorem maximal_point_wing_card (hF : Nat.card F=4) :
    Nat.card (Maximal (wing (F := F) false))=5 := by
  rw [maximal_point_wing_eq_range hF]
  exact plane_family_card hF

theorem join_point_wing (hF : Nat.card F=4) : join (wing (F := F) false)=wing false := by
  apply le_antisymm (sSup_le (fun _ h => h.1))
  have h1 : plane none ≤ join (wing (F := F) false) :=
    le_sSup ((maximal_point_wing_iff hF _).mpr ⟨none,rfl⟩)
  have h2 : plane (some (0:F)) ≤ join (wing (F := F) false) :=
    le_sSup ((maximal_point_wing_iff hF _).mpr ⟨some 0,rfl⟩)
  exact (plane_sup (F := F) (s := none) (t := some 0) (by simp)).symm.trans_le (sup_le h1 h2)

theorem eq_point_wing_of_maximal_finitePlane_and_other (hF : Nat.card F=4)
    {T E : Subgroup (unipotent (F := F))} (l : F)
    (hP : finitePlane l ∈ Maximal T) (hE : E ∈ Maximal T) (hne : E ≠ finitePlane l) :
    T=wing false := by
  have hT := le_point_wing_of_maximal_finitePlane hF T l hP
  have hcard : Nat.card E=16 := by
    have hh := maximal_card_eq hE hP
    norm_num [card_finitePlane,hF] at hh
    exact hh
  have hEP : E ∈ Maximal (wing false) := by
    refine ⟨hE.1.trans hT,hE.2.1,?_⟩
    intro A hA hs
    rw [hcard]
    exact small_card_le_sixteen_in_point_wing hF A hs hA
  obtain ⟨s,hs⟩ := (maximal_point_wing_iff hF E).mp hEP
  apply eq_point_wing_of_two_planes T hT (s := s) (t := some l)
  · intro he
    apply hne
    rw [hs,he]
    rfl
  · exact hs ▸ hE.1
  · exact hP.1

theorem small_classification (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hE : Small E) :
    E=⊥ ∨ (∃s : Option F, E=rootFamily s) ∨
      (E ≤ wing true ∧ 16≤Nat.card E) ∨ (∃l : F, E=finitePlane l) := by
  rcases small_classification_nonstandard hF E hE with hwing | hplane
  · rcases small_wing_classification hF E hwing hE.1 hE.2 with hbot | hroot | hlarge
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hroot)
    · exact Or.inr (Or.inr (Or.inl ⟨hwing,hlarge⟩))
  · exact Or.inr (Or.inr (Or.inr hplane))

theorem two_maximal_force_point_wing (hF : Nat.card F=4)
    {T E A : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hA : A ∈ Maximal T) (hne : E ≠ A) : T=wing false := by
  by_cases hEw : E ≤ wing true
  · by_cases hAw : A ≤ wing true
    · have hlarge : 16≤Nat.card E := by
        by_contra hn
        rcases small_wing_classification hF E hEw hE.2.1.1 hE.2.1.2 with hbot | hroot | hlarge
        · subst E
          have hcard := maximal_card_eq hA hE
          have hAbot : A=⊥ := A.eq_bot_of_card_le (by simpa using hcard.le)
          exact hne hAbot.symm
        · obtain ⟨s,rfl⟩ := hroot
          rcases small_wing_classification hF A hAw hA.2.1.1 hA.2.1.2 with hbot | hroot | hlarge
          · subst A
            have hh := maximal_card_eq hE hA
            norm_num [card_rootFamily,hF] at hh
          · obtain ⟨t,rfl⟩ := hroot
            have hst : s ≠ t := fun he => hne (congrArg rootFamily he)
            have hc : Nat.card (rootFamily s ⊔ rootFamily t : Subgroup (unipotent (F := F)))=16 := by
              norm_num [rootFamily_sup_card hst,hF]
            have hsmall := small_of_le_wing_of_large hF (rootFamily s ⊔ rootFamily t)
              (sup_le (rootFamily_le_wing s) (rootFamily_le_wing t)) hc.ge
            have hh := hE.2.2 _ (sup_le hE.1 hA.1) hsmall
            norm_num [hc,card_rootFamily,hF] at hh
          · have hh := maximal_card_eq hA hE
            norm_num [card_rootFamily,hF] at hh
            omega
        · exact hn hlarge
      have hcard := maximal_card_eq hE hA
      have hEeq := maximal_large_wing_eq_inf hF hE hEw hlarge
      have hAeq := maximal_large_wing_eq_inf hF hA hAw (hcard ▸ hlarge)
      exact False.elim (hne (hEeq.trans hAeq.symm))
    · obtain ⟨l,rfl⟩ := eq_finitePlane_of_small_not_le_wing hF A hA.2.1.1 hA.2.1.2 hAw
      exact eq_point_wing_of_maximal_finitePlane_and_other hF l hA hE hne
  · obtain ⟨l,rfl⟩ := eq_finitePlane_of_small_not_le_wing hF E hE.2.1.1 hE.2.1.2 hEw
    exact eq_point_wing_of_maximal_finitePlane_and_other hF l hE hA hne.symm

theorem two_maximal_classification (hF : Nat.card F=4)
    {T E A : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hA : A ∈ Maximal T) (hne : E ≠ A) :
    T=wing false ∧ Maximal T=Set.range plane ∧ Nat.card (Maximal T)=5 ∧ join T=T := by
  have hT := two_maximal_force_point_wing hF hE hA hne
  subst T
  exact ⟨rfl,maximal_point_wing_eq_range hF,maximal_point_wing_card hF,join_point_wing hF⟩

theorem small_bot : Small (⊥ : Subgroup (unipotent (F := F))) := by
  have he := (fixed_eq_top_iff (⊥ : Subgroup (unipotent (F := F)))).mpr rfl
  have hh := (fixed (⊥ : Subgroup (unipotent (F := F)))).finrank_quotient_add_finrank
  have hsame : Module.finrank F (fixed (⊥ : Subgroup (unipotent (F := F)))) =
      Module.finrank F (Vector (F := F)) := by rw [he]; exact finrank_top F _
  have hz : Module.finrank F (Vector (F := F) ⧸ fixed (⊥ : Subgroup (unipotent (F := F))))=0 := by
    rw [hsame] at hh
    omega
  norm_num [Small,movingIndex,hz]

theorem maximal_nonempty (T : Subgroup (unipotent (F := F))) : (Maximal T).Nonempty := by
  let : Finite (Subgroup (unipotent (F := F))) :=
    Finite.of_injective (fun A : Subgroup (unipotent (F := F)) => (A : Set (unipotent (F := F))))
      SetLike.coe_injective
  obtain ⟨E,hE,hm⟩ := Set.exists_max_image {E | E ≤ T ∧ Small E}
    (fun E => Nat.card E) (Set.toFinite _) ⟨⊥,bot_le,small_bot⟩
  exact ⟨E,hE.1,hE.2,fun A hAT hA => hm A ⟨hAT,hA⟩⟩

theorem maximal_singleton_or_point_wing (hF : Nat.card F=4)
    (T : Subgroup (unipotent (F := F))) :
    (∃ E,Maximal T={E} ∧ join T=E) ∨
    (T=wing false ∧ Maximal T=Set.range plane ∧ Nat.card (Maximal T)=5 ∧ join T=T) := by
  by_cases hpair : ∃ E ∈ Maximal T, ∃ A ∈ Maximal T, E ≠ A
  · obtain ⟨E,hE,A,hA,hne⟩ := hpair
    exact Or.inr (two_maximal_classification hF hE hA hne)
  · obtain ⟨E,hE⟩ := maximal_nonempty T
    have heq : Maximal T={E} := by
      ext A
      constructor
      · intro hA
        apply Set.mem_singleton_iff.mpr
        by_contra hh
        exact hpair ⟨A,hA,E,hE,hh⟩
      · rintro rfl
        exact hE
    refine Or.inl ⟨E,heq,?_⟩
    simp only [join,heq,sSup_singleton]

open scoped Pointwise in
def RootExclusion (T : Subgroup (unipotent (F := F))) : Prop :=
  ∀ s t : Option F, rootFamily s ≤ T → rootFamily t ≤ T →
    ¬ (join T : Set (unipotent (F := F))) ⊆
      (rootFamily s : Set (unipotent (F := F))) * (rootFamily t : Set (unipotent (F := F)))

theorem unique_maximal_large (hF : Nat.card F=4)
    {T E : Subgroup (unipotent (F := F))} (hmax : Maximal T={E})
    (hne : join T ≠ ⊥) (hex : RootExclusion T) :
    16≤Nat.card (join T) ∧
      (join T ≤ wing true ∨ ∃ l : F, join T=finitePlane l ∧ T≤wing false) := by
  have hE : E ∈ Maximal T := hmax ▸ Set.mem_singleton E
  have hj : join T=E := by simp only [join,hmax,sSup_singleton]
  rw [hj] at hne ⊢
  rcases small_classification hF E hE.2.1 with hbot | hroot | hlarge | hplane
  · exact False.elim (hne hbot)
  · obtain ⟨s,hs⟩ := hroot
    have hnot := hex s s (hs ▸ hE.1) (hs ▸ hE.1)
    apply False.elim
    apply hnot
    rw [hj,hs]
    exact Set.subset_mul_left _ (one_mem _)
  · exact ⟨hlarge.2,Or.inl hlarge.1⟩
  · obtain ⟨l,rfl⟩ := hplane
    refine ⟨?_,Or.inr ⟨l,rfl,le_point_wing_of_maximal_finitePlane hF T l hE⟩⟩
    norm_num [card_finitePlane,hF]

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
