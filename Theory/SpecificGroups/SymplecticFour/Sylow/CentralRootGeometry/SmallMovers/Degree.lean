module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootIndex

/-!
# Maximum small movers over arbitrary finite fields of characteristic two

Fixed-vector equations classify every small mover in the standard Sylow
subgroup. Outside the plane radical it is a full point-plane subgroup;
inside it is trivial, a full transvection root, or has order at least q².
Two distinct maximum movers force the ambient two-subgroup to be the
point radical, whose q+1 plane subgroups are exactly its maximum family.
No scalar closure or full-Sylow hypothesis is imposed on that subgroup.

Source: Meierfrankenfeld--Stellmacher (1993), (5.4), printed p.915.
The unique-maximum lower bound still requires the source (5.1) root
exclusion. The application to the actual replacement is in
NonbinarySymplectic.CriticalReduction.SmallMovers.
-/

@[expose] public section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] in
theorem finrank_fixed_ge_two (E : Subgroup (unipotent (F := F))) (hE : movingIndex E ≤ Nat.card F ^ 2) :
    2 ≤ Module.finrank F (fixed E) := by
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E) ≤ 2 := by
    apply (pow_le_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card F)).mp
    exact hE
  have hh := (fixed E).finrank_quotient_add_finrank
  have hdim : Module.finrank F (Vector (F := F)) = 4 := by
    simp [Vector, Module.finrank_fintype_fun_eq_card]
  rw [hdim] at hh
  omega

theorem exists_plane_coordinates_of_not_le_wing (E : Subgroup (unipotent (F := F))) (hE : movingIndex E ≤ Nat.card F ^ 2)
    (hout : ¬ E ≤ wing true) :
    ∃ lam : F, ∀ b u w v, element b u w v ∈ E → v=0 ∧ w=lam*b := by
  obtain ⟨g,hg,hgb⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  have hb : b ≠ 0 := by simpa only [element_mem_wing,↓reduceIte] using hgb
  have hz : ∀ x ∈ fixed E, x (.inr 0)=0 := by
    intro x hx
    exact (mul_eq_zero.mp (((mem_fixed_iff E x).mp hx b u w v hg).2.2)).resolve_left hb
  have ht : ∃ x : fixed E, (x:Vector (F := F)) (.inr 1) ≠ 0 := by
    by_contra hnone
    have hzero : ∀ x : fixed E, (x:Vector (F := F)) (.inr 1)=0 := by
      simpa only [not_exists,not_not] using hnone
    have hdim := fixed_finrank_le_one_of_three_zero E (by
      intro x hx
      have ht : x (.inr 1)=0 := hzero ⟨x,hx⟩
      have hh := ((mem_fixed_iff E x).mp hx b u w v hg).1
      rw [hz x hx,ht,mul_zero,mul_zero,add_zero,add_zero] at hh
      exact ⟨(mul_eq_zero.mp hh).resolve_left hb,hz x hx,ht⟩)
    have htwo := finrank_fixed_ge_two E hE
    omega
  obtain ⟨x,hxt⟩ := ht
  refine ⟨-x.val (.inl 1)/x.val (.inr 1),?_⟩
  intro c z t a hc
  have hfix := (mem_fixed_iff E x.val).mp x.property c z t a hc
  have hzero := hz x.val x.property
  have ha : a=0 := by
    have hh := hfix.2.1
    rw [hzero,mul_zero,zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_right hxt
  refine ⟨ha,?_⟩
  have hh := hfix.1
  rw [hzero,ha,mul_zero,add_zero,mul_zero,add_zero] at hh
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hxt).mpr
  calc
    t * x.val (.inr 1) = -(c*x.val (.inl 1)) := eq_neg_of_add_eq_zero_right hh
    _ = -x.val (.inl 1)*c := by ring

theorem movingIndex_eq_square_of_not_le_wing (E : Subgroup (unipotent (F := F))) (hE : movingIndex E ≤ Nat.card F ^ 2)
    (hout : ¬ E ≤ wing true) : movingIndex E = Nat.card F ^ 2 := by
  have heq : Module.finrank F (fixed E)=2 :=
    le_antisymm (finrank_fixed_le_two_of_not_le_wing E hout) (finrank_fixed_ge_two E hE)
  have hh := (fixed E).finrank_quotient_add_finrank
  have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E)=2 := by
    rw [hdim,heq] at hh
    omega
  rw [movingIndex,hquot]

theorem eq_finitePlane_of_small_not_le_wing (E : Subgroup (unipotent (F := F))) (hmove : movingIndex E ≤ Nat.card E)
    (hE : movingIndex E ≤ Nat.card F ^ 2) (hout : ¬ E ≤ wing true) :
    ∃ l : F, E=finitePlane l := by
  obtain ⟨l,hl⟩ := exists_plane_coordinates_of_not_le_wing E hE hout
  have hle : E ≤ finitePlane l := by
    intro g hg
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
    exact (element_mem_finitePlane l b u w v).mpr (hl b u w v hg)
  refine ⟨l,eq_of_le_of_card_ge hle ?_⟩
  rw [card_finitePlane]
  have hh := movingIndex_eq_square_of_not_le_wing E hE hout
  simpa only [hh] using hmove

theorem movingIndex_finitePlane (l : F) :
    movingIndex (finitePlane l)=Nat.card F ^ 2 := by
  have hle := finrank_fixed_le_two_of_not_le_wing (finitePlane l) (finitePlane_not_le_wing l)
  have hge := finrank_fixed_ge_two_of_le_finitePlane (finitePlane l) l le_rfl
  have hfix := le_antisymm hle hge
  have hh := (fixed (finitePlane l)).finrank_quotient_add_finrank
  have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
  rw [hfix,hdim] at hh
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed (finitePlane l))=2 := by omega
  rw [movingIndex,hquot]

theorem small_wing_classification (E : Subgroup (unipotent (F := F))) (hwing : E ≤ wing true)
    (hmove : movingIndex E ≤ Nat.card E) (_hbound : movingIndex E ≤ Nat.card F ^ 2) :
    E=⊥ ∨ (∃ s : Option F, E=rootFamily s) ∨ Nat.card F ^ 2≤Nat.card E := by
  by_cases hbot : E=⊥
  · exact Or.inl hbot
  by_cases hfix : fixed E = Theory.SpecificGroups.SymplecticFour.plane F
  · have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
    have hfixed : Module.finrank F (fixed E)=2 := by
      rw [hfix]
      exact Theory.SpecificGroups.SymplecticFour.finrank_plane
    have hh := (fixed E).finrank_quotient_add_finrank
    change Module.finrank F (Vector (F := F) ⧸ fixed E) + Module.finrank F (fixed E)=
      Module.finrank F (Vector (F := F)) at hh
    rw [hdim,hfixed] at hh
    have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E)=2 := by omega
    have hm : movingIndex E=Nat.card F ^ 2 := by rw [movingIndex,hquot]
    exact Or.inr (Or.inr (hm ▸ hmove))
  · obtain ⟨s,hs⟩ := exists_rootFamily_of_fixed_ne_standardPlane E hwing hfix
    refine Or.inr (Or.inl ⟨s,eq_of_le_of_card_ge hs ?_⟩)
    rw [card_rootFamily]
    exact (field_le_movingIndex_of_ne_bot E hbot).trans hmove

def Small (E : Subgroup (unipotent (F := F))) : Prop :=
  movingIndex E ≤ Nat.card E ∧ movingIndex E ≤ (Nat.card F ^ 2)

def Maximal (T : Subgroup (unipotent (F := F))) : Set (Subgroup (unipotent (F := F))) :=
  {E | E ≤ T ∧ Small E ∧ ∀ A, A ≤ T → Small A → Nat.card A ≤ Nat.card E}

noncomputable def join (T : Subgroup (unipotent (F := F))) : Subgroup (unipotent (F := F)) :=
  sSup (Maximal T)

theorem small_finitePlane (l : F) : Small (finitePlane l) := by
  simp only [Small,movingIndex_finitePlane,card_finitePlane,le_refl,and_self]

theorem small_of_le_wing_of_large (E : Subgroup (unipotent (F := F))) (hwing : E ≤ wing true) (hlarge : (Nat.card F ^ 2)≤Nat.card E) :
    Small E := by
  have hm := movingIndex_le_field_sq_of_le_wing E hwing
  exact ⟨hm.trans hlarge,hm⟩

theorem small_classification_nonstandard (E : Subgroup (unipotent (F := F))) (hE : Small E) :
    E ≤ wing true ∨ ∃ l : F, E=finitePlane l := by
  by_cases hwing : E ≤ wing true
  · exact Or.inl hwing
  · exact Or.inr (eq_finitePlane_of_small_not_le_wing E hE.1 hE.2 hwing)

omit [CharP F 2] [Finite F] in
theorem maximal_card_eq {T E A : Subgroup (unipotent (F := F))}
    (hE : E ∈ Maximal T) (hA : A ∈ Maximal T) : Nat.card E=Nat.card A :=
  le_antisymm (hA.2.2 E hE.1 hE.2.1) (hE.2.2 A hA.1 hA.2.1)

omit [CharP F 2] in
theorem maximal_eq_of_le {T E A : Subgroup (unipotent (F := F))}
    (hE : E ∈ Maximal T) (hA : A ≤ T) (hsmall : Small A) (hle : E ≤ A) : E=A :=
  eq_of_le_of_card_ge hle (hE.2.2 A hA hsmall)

theorem le_point_wing_of_maximal_finitePlane (T : Subgroup (unipotent (F := F))) (l : F) (hmax : finitePlane l ∈ Maximal T) :
    T ≤ wing false := by
  apply le_point_wing_of_plane_and_card_bound T l hmax.1
  by_contra hn
  have hlarge : (Nat.card F ^ 2) ≤ Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) := by
    omega
  have hs := small_of_le_wing_of_large (T ⊓ wing true) inf_le_right hlarge
  have hbound := hmax.2.2 _ inf_le_left hs
  rw [card_finitePlane] at hbound
  exact hn hbound

theorem maximal_large_wing_eq_inf {T E : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hwing : E ≤ wing true) (hlarge : (Nat.card F ^ 2)≤Nat.card E) : E=T ⊓ wing true := by
  have hle : E ≤ T ⊓ wing true := le_inf hE.1 hwing
  have hc : (Nat.card F ^ 2)≤Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) :=
    hlarge.trans (card_le_of_le hle)
  exact maximal_eq_of_le hE inf_le_left (small_of_le_wing_of_large _ inf_le_right hc) hle

theorem small_plane (s : Option F) : Small (plane s) := by
  cases s with
  | none =>
    apply small_of_le_wing_of_large _
    · exact center_le_wings.trans inf_le_right
    · rw [card_plane]
  | some s => exact small_finitePlane s

theorem small_card_le_square_in_point_wing (E : Subgroup (unipotent (F := F))) (hsmall : Small E) (hpoint : E ≤ wing false) :
    Nat.card E ≤ (Nat.card F ^ 2) := by
  rcases small_classification_nonstandard E hsmall with hwing | ⟨l,rfl⟩
  · have hcenter : E ≤ center (unipotent (F := F)) := (wings_inf (F := F)) ▸ le_inf hpoint hwing
    have hc := card_le_of_le hcenter
    norm_num [card_center] at hc
    exact hc
  · norm_num [card_finitePlane]

theorem maximal_point_wing_iff (E : Subgroup (unipotent (F := F))) :
    E ∈ Maximal (wing false) ↔ ∃ s : Option F, E=plane s := by
  constructor
  · intro hE
    have hplane := small_plane (F := F) none
    have hlarge : (Nat.card F ^ 2) ≤ Nat.card E := by
      have hh := hE.2.2 (plane none) (plane_le_wing none) hplane
      norm_num [plane,card_center] at hh
      exact hh
    rcases small_classification_nonstandard E hE.2.1 with hwing | ⟨l,rfl⟩
    · refine ⟨none,eq_of_le_of_card_ge ?_ ?_⟩
      · change E ≤ center (unipotent (F := F))
        exact (wings_inf (F := F)) ▸ le_inf hE.1 hwing
      · simpa [plane,card_center] using hlarge
    · exact ⟨some l,rfl⟩
  · rintro ⟨s,rfl⟩
    refine ⟨plane_le_wing s,small_plane s,?_⟩
    intro A hA hsmall
    rw [card_plane]
    exact small_card_le_square_in_point_wing A hsmall hA

theorem maximal_point_wing_eq_range :
    Maximal (wing (F := F) false)=Set.range plane := by
  ext E
  simp only [maximal_point_wing_iff,Set.mem_range]
  exact exists_congr (fun _ => eq_comm)

theorem maximal_point_wing_card :
    Nat.card (Maximal (wing (F := F) false))=Nat.card F+1 := by
  rw [maximal_point_wing_eq_range]
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_range_of_injective plane_injective]
  simp only [Nat.card_eq_fintype_card,Fintype.card_option]

theorem join_point_wing : join (wing (F := F) false)=wing false := by
  apply le_antisymm (sSup_le (fun _ h => h.1))
  have h1 : plane none ≤ join (wing (F := F) false) :=
    le_sSup ((maximal_point_wing_iff _).mpr ⟨none,rfl⟩)
  have h2 : plane (some (0:F)) ≤ join (wing (F := F) false) :=
    le_sSup ((maximal_point_wing_iff _).mpr ⟨some 0,rfl⟩)
  exact (plane_sup (F := F) (s := none) (t := some 0) (by simp)).symm.trans_le (sup_le h1 h2)

theorem eq_point_wing_of_maximal_finitePlane_and_other {T E : Subgroup (unipotent (F := F))} (l : F)
    (hP : finitePlane l ∈ Maximal T) (hE : E ∈ Maximal T) (hne : E ≠ finitePlane l) :
    T=wing false := by
  have hT := le_point_wing_of_maximal_finitePlane T l hP
  have hcard : Nat.card E=(Nat.card F ^ 2) := (maximal_card_eq hE hP).trans (card_finitePlane l)
  have hEP : E ∈ Maximal (wing false) := by
    refine ⟨hE.1.trans hT,hE.2.1,?_⟩
    intro A hA hs
    rw [hcard]
    exact small_card_le_square_in_point_wing A hs hA
  obtain ⟨s,hs⟩ := (maximal_point_wing_iff E).mp hEP
  apply eq_point_wing_of_two_planes T hT (s := s) (t := some l)
  · intro he
    apply hne
    rw [hs,he]
    rfl
  · exact hs ▸ hE.1
  · exact hP.1

theorem small_classification (E : Subgroup (unipotent (F := F))) (hE : Small E) :
    E=⊥ ∨ (∃s : Option F, E=rootFamily s) ∨
      (E ≤ wing true ∧ (Nat.card F ^ 2)≤Nat.card E) ∨ (∃l : F, E=finitePlane l) := by
  rcases small_classification_nonstandard E hE with hwing | hplane
  · rcases small_wing_classification E hwing hE.1 hE.2 with hbot | hroot | hlarge
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hroot)
    · exact Or.inr (Or.inr (Or.inl ⟨hwing,hlarge⟩))
  · exact Or.inr (Or.inr (Or.inr hplane))

theorem two_maximal_force_point_wing {T E A : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hA : A ∈ Maximal T) (hne : E ≠ A) : T=wing false := by
  by_cases hEw : E ≤ wing true
  · by_cases hAw : A ≤ wing true
    · have hlarge : (Nat.card F ^ 2)≤Nat.card E := by
        by_contra hn
        rcases small_wing_classification E hEw hE.2.1.1 hE.2.1.2 with hbot | hroot | hlarge
        · subst E
          have hcard := maximal_card_eq hA hE
          have hAbot : A=⊥ := A.eq_bot_of_card_le (by simpa using hcard.le)
          exact hne hAbot.symm
        · obtain ⟨s,rfl⟩ := hroot
          rcases small_wing_classification A hAw hA.2.1.1 hA.2.1.2 with hbot | hroot | hlarge
          · subst A
            have hh := maximal_card_eq hE hA
            rw [card_rootFamily] at hh
            rw [card_bot] at hh
            have hq := Finite.one_lt_card (α := F)
            omega
          · obtain ⟨t,rfl⟩ := hroot
            have hst : s ≠ t := fun he => hne (congrArg rootFamily he)
            have hc : Nat.card (rootFamily s ⊔ rootFamily t : Subgroup (unipotent (F := F)))=(Nat.card F ^ 2) := by
              norm_num [rootFamily_sup_card hst]
            have hsmall := small_of_le_wing_of_large (rootFamily s ⊔ rootFamily t)
              (sup_le (rootFamily_le_wing s) (rootFamily_le_wing t)) hc.ge
            have hh := hE.2.2 _ (sup_le hE.1 hA.1) hsmall
            rw [hc,card_rootFamily] at hh
            have hq := Finite.one_lt_card (α := F)
            nlinarith
          · have hh := maximal_card_eq hA hE
            rw [card_rootFamily] at hh
            rw [card_rootFamily] at hn
            omega
        · exact hn hlarge
      have hcard := maximal_card_eq hE hA
      have hEeq := maximal_large_wing_eq_inf hE hEw hlarge
      have hAeq := maximal_large_wing_eq_inf hA hAw (hcard ▸ hlarge)
      exact False.elim (hne (hEeq.trans hAeq.symm))
    · obtain ⟨l,rfl⟩ := eq_finitePlane_of_small_not_le_wing A hA.2.1.1 hA.2.1.2 hAw
      exact eq_point_wing_of_maximal_finitePlane_and_other l hA hE hne
  · obtain ⟨l,rfl⟩ := eq_finitePlane_of_small_not_le_wing E hE.2.1.1 hE.2.1.2 hEw
    exact eq_point_wing_of_maximal_finitePlane_and_other l hE hA hne.symm

theorem two_maximal_classification {T E A : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hA : A ∈ Maximal T) (hne : E ≠ A) :
    T=wing false ∧ Maximal T=Set.range plane ∧ Nat.card (Maximal T)=Nat.card F+1 ∧ join T=T := by
  have hT := two_maximal_force_point_wing hE hA hne
  subst T
  exact ⟨rfl,maximal_point_wing_eq_range,maximal_point_wing_card,join_point_wing⟩

theorem small_bot : Small (⊥ : Subgroup (unipotent (F := F))) := by
  have he := (fixed_eq_top_iff (⊥ : Subgroup (unipotent (F := F)))).mpr rfl
  have hh := (fixed (⊥ : Subgroup (unipotent (F := F)))).finrank_quotient_add_finrank
  have hsame : Module.finrank F (fixed (⊥ : Subgroup (unipotent (F := F)))) =
      Module.finrank F (Vector (F := F)) := by rw [he]; exact finrank_top F _
  have hz : Module.finrank F (Vector (F := F) ⧸ fixed (⊥ : Subgroup (unipotent (F := F))))=0 := by
    rw [hsame] at hh
    omega
  simp only [Small,movingIndex,hz,pow_zero,card_bot,le_refl,true_and]
  exact Nat.one_le_pow _ _ (Nat.card_pos (α := F))

theorem maximal_nonempty (T : Subgroup (unipotent (F := F))) : (Maximal T).Nonempty := by
  let : Finite (Subgroup (unipotent (F := F))) :=
    Finite.of_injective (fun A : Subgroup (unipotent (F := F)) => (A : Set (unipotent (F := F))))
      SetLike.coe_injective
  obtain ⟨E,hE,hm⟩ := Set.exists_max_image {E | E ≤ T ∧ Small E}
    (fun E => Nat.card E) (Set.toFinite _) ⟨⊥,bot_le,small_bot⟩
  exact ⟨E,hE.1,hE.2,fun A hAT hA => hm A ⟨hAT,hA⟩⟩

theorem maximal_singleton_or_point_wing (T : Subgroup (unipotent (F := F))) :
    (∃ E,Maximal T={E} ∧ join T=E) ∨
    (T=wing false ∧ Maximal T=Set.range plane ∧ Nat.card (Maximal T)=Nat.card F+1 ∧ join T=T) := by
  by_cases hpair : ∃ E ∈ Maximal T, ∃ A ∈ Maximal T, E ≠ A
  · obtain ⟨E,hE,A,hA,hne⟩ := hpair
    exact Or.inr (two_maximal_classification hE hA hne)
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

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
