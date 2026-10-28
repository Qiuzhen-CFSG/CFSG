module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Fixed
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootFamily
/-!
# Small movers inside the standard plane radical

Every subgroup of the plane radical fixes the standard isotropic plane.
An additional fixed vector forces the subgroup into one full transvection
root, even when the subgroup is only binary-linear. Its order and the
small-mover inequality then force equality with that root. Otherwise its
moving index is sixteen.

This is the standard-plane branch of MS93 (5.4), printed p.915. Together
with the nonstandard plane branch it covers every subgroup of the Sylow
radical without assuming it is itself a full Sylow subgroup.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem standardPlane_le_fixed (E : Subgroup (unipotent (F := F))) (hE : E ≤ wing true) :
    Theory.SpecificGroups.SymplecticFour.plane F ≤ fixed E := by
  intro x hx
  apply (mem_fixed_iff E x).mpr
  intro b u w v hg
  have hb : b=0 := by simpa only [element_mem_wing,↓reduceIte] using hE hg
  have h0 := hx (0 : Fin 2)
  have h1 := hx (1 : Fin 2)
  simp [hb,h0,h1]

theorem movingIndex_le_field_sq_of_le_wing (E : Subgroup (unipotent (F := F)))
    (hE : E ≤ wing true) : movingIndex E ≤ Nat.card F ^ 2 := by
  have hd := Submodule.finrank_mono (standardPlane_le_fixed E hE)
  rw [Theory.SpecificGroups.SymplecticFour.finrank_plane] at hd
  have hh := (fixed E).finrank_quotient_add_finrank
  change 2 ≤ Module.finrank F (fixed E) at hd
  have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
  change Module.finrank F (Vector (F := F) ⧸ fixed E) + Module.finrank F (fixed E) = Module.finrank F (Vector (F := F)) at hh
  rw [hdim] at hh
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E) ≤ 2 := by omega
  exact Nat.pow_le_pow_right (Nat.card_pos (α := F)) hquot

theorem fixed_eq_top_iff (E : Subgroup (unipotent (F := F))) : fixed E = ⊤ ↔ E=⊥ := by
  constructor
  · intro htop
    apply le_bot_iff.mp
    intro g hg
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
    have hf (x : Vector (F := F)) := (mem_fixed_iff E x).mp (htop ▸ Submodule.mem_top) b u w v hg
    have hb : b=0 := by
      have hh := (hf (Pi.single (.inl 1) 1)).1
      simpa using hh
    have hu : u=0 := by
      have hh := (hf (Pi.single (.inr 0) 1)).1
      simpa using hh
    have hw : w=0 := by
      have hh := (hf (Pi.single (.inr 0) 1)).2.1
      simpa using hh
    have hv : v=0 := by
      have hh := (hf (Pi.single (.inr 1) 1)).2.1
      simpa using hh
    change element b u w v = 1
    rw [hb,hu,hw,hv,element_zero]
  · rintro rfl
    apply top_unique
    intro x _
    apply (mem_fixed_iff _ x).mpr
    intro b u w v h
    have hh : element b u w v=element 0 0 0 0 := (mem_bot.mp h).trans element_zero.symm
    obtain ⟨hb,hu,hw,hv⟩ := (element_eq_iff _ _ _ _ _ _ _ _).mp hh
    simp [hb,hu,hw,hv]

theorem field_le_movingIndex_of_ne_bot (E : Subgroup (unipotent (F := F))) (hE : E ≠ ⊥) :
    Nat.card F ≤ movingIndex E := by
  have hnt : fixed E ≠ ⊤ := fun ht => hE ((fixed_eq_top_iff E).mp ht)
  have hd := Submodule.finrank_lt hnt
  have hh := (fixed E).finrank_quotient_add_finrank
  have hq : 1 ≤ Module.finrank F (Vector (F := F) ⧸ fixed E) := by omega
  simpa only [pow_one,movingIndex] using Nat.pow_le_pow_right (Nat.card_pos (α := F)) hq

theorem le_rootFamily_of_fixed_outside (E : Subgroup (unipotent (F := F)))
    (hE : E ≤ wing true) {x : Vector (F := F)} (hx : x ∈ fixed E)
    (hout : x (.inr 0) ≠ 0 ∨ x (.inr 1) ≠ 0) : ∃ s : Option F, E ≤ rootFamily s := by
  by_cases hz : x (.inr 0)=0
  · have ht : x (.inr 1) ≠ 0 := hout.resolve_left (not_not.mpr hz)
    refine ⟨none,?_⟩
    intro g hg
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
    have hb : b=0 := by simpa only [element_mem_wing,↓reduceIte] using hE hg
    have hh := (mem_fixed_iff E x).mp hx b u w v hg
    simp only [hb,hz,zero_mul,mul_zero,zero_add,add_zero] at hh
    exact (element_mem_root _ _ _ _).mpr
      ⟨hb,(mul_eq_zero.mp hh.1).resolve_right ht,(mul_eq_zero.mp hh.2.1).resolve_right ht⟩
  · let s := x (.inr 1)/x (.inr 0)
    refine ⟨some s,?_⟩
    intro g hg
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
    have hb : b=0 := by simpa only [element_mem_wing,↓reduceIte] using hE hg
    have hh := (mem_fixed_iff E x).mp hx b u w v hg
    have hw : w=s*v := by
      dsimp [s]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hz).mpr
      calc
        w*x (.inr 0) = -(v*x (.inr 1)) := eq_neg_of_add_eq_zero_left hh.2.1
        _ = x (.inr 1)*v := by rw [CharTwo.neg_eq]; ring
    have hu : u=s^2*v := by
      have he := hh.1
      simp only [hb,zero_mul,zero_add,add_zero] at he
      have hs : s*x (.inr 0)=x (.inr 1) := by dsimp [s]; exact div_mul_cancel₀ _ hz
      apply mul_right_cancel₀ hz
      calc
        u*x (.inr 0) = -(w*x (.inr 1)) := eq_neg_of_add_eq_zero_left he
        _ = (s^2*v)*x (.inr 0) := by rw [CharTwo.neg_eq,hw,←hs]; ring
    exact (element_mem_finiteRoot _ _ _ _ _).mpr ⟨hb,hu,hw⟩

theorem exists_rootFamily_of_fixed_ne_standardPlane (E : Subgroup (unipotent (F := F)))
    (hE : E ≤ wing true) (hne : fixed E ≠ Theory.SpecificGroups.SymplecticFour.plane F) :
    ∃ s : Option F, E ≤ rootFamily s := by
  have hn : ¬ fixed E ≤ Theory.SpecificGroups.SymplecticFour.plane F :=
    fun hh => hne (le_antisymm hh (standardPlane_le_fixed E hE))
  obtain ⟨x,hx,hout⟩ := SetLike.not_le_iff_exists.mp hn
  apply le_rootFamily_of_fixed_outside E hE hx
  by_contra hh
  have h0 : x (.inr 0)=0 := by tauto
  have h1 : x (.inr 1)=0 := by tauto
  apply hout
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem movingIndex_eq_field_sq_of_large_wing (E : Subgroup (unipotent (F := F)))
    (hE : E ≤ wing true) (hlarge : Nat.card F < Nat.card E) : movingIndex E = Nat.card F ^ 2 := by
  have heq : fixed E = Theory.SpecificGroups.SymplecticFour.plane F := by
    by_contra hne
    obtain ⟨s,hs⟩ := exists_rootFamily_of_fixed_ne_standardPlane E hE hne
    have hc := card_le_of_le hs
    rw [card_rootFamily] at hc
    omega
  have hfixed : Module.finrank F (fixed E)=2 := by
    rw [heq]
    exact Theory.SpecificGroups.SymplecticFour.finrank_plane
  have hh := (fixed E).finrank_quotient_add_finrank
  change Module.finrank F (Vector (F := F) ⧸ fixed E) + Module.finrank F (fixed E) = Module.finrank F (Vector (F := F)) at hh
  have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
  rw [hdim,hfixed] at hh
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E)=2 := by omega
  rw [movingIndex,hquot]

theorem small_wing_classification (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hwing : E ≤ wing true)
    (hmove : movingIndex E ≤ Nat.card E) (_hbound : movingIndex E ≤ 16) :
    E=⊥ ∨ (∃ s : Option F, E=rootFamily s) ∨ 16≤Nat.card E := by
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
    have hm : movingIndex E=16 := by norm_num [movingIndex,hF,hquot]
    exact Or.inr (Or.inr (hm ▸ hmove))
  · obtain ⟨s,hs⟩ := exists_rootFamily_of_fixed_ne_standardPlane E hwing hfix
    refine Or.inr (Or.inl ⟨s,eq_of_le_of_card_ge hs ?_⟩)
    rw [card_rootFamily]
    exact (field_le_movingIndex_of_ne_bot E hbot).trans hmove

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
