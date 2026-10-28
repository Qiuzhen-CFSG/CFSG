module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.PlaneFamily
/-!
# The transvection roots of the standard symplectic plane radical

The q+1 full transvection groups in the standard plane wing have coordinates
(0,s²a,sa,a), together with the first central root at infinity. Each has
order q; distinct members intersect trivially and have a join of order q²
inside that elementary wing. These literal coordinate groups include all
possible full rank-one roots, without assuming arbitrary subgroups of the
wing are vector spaces over the field.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.1) and (5.4), printed pp.913--915. The companion wing-classification
module applies the natural fixed-space inequalities to arbitrary subgroups.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2]

def transvectionHom (s : F) : Multiplicative F →* unipotent (F := F) where
  toFun a := element 0 (s^2*a.toAdd) (s*a.toAdd) a.toAdd
  map_one' := by simpa using (element_zero (F := F))
  map_mul' a b := by
    simp only [element_mul]
    apply (element_eq_iff _ _ _ _ _ _ _ _).mpr
    dsimp
    constructor
    · simp
    constructor
    · ring
    constructor
    · ring
    · rfl

theorem transvectionHom_injective (s : F) : Function.Injective (transvectionHom s) := by
  intro x y h
  exact congrArg Multiplicative.ofAdd ((element_eq_iff _ _ _ _ _ _ _ _).mp h).2.2.2

def finiteRoot (s : F) : Subgroup (unipotent (F := F)) := (transvectionHom s).range

theorem element_mem_finiteRoot (s b u w v : F) :
    element b u w v ∈ finiteRoot s ↔ b=0 ∧ u=s^2*v ∧ w=s*v := by
  constructor
  · rintro ⟨a,h⟩
    have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp h
    exact ⟨hh.1.symm,by rw [←hh.2.2.2]; exact hh.2.1.symm,
      by rw [←hh.2.2.2]; exact hh.2.2.1.symm⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact ⟨Multiplicative.ofAdd v,rfl⟩

def rootFamily : Option F → Subgroup (unipotent (F := F))
  | none => root
  | some s => finiteRoot s

theorem card_finiteRoot (s : F) : Nat.card (finiteRoot s) = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective (transvectionHom_injective s)).toEquiv).symm

theorem card_rootFamily (s : Option F) : Nat.card (rootFamily s) = Nat.card F := by
  cases s with
  | none => exact card_root
  | some s => exact card_finiteRoot s

variable [Finite F]

theorem rootFamily_le_wing (s : Option F) : rootFamily s ≤ wing true := by
  intro x hx
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  rw [element_mem_wing]
  cases s with
  | none => exact ((element_mem_root _ _ _ _).mp hx).1
  | some s => exact ((element_mem_finiteRoot _ _ _ _ _).mp hx).1

theorem finiteRoot_inf_root (s : F) : finiteRoot s ⊓ root = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  obtain ⟨hb,hu,hw⟩ := (element_mem_finiteRoot _ _ _ _ _).mp hx.1
  obtain ⟨_,_,hv⟩ := (element_mem_root _ _ _ _).mp hx.2
  dsimp at hb hu hw hv
  subst b; subst v
  simp only [mul_zero] at hu hw
  subst u; subst w
  exact element_zero

theorem finiteRoot_inf_finiteRoot {s t : F} (hne : s ≠ t) :
    finiteRoot s ⊓ finiteRoot t = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  obtain ⟨hb,hu,hw⟩ := (element_mem_finiteRoot _ _ _ _ _).mp hx.1
  obtain ⟨_,_,ht⟩ := (element_mem_finiteRoot _ _ _ _ _).mp hx.2
  have hv : v=0 := by
    have hh : (s-t)*v=0 := by rw [sub_mul,←hw,←ht,sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
  dsimp at hb hu hw hv
  subst b; subst v
  simp only [mul_zero] at hu hw
  subst u; subst w
  exact element_zero

theorem rootFamily_inf {s t : Option F} (hne : s ≠ t) :
    rootFamily s ⊓ rootFamily t = ⊥ := by
  cases s with
  | none =>
    cases t with
    | none => exact False.elim (hne rfl)
    | some t => exact (inf_comm _ _).trans (finiteRoot_inf_root t)
  | some s =>
    cases t with
    | none => exact finiteRoot_inf_root s
    | some t => exact finiteRoot_inf_finiteRoot (fun hh => hne (congrArg some hh))

theorem rootFamily_sup_card {s t : Option F} (hne : s ≠ t) :
    Nat.card (rootFamily s ⊔ rootFamily t : Subgroup (unipotent (F := F))) = Nat.card F ^ 2 := by
  let := wing_elementary (F := F) true
  have hn : rootFamily t ≤ normalizer (rootFamily s : Set (unipotent (F := F))) :=
    (rootFamily_le_wing t).trans (((wing true).le_centralizer.trans
      (centralizer_le (rootFamily_le_wing s))).trans (Subgroup.centralizer_le_normalizer _))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn (disjoint_iff.mpr (rootFamily_inf hne)),
    card_rootFamily,card_rootFamily,pow_two]

theorem rootFamily_injective : Function.Injective (rootFamily (F := F)) := by
  intro s t he
  by_contra hne
  have hh := rootFamily_inf hne
  rw [he,inf_idem] at hh
  have hc : Nat.card F=1 := by rw [←card_rootFamily t,hh,card_bot]
  have := Finite.one_lt_card (α := F)
  omega

theorem rootFamily_card (hF : Nat.card F=4) :
    Nat.card (Set.range (rootFamily (F := F))) = 5 := by
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_range_of_injective rootFamily_injective]
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using congrArg (fun n => n+1) hF

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
