module
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Theory.Representation.SpecialLinearNatural.SylowQuotientIrreducible

/-!
# The Borel on the actual natural module

A nonzero vector has a two-group stabilizer in the marked SL₂ quotient.
Lifting through O₂(L) shows that the centralizer in L of the natural
Sylow fixed line is the specified Sylow subgroup. Thus its setwise
stabilizer is the original Borel. The matrix invariant-interval theorem
then proves irreducibility above this line on the actual subgroup module.

All transports use the supplied natural marking and L → L/O₂(L).
Source: Aschbacher–Smith, 5.1.17, printed p.640, the verification of
G.2.1 used before constructing F.8.1 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G} {n : ℕ}

/-- The centralizer in L of its natural Sylow fixed line is precisely the Sylow subgroup. -/
theorem IsNaturalModule.sylow_fixed_centralizer (h : IsNaturalModule L V n)
    (S : Sylow 2 L) :
    L ⊓ centralizer (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) : Set G) =
      (S : Subgroup L).map L.subtype := by
  let Z := V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G)
  have hZ : Z ≠ ⊥ := by
    intro hz
    have hc := h.sylow_fixed_geometry S
    rw [show V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) = ⊥ from hz,
      card_bot] at hc
    obtain ⟨F,_,_,_,hF,_⟩ := h
    have hp : 1 < Nat.card F := Finite.one_lt_card
    rw [hF,← hc.1] at hp
    omega
  obtain ⟨x,hx1⟩ := ne_bot_iff_exists_ne_one.mp hZ
  obtain ⟨F,_,_,_,_,e,f,hf⟩ := h
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hk : q.ker = pCore 2 L := by
    ext l
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  let v := (f ⟨x,x.property.1⟩).toAdd
  have hv : v ≠ 0 := by
    intro he
    apply hx1
    apply Subtype.ext
    exact congrArg (fun z : V => (z : G)) (f.injective (he.trans f.map_one.symm))
  let C : Subgroup L := (centralizer ({(x : G)} : Set G)).comap L.subtype
  have hC : IsPGroup 2 C := by
    apply ((Matrix.SL2.stabilizer_nonzero_isPGroup v hv).comap_of_ker_isPGroup
      q (hk ▸ pCore_isPGroup)).to_le
    intro l hl
    change (q l).val.mulVec v = v
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    have hh := hf l ⟨x,x.property.1⟩
    change (f.symm (Multiplicative.ofAdd ((q l).val.mulVec v)) : G) = _ at hh
    rw [hh]
    change (l : G) * (x : G) * (l : G)⁻¹ = (f.symm (f ⟨x,x.property.1⟩) : G)
    rw [f.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hl)
  have hSC : (S : Subgroup L) ≤ C := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp x.property.2 _ (mem_map_of_mem L.subtype hl))
  have he : C = (S : Subgroup L) := S.is_maximal' hC hSC
  apply le_antisymm
  · intro l hl
    have hc : (⟨l,hl.1⟩ : L) ∈ C := mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hl.2 x x.property).symm
    rw [he] at hc
    exact mem_map_of_mem L.subtype hc
  · intro l hl
    exact ⟨map_subtype_le _ hl, mem_centralizer_iff.mpr
      (fun z hz => (mem_centralizer_iff.mp hz.2 l hl).symm)⟩

/-- The setwise natural Sylow-line stabilizer is the actual Borel. -/
theorem IsNaturalModule.sylow_fixed_normalizer (h : IsNaturalModule L V n)
    (S : Sylow 2 L) :
    L ⊓ normalizer (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) : Set G) =
      L ⊓ normalizer ((S : Subgroup L).map L.subtype : Set G) := by
  have hLV : L ≤ normalizer (V : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := h
    exact hm.normalizes
  apply le_antisymm
  · intro g hg
    refine ⟨hg.1,?_⟩
    have he := h.sylow_fixed_centralizer S
    have hm : g ∈ normalizer (L ⊓ centralizer
        (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) : Set G) : Set G) :=
      inf_normalizer_le_normalizer_inf
        ⟨L.le_normalizer hg.1, normalizer_le_normalizer_centralizer
          (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G)) hg.2⟩
    change g ∈ normalizer ((L ⊓ centralizer
      (V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) : Set G) : Subgroup G) : Set G) at hm
    rwa [he] at hm
  · intro g hg
    exact ⟨hg.1,inf_normalizer_le_normalizer_inf
      ⟨hLV hg.1,normalizer_le_normalizer_centralizer ((S : Subgroup L).map L.subtype) hg.2⟩⟩

/-- The literal Borel action is irreducible on the natural module modulo its Sylow fixed line. -/
theorem IsNaturalModule.sylow_fixed_invariant_interval (h : IsNaturalModule L V n)
    (S : Sylow 2 L) (X : Subgroup G)
    (hZX : V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) ≤ X)
    (hXV : X ≤ V)
    (hNX : L ⊓ normalizer ((S : Subgroup L).map L.subtype : Set G) ≤ normalizer (X : Set G)) :
    X = V ⊓ centralizer ((S : Subgroup L).map L.subtype : Set G) ∨ X = V := by
  obtain ⟨F,_,_,_,_,e,f,hf⟩ := h
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext l
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  let P := S.mapSurjective hq
  let j : Multiplicative (Fin 2 → F) →* G := V.subtype.comp f.symm.toMonoidHom
  have hj : Function.Injective j := V.subtype_injective.comp f.symm.injective
  have hconj (l : L) (v : Fin 2 → F) :
      j (Multiplicative.ofAdd (toLin' (q l) v)) =
        (l : G) * j (Multiplicative.ofAdd v) * (l : G)⁻¹ := by
    have hh := hf l (f.symm (Multiplicative.ofAdd v))
    rw [f.apply_symm_apply, toAdd_ofAdd] at hh
    exact hh
  have hfix (v : Fin 2 → F) :
      (∀ g ∈ (P : Subgroup SL(2,F)), toLin' g v = v) ↔
        j (Multiplicative.ofAdd v) ∈ centralizer ((S : Subgroup L).map L.subtype : Set G) := by
    constructor
    · intro hv
      apply mem_centralizer_iff.mpr
      rintro _ ⟨s,hs,rfl⟩
      have he := hconj s v
      rw [hv (q s) (mem_map_of_mem q hs)] at he
      exact mul_inv_eq_iff_eq_mul.mp he.symm
    · intro hv g hg
      obtain ⟨s,hs,rfl⟩ := hg
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hconj]
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_iff.mp hv _ (mem_map_of_mem L.subtype hs))
  let Y : AddSubgroup (Fin 2 → F) := (X.comap j).toAddSubgroup
  have hyfix : ∀ v, (∀ g ∈ (P : Subgroup SL(2,F)), toLin' g v = v) → v ∈ Y := by
    intro v hv
    exact hZX ⟨(f.symm (Multiplicative.ofAdd v)).property, (hfix v).mp hv⟩
  have hyn : ∀ g ∈ normalizer (P : Set SL(2,F)), ∀ v ∈ Y, toLin' g v ∈ Y := by
    intro g hg v hv
    obtain ⟨l,rfl⟩ := hq g
    have hl : l ∈ normalizer (S : Set L) := by
      have he : ((P : Subgroup SL(2,F))).comap q = (S : Subgroup L) := by
        change ((S : Subgroup L).map q).comap q = _
        rw [comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal S)]
      have hh : l ∈ (normalizer (P : Set SL(2,F))).comap q := hg
      change l ∈ (normalizer ((P : Subgroup SL(2,F)) : Set SL(2,F))).comap q at hh
      rw [comap_normalizer_eq_of_surjective (P : Subgroup SL(2,F)) hq,he] at hh
      exact hh
    have hl' : (l : G) ∈ normalizer ((S : Subgroup L).map L.subtype : Set G) :=
      (S : Subgroup L).le_normalizer_map L.subtype (mem_map_of_mem L.subtype hl)
    change j (Multiplicative.ofAdd (toLin' (q l) v)) ∈ X
    rw [hconj]
    exact (mem_normalizer_iff.mp (hNX ⟨l.property,hl'⟩) _).mp hv
  rcases Representation.SpecialLinearTwo.sylow_normalizer_invariant_interval P Y hyfix hyn with hy | hy
  · left
    apply le_antisymm ?_ hZX
    intro x hx
    have hv : (f ⟨x,hXV hx⟩).toAdd ∈ Y := by
      change (f.symm (f ⟨x,hXV hx⟩) : G) ∈ X
      simpa only [f.symm_apply_apply] using hx
    have hh := (hfix _).mp (hy _ hv)
    change (f.symm (f ⟨x,hXV hx⟩) : G) ∈ _ at hh
    rw [f.symm_apply_apply] at hh
    exact ⟨hXV hx,hh⟩
  · right
    apply le_antisymm hXV
    intro v hv
    have hh : (f ⟨v,hv⟩).toAdd ∈ Y := hy.ge (AddSubgroup.mem_top _)
    change (f.symm (f ⟨v,hv⟩) : G) ∈ X at hh
    simpa only [f.symm_apply_apply] using hh

end CFSG.Quasithin.Chapter6.Source
