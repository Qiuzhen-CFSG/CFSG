module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage

/-!
# A normal intermediate subgroup above a symmetric-three square

The two-residual of S₃ × S₃ is A₃ × A₃. Pulling back one alternating
factor, then intersecting with the original two-residual, gives a normal
subgroup strictly between its two-core and itself. Explicit three-cycles
witness both strict containments, so no recognition by group order is used.

Source: Aschbacher--Smith, 15.2.23(a), printed p.1117. The literal K,S
application is in TerminalLinear.RepeatedNatural.MinimalParabolic.
-/

public noncomputable section
open Subgroup
namespace SymmetricThreeProductResidual
variable {H : Type*} [Group H] [Finite H]

/-- One alternating factor lifts to a normal strict intermediate subgroup
of the two-residual above its two-core. -/
theorem exists_normal_intermediate
    (e : (H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    ∃ L : Subgroup H, L.Normal ∧ (pResidual 2 H).pCoreIn 2 < L ∧ L < pResidual 2 H := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff x)
  let R := pResidual 2 H
  let F := (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3)))
  let L := R ⊓ F.comap q
  have hn : L.Normal := inferInstance
  have hQn : (R.pCoreIn 2).Normal := normalizer_eq_top_iff.mp (top_unique
    (le_normalizer_of_normal.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R))))
  have hQ : R.pCoreIn 2 ≤ q.ker := by
    rw [hk]
    exact le_sSup ⟨hQn,isPGroup_pCoreIn 2 R⟩
  have hQL : R.pCoreIn 2 ≤ L := le_inf (pCoreIn_le 2 R)
    (fun x hx => by change q x ∈ F; rw [show q x = 1 from hQ hx]; exact one_mem _)
  have hm : R.map q = (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) :=
    (map_pResidual_of_surjective 2 q hq).trans residual_eq
  let c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hc : c ∈ alternatingGroup (Fin 3) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  have hc1 : c ≠ 1 := by decide +kernel
  have hx : (c,1) ∈ R.map q := by rw [hm]; exact ⟨hc,one_mem _⟩
  obtain ⟨x,hx,hqx⟩ := hx
  have hxL : x ∈ L := ⟨hx,by change q x ∈ F; rw [hqx]; exact ⟨hc,one_mem _⟩⟩
  have hy : (1,c) ∈ R.map q := by rw [hm]; exact ⟨one_mem _,hc⟩
  obtain ⟨y,hy,hqy⟩ := hy
  refine ⟨L,hn,lt_of_le_of_ne hQL ?_,lt_of_le_of_ne inf_le_left ?_⟩
  · intro he
    have hh : q x = 1 := hQ (he.symm ▸ hxL)
    exact hc1 (congrArg Prod.fst (hqx.symm.trans hh))
  · intro he
    have hh : q y ∈ F := (show y ∈ L from he.symm ▸ hy).2
    rw [hqy] at hh
    exact hc1 hh.2

end SymmetricThreeProductResidual
