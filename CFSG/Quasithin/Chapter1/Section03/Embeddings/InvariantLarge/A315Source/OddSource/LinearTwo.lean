module

public import Theory.SpecificGroups.PSL2.OddSylowProducts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action

/-!
# The original odd PSL₂ source exclusion

The permuting p-subgroup and original Sylow two-subgroup generate a solvable
group. Its intersection with the intrinsic normal simple subgroup contains
the actual Sylow intersection and the original complement. Transporting this
literal subgroup to PSL₂ invokes the odd Sylow-overgroup theorem, forcing
the complement cyclic, contrary to the original pair action.

Source: Aschbacher–Smith A.3.15(1) and Proposition 1.3.4, printed pp.50–51
and 510–511. The proof works for every odd field exponent and assumes no
Cartan placement, automorphism coverage, or A.3.15 conclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
variable {J : Type*} [Group J] [Finite J]

theorem not_linearTwo
    {κ : GroupClass} {D B : Subgroup J} {S : Sylow 2 J} {p q f : ℕ}
    (h : OddCartan.AmbientInput κ D B S p)
    (ha : SourceTransport.PairAction p (S : Subgroup J) B)
    (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL D 2 (q ^ f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨h.prime⟩
  let : Fact q.Prime := ⟨hq⟩
  let : D.Normal := h.normal
  let A := B ⊔ (S : Subgroup J)
  let : Group.IsSolvable A := solvable_product B S h.p_group S.isPGroup' (ne_of_gt (lt_trans (by decide : 2 < 3) h.large)) h.permutes
  let H := A.subgroupOf D
  let j : H →* A := (D.subtype.comp H.subtype).codRestrict A (fun x => x.property)
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => z.val) he
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective (f := j) hj
  let HM := H.map e.toMonoidHom
  let : Group.IsSolvable HM := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  let P := (B.subgroupOf D).map e.toMonoidHom
  have hPH : P ≤ HM := by
    apply map_mono
    intro x hx
    change x.val ∈ A
    exact (show B ≤ A from le_sup_left) hx
  have hP : IsPGroup p P := h.p_group.comap_subtype.map e.toMonoidHom
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let TM := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTH : (TM : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≤ HM := by
    change (T : Subgroup D).map e.toMonoidHom ≤ HM
    apply map_mono
    rw [hT]
    intro x hx
    change x.val ∈ A
    exact (show (S : Subgroup J) ≤ A from le_sup_right) hx
  have hc : IsCyclic (P.subgroupOf HM) :=
    Theory.PSL2.OddSylowProducts.isCyclic_of_solvable_sylow_overgroup
      hF ho h.large TM HM hTH _ hP.comap_subtype
  have hPc : IsCyclic P := (subgroupOfEquivOfLe hPH).isCyclic.mp hc
  have hBc : IsCyclic (B.subgroupOf D) :=
    ((B.subgroupOf D).equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr hPc
  exact ha.oddComplement.not_isCyclic ((subgroupOfEquivOfLe h.inside).isCyclic.mp hBc)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
