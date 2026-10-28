module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.ElementaryAbelian.ExtraspecialEquiv
import all CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape

/-!
# Transport of the full nonsimple A.3.6 alternatives

Group isomorphisms carry the generalized Fitting subgroup and every prime
core to their counterparts. They therefore transport the literal natural
SL₂ conjugation action, and the nilpotent alternative with all homocyclic
exponents and the extraspecial power condition retained.

The internal quotient-structure import reuses its Fitting and layer
transport proofs without changing that shared module's public boundary.
Source: the intrinsic alternatives in Aschbacher--Smith A.3.6,
printed pp.43--45, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open LocalModels Chapter1.RadicalStructure
variable {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]

theorem A36Natural.of_mulEquiv (h : A36Natural A) (e : A ≃* B) : A36Natural B := by
  have hg := generalizedFitting_map e
  have hf := fitting_map e
  have hgf : generalizedFitting B = fittingSubgroup B := by rw [←hg,←hf,h.1]
  obtain ⟨p,hp,hp3,F,hF,hfin,hcard,v,r,hact⟩ := h.2
  let g : generalizedFitting A ≃* generalizedFitting B :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hg)
  let q := QuotientGroup.congr _ _ e hg
  refine ⟨hgf,p,hp,hp3,F,hF,hfin,hcard,g.symm.trans v,q.symm.trans r,?_⟩
  intro b x
  change v (g.symm _) = _
  have he : g.symm ⟨b*x*b⁻¹,(inferInstance : (generalizedFitting B).Normal).conj_mem x x.property b⟩ =
      ⟨e.symm b * (g.symm x : A) * (e.symm b)⁻¹,
        (inferInstance : (generalizedFitting A).Normal).conj_mem (g.symm x) (g.symm x).property (e.symm b)⟩ := by
    apply Subtype.ext
    exact (map_mul e.symm _ _).trans (congrArg₂ (· * ·) (map_mul e.symm _ _) (map_inv e.symm _))
  rw [he,hact]
  rfl

theorem A36Nilpotent.of_mulEquiv (h : A36Nilpotent A) (e : A ≃* B) : A36Nilpotent B := by
  have hg := generalizedFitting_map e
  have hf := fitting_map e
  let g : generalizedFitting A ≃* generalizedFitting B :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hg)
  let := h.2.1
  refine ⟨by rw [←hg,←hf,h.1],Group.nilpotent_of_mulEquiv g,?_,?_⟩
  · obtain ⟨F,hF,hfin,hcard,⟨r⟩⟩ := h.2.2.1
    exact ⟨F,hF,hfin,hcard,⟨(QuotientGroup.congr _ _ e hg).symm.trans r⟩⟩
  · intro p hp hd
    have hd' : p ∣ Nat.card (generalizedFitting A) := by rwa [Nat.card_congr g.toEquiv]
    obtain ⟨hmod,hshape⟩ := h.2.2.2 p hp hd'
    let c := (e.subgroupMap (pCore p A)).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
    refine ⟨hmod,?_⟩
    rcases hshape with ho | hh
    · left
      refine ⟨⟨ho.1.1.of_mulEquiv c, (Nat.card_congr c.toEquiv).symm.trans ho.1.2⟩,?_⟩
      intro x
      obtain ⟨y,rfl⟩ := c.surjective x
      rw [←map_pow,ho.2,map_one]
    · obtain ⟨n,hn,⟨f⟩⟩ := hh
      exact .inr ⟨n,hn,⟨c.symm.trans f⟩⟩
end CFSG.Quasithin.Chapter1.Section02
