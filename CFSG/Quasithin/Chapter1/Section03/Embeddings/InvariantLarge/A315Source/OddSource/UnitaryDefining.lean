module
public import Theory.SpecificGroups.SU3.DefiningSylowProducts.Model
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action
/-!
# The defining unitary branch of the original large-prime pair

The normal simple subgroup D contains the original complement B. Intersecting
the original Sylow two-subgroup with D gives a full Sylow of D, and the actual
permuting product restricts to D. The supplied PSU₃(p) equivalence transports
both of these literal subgroups. Their complement has order p² or p³ by the
original Xi shape. The isotropic-point exclusion proves these two subgroups
cannot permute, discharging the defining-unitary alternative.

The theorem retains the exact AmbientInput and PairAction records, with an
arbitrary catalogue parameter (in particular the full known-simple class).
It assumes no Borel placement, normality of the odd subgroup, or local
classification conclusion. No additional premise remains.
Source: Aschbacher–Smith A.3.15 and Proposition1.3.4, printed pp.50–51,510–511.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
variable {J : Type*} [Group J] [Finite J]

omit [Finite J] in
private theorem restricted_permuting (D B S : Subgroup J) (hBD : B≤D)
    (hperm : (B:Set J)*(S:Set J)=(S:Set J)*(B:Set J)) :
    (B.subgroupOf D : Set D)*(S.subgroupOf D : Set D)=
      (S.subgroupOf D : Set D)*(B.subgroupOf D : Set D) := by
  ext x
  constructor
  · rintro ⟨b,hb,s,hs,he⟩
    have hx : (x:J)∈(B:Set J)*(S:Set J) := ⟨b,hb,s,hs,congrArg Subtype.val he⟩
    rw [hperm] at hx
    obtain ⟨s',hs',b',hb',he'⟩ := hx
    have hsD : s'∈D := by
      have hh := D.mul_mem x.property (D.inv_mem (hBD hb'))
      rw [←he',mul_inv_cancel_right] at hh
      exact hh
    exact ⟨⟨s',hsD⟩,hs',⟨b',hBD hb'⟩,hb',Subtype.ext he'⟩
  · rintro ⟨s,hs,b,hb,he⟩
    have hx : (x:J)∈(S:Set J)*(B:Set J) := ⟨s,hs,b,hb,congrArg Subtype.val he⟩
    rw [←hperm] at hx
    obtain ⟨b',hb',s',hs',he'⟩ := hx
    have hsD : s'∈D := by
      have hh := D.mul_mem (D.inv_mem (hBD hb')) x.property
      rw [←he',inv_mul_cancel_left] at hh
      exact hh
    exact ⟨⟨b',hBD hb'⟩,hb',⟨s',hsD⟩,hs',Subtype.ext he'⟩

/-- The defining PSU₃(p) alternative is impossible for the original pair. -/
theorem not_unitary_defining
    {κ : GroupClass} {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}
    (h : OddCartan.AmbientInput κ D B S p)
    (ha : SourceTransport.PairAction p (S : Subgroup J) B)
    (hm : ClassicalGroup.IsPSU D 3 p) : False := by
  obtain ⟨E,_,_,form,hcard,hconj,⟨e⟩⟩ := hm
  let : D.Normal := h.normal
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let T' := T.mapSurjective (f:=e.toMonoidHom) e.surjective
  let U := (B.subgroupOf D).map e.toMonoidHom
  have hc : Nat.card U=Nat.card B :=
    (card_map_of_injective (f:=e.toMonoidHom) e.injective).trans
      (Nat.card_congr (subgroupOfEquivOfLe h.inside).toEquiv)
  have hU : Nat.card U=p^2 ∨ Nat.card U=p^3 := by
    rw [hc]
    rcases ha.oddComplement with ⟨_,hb⟩ | ⟨_,hb,_⟩
    · exact Or.inl hb
    · exact Or.inr hb
  apply BenderSuzuki.MatrixGroups.HermitianForm.DefiningSylowProducts.not_permuting
    form p h.prime h.odd h.large hcard hconj T' U hU
  have hh := congrArg (Set.image e) (restricted_permuting D B S h.inside h.permutes)
  change ((B.subgroupOf D).map e.toMonoidHom : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup form)) *
    ((T:Subgroup D).map e.toMonoidHom : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup form)) =
      ((T:Subgroup D).map e.toMonoidHom : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup form)) * ((B.subgroupOf D).map e.toMonoidHom : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup form))
  rw [hT]
  simpa only [Set.image_mul,Subgroup.coe_map,MulEquiv.coe_toMonoidHom] using hh
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
