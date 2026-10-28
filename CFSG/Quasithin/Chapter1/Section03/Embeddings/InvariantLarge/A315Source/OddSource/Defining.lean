module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
/-!
# The defining odd linear-three case of the intrinsic embedding

For the original permuting pair B,S and normal simple component D ≅ PSL₃(p),
the extraspecial alternative would make B a full defining Sylow subgroup.
The actual solvable product BS, restricted to D, also contains the given
Sylow two-intersection. Its transported image contradicts the even index
of a Borel. Thus B is elementary of order p² and has the required plane
coordinates. No Borel placement, Sylow conjugate, or action conclusion is
assumed.

Source: Aschbacher–Smith, A.3.15(2), printed pp.50–51, and the proof
of Proposition 1.3.4, printed pp.510–511.
-/

public section

open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
variable {J : Type*} [Group J] [Finite J]
variable {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}

/-- The original defining PSL₃(p) branch supplies the actual plane isomorphism. -/
theorem linear_plane_of_defining
    (h : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (ha : SourceTransport.PairAction p (S : Subgroup J) B)
    (hm : ClassicalGroup.IsPSL D 3 p) : Nonempty (B ≃* Plane p) := by
  let : Fact p.Prime := ⟨h.prime⟩
  apply InvariantThree.plane_of_odd_complement_card ha.oddComplement
  intro hc
  obtain ⟨F,hFld,hFin,hF,⟨e⟩⟩ := hm
  let : D.Normal := h.normal
  let A := B ⊔ (S : Subgroup J)
  let : Group.IsSolvable A := solvable_product B S h.p_group S.isPGroup'
    (by have := h.large; omega) h.permutes
  let K := A.subgroupOf D
  let j : K →* A :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (f := j)
    (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : A => (x : J)) hab)))
  let H := K.map e.toMonoidHom
  let : Group.IsSolvable H := Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupMap_surjective K)
  let R := (B.subgroupOf D).map e.toMonoidHom
  have hr : IsPGroup p R := h.p_group.comap_subtype.map e.toMonoidHom
  have hcard : Nat.card R = p^3 := by
    rw [← Nat.card_congr ((B.subgroupOf D).equivMapOfInjective
      e.toMonoidHom e.injective).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe h.inside).toEquiv]
    exact hc
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRH : R ≤ H := map_mono (fun x hx => (show B ≤ A from le_sup_left) hx)
  have hTH : (T' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) ≤ H := by
    apply map_mono
    rw [hT]
    exact fun x hx => (show (S : Subgroup J) ≤ A from le_sup_right) hx
  exact Matrix.PSL3.LinearThree.DefiningSylow.not_solvable_overgroup_of_card_cube
    F h.large h.odd hF R H hr hcard hRH T' hTH

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
