module
public import Mathlib.GroupTheory.Sylow
/-!
# Images of a supplied Sylow intersection

Let S be Sylow p in the finite group G, and P be Sylow p in a subgroup L.
If the ambient image B of P lies in S, then any homomorphism q satisfies
q(B)=q(S) intersect q(L). No normality of L or injectivity of q is required.

The image of P is Sylow in q(L). The restriction of q(S) to q(L) is a
p-subgroup containing that image, so Sylow maximality identifies them.
Mapping its subtype gives the displayed intersection.

This standard finite-group argument supplies quotient transport in the
prescribed-module applications of Stellmacher (2.4), in (4.6) and (8.3),
refs/latex/stellmacher-n-group.tex. It generalizes the former private
prime-two proof in SectionFour/PartnerCoreResidual.
-/

/-- A supplied Sylow intersection remains the same intersection after any homomorphism. -/
public theorem Sylow.map_image_eq_inf
    {G H : Type*} [Group G] [Group H] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (L B : Subgroup G) (P : Sylow p L)
    (hP : (P : Subgroup L).map L.subtype = B) (hBS : B ≤ (S : Subgroup G))
    (q : G →* H) :
    B.map q = ((S : Subgroup G).map q) ⊓ L.map q := by
  let f := q.subgroupMap L
  let U := P.mapSurjective (q.subgroupMap_surjective L)
  let C := ((S : Subgroup G).map q).subgroupOf (L.map q)
  have hUmap : (U : Subgroup (L.map q)).map (L.map q).subtype = B.map q := by
    change ((P : Subgroup L).map f).map (L.map q).subtype = _
    rw [Subgroup.map_map]
    change (P : Subgroup L).map (q.comp L.subtype) = _
    rw [← Subgroup.map_map, hP]
  have hUC : (U : Subgroup (L.map q)) ≤ C := by
    intro u hu
    have hm : (u : H) ∈ B.map q := by rw [← hUmap]; exact ⟨u, hu, rfl⟩
    exact Subgroup.map_mono hBS hm
  have hCp : IsPGroup p C :=
    (S.isPGroup'.map q).comap_of_injective (L.map q).subtype (L.map q).subtype_injective
  have hCU : C = (U : Subgroup (L.map q)) := U.3 hCp hUC
  rw [← hUmap, ← hCU]
  exact Subgroup.subgroupOf_map_subtype _ _

