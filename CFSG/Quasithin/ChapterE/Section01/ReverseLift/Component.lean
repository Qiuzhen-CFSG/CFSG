module

public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Component.MinimalLift

/-!
# The component branch of reverse E-member quotient lifting

Let `I` be a component-type E-member in `G/Y`. Its full preimage `P` contains
the ambient tau, and the prescribed Sylow intersects `P` in a Sylow subgroup.
Choose a minimal supplement to the kernel of `P → I`, over that Sylow, using
the source section `O²(P) ker(P → I)`. Its image is all of `I`.

The solvable kernel identifies the intrinsic radical quotients, and minimality
identifies the local tau images. Thus `Component.MinimalLift` transfers every
component clause and the exact rank. E.1.8 then gives ambient membership;
functoriality of the finite two-residual gives the literal residual-image equality.

For this branch the full preimage suffices: the component data transfer across
the radical isomorphism without shrinking to the residual--tau subgroup. We
therefore prove the stronger full-image conclusion, while also exporting the
source's residual-image-only interface for the parent two-branch assembly.
The odd-prime branch is not used in this argument.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10(7), printed pp.211--212, using E.1.10(2),(4) and E.1.8(2).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The component branch of E.1.10(7) admits a lift with full image `I`.
The bound is on the intrinsic radical quotient, and the conclusion includes
membership in the original ambient group and the literal residual image. -/
theorem exists_component_quotient_lift_with_image (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {I : Subgroup (G ⧸ Y)} {i : ℕ}
    (h0 : IsEMember ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I)
    (hc : ECaseComponent ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I)
    (hi : Group.rank (((A.map (QuotientGroup.mk' Y)).subgroupOf I).map
      (QuotientGroup.mk' (solvableRadical I))) ≤ i) :
    ∃ J : Subgroup G, IsEMemberAt i (T : Subgroup G) A J ∧
      J.map (QuotientGroup.mk' Y) = I ∧
      ((pResidual 2 J).map J.subtype).map (QuotientGroup.mk' Y) =
        (pResidual 2 I).map I.subtype := by
  let q := QuotientGroup.mk' Y
  let P := I.comap q
  have hI : IsEMemberAt i ((T : Subgroup G).map q) (A.map q) I :=
    ⟨h0, Or.inr ⟨hc, hi⟩⟩
  obtain ⟨htau, hAP, S, hS⟩ := hI.quotient_preimage T A Y
  let B := A.subgroupOf P
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAP
  have hBS : B ≤ (S : Subgroup P) := by
    rw [hS]
    exact subgroupOf_mono P hAT
  let f : P →* I := (q.comp P.subtype).codRestrict I (fun x => x.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective Y x.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change q g ∈ I
    exact hg.symm ▸ x.property
  obtain ⟨K, hK, hKu⟩ := exists_minimalResidualSupplement S f.ker
  let u := QuotientGroup.mk' f.ker
  let e0 := QuotientGroup.quotientKerEquivOfSurjective f hf
  let e : K.map u ≃* I := MulEquiv.ofBijective
    (e0.toMonoidHom.comp (K.map u).subtype)
    ⟨e0.injective.comp (K.map u).subtype_injective, by
      intro x
      refine ⟨⟨e0.symm x, ?_⟩, e0.apply_symm_apply x⟩
      rw [hKu]
      trivial⟩
  have hmap (C : Subgroup P) (hCK : C ≤ K) :
      ((C.subgroupOf K).map (u.subgroupMap K)).map e.toMonoidHom = C.map f := by
    rw [map_map]
    change (C.subgroupOf K).map (f.comp K.subtype) = C.map f
    rw [← map_map, map_subgroupOf_eq_of_le hCK]
  have hSf : (S : Subgroup P).map f = ((T : Subgroup G).map q).subgroupOf I := by
    rw [hS]
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.val, hs, rfl⟩
    · rintro ⟨t, ht, he⟩
      have htP : t ∈ P := by
        change q t ∈ I
        exact he.symm ▸ x.property
      exact ⟨⟨t, htP⟩, ht, Subtype.ext he⟩
  have hBf : B.map f = (A.map q).subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_map]
    change B.map (q.comp P.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hAP, subgroupOf_map_subtype,
      inf_eq_left.mpr h0.2.2.1]
  obtain ⟨hcomp, hrank⟩ := hK.component_of_image_equiv S hBS hc e
    ((hmap _ hK.1.1).trans hSf) ((hmap _ (hBS.trans hK.1.1)).trans hBf)
  have hmem : IsEMemberAt i (S : Subgroup P) B K := by
    refine ⟨⟨inferInstance, hBS, hBS.trans hK.1.1,
      le_inf (tau_le _ _) ((tau_le _ _).trans hK.1.1),
      ⟨S.subtype hK.1.1, rfl⟩, Or.inr hcomp⟩, Or.inr ⟨hcomp, hrank.trans_le hi⟩⟩
  have hfK : K.map f = ⊤ := by
    calc
      _ = (K.map u).map e0.toMonoidHom := by rw [map_map]; rfl
      _ = ⊤ := by
        rw [hKu]
        exact map_top_of_surjective e0.toMonoidHom e0.surjective
  have hJ : (K.map P.subtype).map q = I := by
    calc
      _ = (K.map f).map I.subtype := by rw [map_map, map_map]; rfl
      _ = I := by rw [hfK, ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨K.map P.subtype, ?_, hJ, ?_⟩
  · rw [hS] at hmem
    exact hmem.inherit T A P hAT htau
  · rw [map_embedded_pResidual, hJ]

/-- E.1.10(7), restricted to the component disjunct of `IsEMemberAt`.
This is the interface for the parent two-branch assembly; it requires only
the residual image, as in the source. -/
theorem exists_component_quotient_lift (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {I : Subgroup (G ⧸ Y)} {i : ℕ}
    (h0 : IsEMember ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I)
    (hc : ECaseComponent ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I)
    (hi : Group.rank (((A.map (QuotientGroup.mk' Y)).subgroupOf I).map
      (QuotientGroup.mk' (solvableRadical I))) ≤ i) :
    ∃ J : Subgroup G, IsEMemberAt i (T : Subgroup G) A J ∧
      ((pResidual 2 J).map J.subtype).map (QuotientGroup.mk' Y) =
        (pResidual 2 I).map I.subtype := by
  obtain ⟨J, hJ, _, hres⟩ :=
    exists_component_quotient_lift_with_image T A Y hAT h0 hc hi
  exact ⟨J, hJ, hres⟩

end CFSG.Quasithin.ChapterE
