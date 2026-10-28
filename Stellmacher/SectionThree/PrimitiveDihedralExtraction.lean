module

public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.Quotient
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.CyclicResidual
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.PhiTwoTransfer
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.CoreFreeReflection
public import Theory.GroupTheory.SelfContainingConjugator

/-!
# Stellmacher (3.6): primitive dihedral extraction

This module packages the part of Stellmacher's Lemma (3.6), Journal of
Algebra 190 (1997), pp. 22--23, which extracts the cyclic odd rotation group
from a solvable member `P` of `PSet`. The quotient construction chooses a
reflected cyclic subgroup `K ≤ P/O₂(P)` outside the relevant Frattini
subgroup and a coatom of the elementary abelian actor which centralizes it.
The lifted actor coatom has index two; its cardinality relation is retained
explicitly for the local index assertion in (7.8)(a).
The quotient rotation's non-Frattini witness is also retained, so the
unique-maximal residual intersection from (3.3) can prove local generation.

We lift a generator of `K` to `x : P`, put
`L = A ⊔ A.conjBy x`, and choose the lift so that `x ∈ L`. This follows by
minimizing `|L|` over lifts and lifting the same quotient element inside
`L` once more. We then identify `O²(L)` with the lift `F₀`. Residual
functoriality gives the rotation equality; Frattini transfer proves
`F₀ ≰ Φ₂(O²(P))`; residual perfection lifts the quotient commutator
calculation to `F₀ ≤ [F₀,T]`. The public data package is exactly the input
needed by the separate generated-dihedral assembly for the four conclusions
of Lemma (3.6).
-/

open BenderSuzuki.External
open scoped Pointwise

universe u

@[expose] public section

namespace Stellmacher.SectionThree

public structure PrimitiveDihedralExtractionData
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (hAP : A ≤ P) (a : G) (haA : a ∈ A) where
  x : P
  x_mem_generated : (x : G) ∈ A ⊔ A.conjBy (x : G)
  A₀ : Subgroup G
  F₀ : Subgroup G
  p : ℕ
  n : ℕ
  prime_p : Nat.Prime p
  odd_p : Odd p
  n_pos : 0 < n
  A₀_le : A₀ ≤ A
  A₀_index_two : Nat.card A = 2 * Nat.card A₀
  A_factor : (A : Set G) =
    (Subgroup.zpowers a : Set G) * (A₀ : Set G)
  residual_generated :
    F₀ = twoResidualAmbient (A ⊔ A.conjBy (x : G))
  F₀_le_P : F₀ ≤ P
  rotation_eq :
    (F₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) =
      Subgroup.zpowers (QuotientGroup.mk' (pCore 2 P) x)
  rotation_le_residual :
    (F₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) ≤
      twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))
  rotation_not_residual_frattini :
    ¬ (F₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) ≤
      frattiniAmbient (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))
  rotation_card :
    Nat.card ((F₀.subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P))) = p ^ n
  reflected : ∀ r : P ⧸ pCore 2 P,
    r ∈ (F₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) →
    QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩ * r *
      (QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩)⁻¹ = r⁻¹
  reflection_involution : IsInvolution
    (QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩)
  A₀_centralizes_rotation : ∀ (b : G) (hb : b ∈ A₀),
    ∀ r : P ⧸ pCore 2 P,
      r ∈ (F₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) →
      QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (A₀_le hb)⟩ * r =
        r * QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (A₀_le hb)⟩
  residual_not_phi : ¬ F₀ ≤ phiTwo (twoResidualAmbient P)
  residual_commutator : F₀ ≤ ⁅F₀, T⁆

theorem map_subgroupOf_subtype_eq
    {G : Type*} [Group G] (K P : Subgroup G) (hKP : K ≤ P) :
    (K.subgroupOf P).map P.subtype = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKP hx⟩, hx, rfl⟩

theorem generated_inside_and_quotient_image
    {G : Type u} [Group G] [Finite G]
    (P A : Subgroup G) (hAP : A ≤ P) (x : P) :
    let AP := A.subgroupOf P
    let LP := AP ⊔ AP.conjBy x
    let L := LP.map P.subtype
    let qO : P →* P ⧸ pCore 2 P := QuotientGroup.mk' (pCore 2 P)
    L = A ⊔ A.conjBy (x : G) ∧
      LP.map qO = AP.map qO ⊔ (AP.map qO).conjBy (qO x) := by
  dsimp only
  constructor
  · rw [Subgroup.map_sup, map_conjBy]
    rw [map_subgroupOf_subtype_eq A P hAP]
    change A ⊔ A.conjBy (x : G) = A ⊔ A.conjBy (x : G)
    rfl
  · rw [Subgroup.map_sup, map_conjBy]

noncomputable def quotient_rotation_lift
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (P₀ : Subgroup P)
    (hTP : T ≤ P) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A)
    (qd : QuotientExtractionData P T A P₀ hTP hAP a haA) :
    {x : P //
      let qO : P →* P ⧸ pCore 2 P := QuotientGroup.mk' (pCore 2 P)
      let AP := A.subgroupOf P
      let LP := AP ⊔ AP.conjBy x
      qO x = qd.z ∧
        LP.map qO = qd.K ⊔ AP.map qO ∧
        (twoResidualAmbient LP).map qO = qd.K ∧ x ∈ LP} := by
  classical
  let O : Subgroup P := pCore 2 P
  let qO : P →* P ⧸ O := QuotientGroup.mk' O
  let AP : Subgroup P := A.subgroupOf P
  let Abar : Subgroup (P ⧸ O) := AP.map qO
  let abar : P ⧸ O := qO ⟨a, hAP haA⟩
  have habarA : abar ∈ Abar := by
    exact Subgroup.mem_map_of_mem qO
      (show ⟨a, hAP haA⟩ ∈ AP from haA)
  let _ : Fact qd.p.Prime := ⟨qd.prime_p⟩
  have hzp : IsPGroup qd.p (Subgroup.zpowers qd.z) := by
    rw [← qd.K_cyclic]
    exact qd.K_pgroup
  have hzref : abar * qd.z * abar⁻¹ = qd.z⁻¹ := by
    exact qd.reflected qd.z (by rw [qd.K_cyclic]; exact Subgroup.mem_zpowers _)
  have hsup : Abar ⊔ Abar.conjBy qd.z = qd.K ⊔ Abar := by
    rw [sup_conjBy_eq_zpowers_sup_of_reflection Abar qd.z abar
      qd.odd_p hzp qd.actor_elementary habarA hzref]
    rw [← qd.K_cyclic]
  have hzin : qd.z ∈ Abar ⊔ Abar.conjBy qd.z := by
    rw [hsup]
    apply (show qd.K ≤ qd.K ⊔ Abar from le_sup_left)
    rw [qd.K_cyclic]
    exact Subgroup.mem_zpowers _
  have hex := Subgroup.exists_lift_mem_sup_conjBy qO AP qd.z
    (QuotientGroup.mk'_surjective O qd.z) hzin
  let x : P := Classical.choose hex
  have hx : qO x = qd.z := (Classical.choose_spec hex).1
  have hxmem : x ∈ AP ⊔ AP.conjBy x := (Classical.choose_spec hex).2
  let LP : Subgroup P := AP ⊔ AP.conjBy x
  let J : Subgroup (P ⧸ O) := LP.map qO
  have hJ : J = Abar ⊔ Abar.conjBy qd.z := by
    dsimp only [J, LP, Abar]
    rw [Subgroup.map_sup, map_conjBy, hx]
  have hJK : J = qd.K ⊔ Abar := hJ.trans hsup
  have hresJ : twoResidualAmbient J = qd.K := by
    rw [hJK]
    exact twoResidualAmbient_sup_eq_odd_normal_subgroup qd.K Abar
      qd.prime_p qd.odd_p qd.K_pgroup qd.actor_two
        qd.actor_normalizes_K
  have hresLP : (twoResidualAmbient LP).map qO = qd.K := by
    rw [map_twoResidualAmbient_of_subgroup_image LP qO J rfl]
    exact hresJ
  refine ⟨x, ?_⟩
  dsimp only
  refine ⟨hx, ?_, ?_⟩
  · exact hJK
  · exact ⟨hresLP, hxmem⟩

structure LiftedRotationData
    {G : Type u} [Group G] [Finite G]
    (P A : Subgroup G) (hAP : A ≤ P)
    (K : Subgroup (P ⧸ pCore 2 P))
    (z : P ⧸ pCore 2 P) where
  x : P
  x_mem_generated : (x : G) ∈ A ⊔ A.conjBy (x : G)
  x_image : QuotientGroup.mk' (pCore 2 P) x = z
  F₀ : Subgroup G
  residual_generated :
    F₀ = twoResidualAmbient (A ⊔ A.conjBy (x : G))
  F₀_le_P : F₀ ≤ P
  rotation_eq :
    (F₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) = K

noncomputable def liftedRotationData
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (P₀ : Subgroup P)
    (hTP : T ≤ P) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A)
    (qd : QuotientExtractionData P T A P₀ hTP hAP a haA) :
    LiftedRotationData P A hAP qd.K qd.z := by
  classical
  let qlift := quotient_rotation_lift P T A P₀ hTP hAP a haA qd
  let x : P := qlift.1
  have hx : (QuotientGroup.mk' (pCore 2 P)) x = qd.z := qlift.2.1
  let AP : Subgroup P := A.subgroupOf P
  let LP : Subgroup P := AP ⊔ AP.conjBy x
  let L : Subgroup G := LP.map P.subtype
  let F₀ : Subgroup G := twoResidualAmbient L
  have hL : L = A ⊔ A.conjBy (x : G) :=
    (generated_inside_and_quotient_image P A hAP x).1
  have hLPmap : LP.map (QuotientGroup.mk' (pCore 2 P)) =
      qd.K ⊔ AP.map (QuotientGroup.mk' (pCore 2 P)) :=
    qlift.2.2.1
  have hresLP : (twoResidualAmbient LP).map
      (QuotientGroup.mk' (pCore 2 P)) = qd.K :=
    qlift.2.2.2.1
  have hF₀P : F₀ ≤ P := by
    exact (Subgroup.map_subtype_le (twoResidualSubgroup L)).trans
      (Subgroup.map_subtype_le LP)
  have hF₀sub : F₀.subgroupOf P = twoResidualAmbient LP := by
    apply Subgroup.map_injective P.subtype_injective
    rw [map_subgroupOf_subtype_eq F₀ P hF₀P]
    symm
    exact map_twoResidualAmbient_of_subgroup_image LP P.subtype L rfl
  refine
    { x := x
      x_mem_generated := by
        rw [← hL]
        exact Subgroup.mem_map_of_mem P.subtype qlift.2.2.2.2
      x_image := hx
      F₀ := F₀
      residual_generated := by
        change twoResidualAmbient L =
          twoResidualAmbient (A ⊔ A.conjBy (x : G))
        rw [hL]
      F₀_le_P := hF₀P
      rotation_eq := by rw [hF₀sub]; exact hresLP }

end Stellmacher.SectionThree

namespace Stellmacher.SectionThree

theorem twoResidualAmbient_subgroupOf_map_quotient
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    ((twoResidualAmbient P).subgroupOf P).map
        (QuotientGroup.mk' (pCore 2 P)) =
      twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)) := by
  classical
  let qO : P →* P ⧸ pCore 2 P := QuotientGroup.mk' (pCore 2 P)
  have htopP : (⊤ : Subgroup P).map P.subtype = P := by
    ext x
    simp
  have htopQ : (⊤ : Subgroup P).map qO = ⊤ :=
    Subgroup.map_top_of_surjective qO
      (QuotientGroup.mk'_surjective (pCore 2 P))
  have hresP : (twoResidualAmbient (⊤ : Subgroup P)).map P.subtype =
      twoResidualAmbient P :=
    map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P)
      P.subtype P htopP
  have hsub : (twoResidualAmbient P).subgroupOf P =
      twoResidualAmbient (⊤ : Subgroup P) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [map_subgroupOf_subtype_eq (twoResidualAmbient P) P
      (Subgroup.map_subtype_le (twoResidualSubgroup P))]
    exact hresP.symm
  rw [hsub]
  exact map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) qO ⊤ htopQ

theorem lifted_residual_not_phi
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (P₀ : Subgroup P)
    (hTP : T ≤ P) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A)
    (qd : QuotientExtractionData P T A P₀ hTP hAP a haA)
    (F₀ : Subgroup G) (_hF₀P : F₀ ≤ P)
    (hrotation : (F₀.subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P)) = qd.K) :
    ¬ F₀ ≤ phiTwo (twoResidualAmbient P) := by
  classical
  intro hFphi
  let O : Subgroup P := pCore 2 P
  let qO : P →* P ⧸ O := QuotientGroup.mk' O
  let U : Subgroup G := twoResidualAmbient P
  have hUP : U ≤ P :=
    Subgroup.map_subtype_le (twoResidualSubgroup P)
  let R : Subgroup (P ⧸ O) :=
    twoResidualAmbient (⊤ : Subgroup (P ⧸ O))
  have hUR : (U.subgroupOf P).map qO = R := by
    simpa [U, R, O, qO] using
      twoResidualAmbient_subgroupOf_map_quotient P
  let fU0 : U →* P ⧸ O := qO.comp (Subgroup.inclusion hUP)
  let fU : U →* R := fU0.codRestrict R (fun x => by
    have hxUP : (Subgroup.inclusion hUP x) ∈ U.subgroupOf P := x.property
    have hxmap : qO (Subgroup.inclusion hUP x) ∈ (U.subgroupOf P).map qO :=
      Subgroup.mem_map_of_mem qO hxUP
    change qO (Subgroup.inclusion hUP x) ∈ R
    rw [← hUR]
    exact hxmap)
  have hfU : Function.Surjective fU := by
    intro y
    have hymap : (y : P ⧸ O) ∈ (U.subgroupOf P).map qO := by
      rw [hUR]
      exact y.property
    rcases hymap with ⟨x, hx, hxy⟩
    let u : U := ⟨(x : G), hx⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hxy
  let _ : Fact qd.p.Prime := ⟨qd.prime_p⟩
  have hPhiMap : ((phiTwo U).subgroupOf U).map fU ≤ frattini R :=
    phiTwo_map_le_frattini_of_surjective_odd_pGroup U fU hfU
      qd.odd_p qd.residual_pgroup
  apply qd.K_not_residual_frattini
  have hKR : qd.K ≤ R := by
    rw [qd.K_cyclic]
    exact Subgroup.zpowers_le.2 qd.z_mem_residual
  intro k hk
  have hkimage : k ∈ (F₀.subgroupOf P).map qO := by
    rw [hrotation]
    exact hk
  rcases hkimage with ⟨x, hx, hxk⟩
  have hxphi : (x : G) ∈ phiTwo U := hFphi hx
  have hxU : (x : G) ∈ U :=
    (Subgroup.map_subtype_le
      ((frattini (U ⧸ pCore 2 U)).comap
        (QuotientGroup.mk' (pCore 2 U)))) hxphi
  let u : U := ⟨(x : G), hxU⟩
  let kR : R := ⟨k, hKR hk⟩
  have hkPhiMap : kR ∈ ((phiTwo U).subgroupOf U).map fU := by
    refine ⟨u, hxphi, ?_⟩
    apply Subtype.ext
    exact hxk
  exact Subgroup.mem_map_of_mem R.subtype (hPhiMap hkPhiMap)

theorem lifted_residual_le_commutator
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (P₀ : Subgroup P)
    (hTP : T ≤ P) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A)
    (qd : QuotientExtractionData P T A P₀ hTP hAP a haA)
    (L F₀ : Subgroup G) (hF₀ : F₀ = twoResidualAmbient L)
    (hF₀P : F₀ ≤ P)
    (hrotation : (F₀.subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P)) = qd.K) :
    F₀ ≤ ⁅F₀, T⁆ := by
  classical
  let O : Subgroup P := pCore 2 P
  let qO : P →* P ⧸ O := QuotientGroup.mk' O
  let F₀P : Subgroup P := F₀.subgroupOf P
  let TP : Subgroup P := T.subgroupOf P
  have hmapF : F₀P.map P.subtype = F₀ :=
    map_subgroupOf_subtype_eq F₀ P hF₀P
  have hmapT : TP.map P.subtype = T :=
    map_subgroupOf_subtype_eq T P hTP
  have hFperfectG : hktPResidual 2 F₀ = ⊤ := by
    rw [hF₀]
    exact twoResidualAmbient_has_top_twoResidual L
  let e₀ : F₀P ≃* F₀P.map P.subtype :=
    Subgroup.equivMapOfInjective F₀P P.subtype P.subtype_injective
  let e : F₀P ≃* F₀ := e₀.trans (MulEquiv.subgroupCongr hmapF)
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hresmap : (hktPResidual 2 F₀P).map e.toMonoidHom =
      hktPResidual 2 F₀ :=
    hktPResidual_map_of_surjective' e.toMonoidHom e.surjective
  have hFperfectP : hktPResidual 2 F₀P = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hresmap, hFperfectG]
    exact (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hrotation' : F₀P.map qO = qd.K := by
    simpa [F₀P, qO, O] using hrotation
  have hTmap' : TP.map qO =
      (T.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) := by
    rfl
  have hcommMap : F₀P.map qO ≤ (⁅F₀P, TP⁆).map qO := by
    rw [Subgroup.map_commutator]
    rw [hrotation', hTmap']
    exact qd.K_commutator
  have hOnormal : O.Normal := pCore_normal
  have hOtwo : IsPGroup 2 O := pCore_isPGroup
  have hcommP : F₀P ≤ ⁅F₀P, TP⁆ :=
    residualPerfect_le_commutator_of_quotient O F₀P TP
      hOnormal hOtwo hFperfectP hcommMap
  calc
    F₀ = F₀P.map P.subtype := hmapF.symm
    _ ≤ (⁅F₀P, TP⁆).map P.subtype := Subgroup.map_mono hcommP
    _ = ⁅F₀, T⁆ := by rw [Subgroup.map_commutator, hmapF, hmapT]

end Stellmacher.SectionThree

namespace Stellmacher.SectionThree

structure ActorLiftData
    {G : Type u} [Group G] [Finite G]
    (P A : Subgroup G) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A)
    (K : Subgroup (P ⧸ pCore 2 P)) where
  A₀ : Subgroup G
  A₀_le : A₀ ≤ A
  A₀_index_two : Nat.card A = 2 * Nat.card A₀
  A_factor : (A : Set G) =
    (Subgroup.zpowers a : Set G) * (A₀ : Set G)
  centralizes_K : ∀ (b : G) (hb : b ∈ A₀),
    ∀ r : P ⧸ pCore 2 P, r ∈ K →
      QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (A₀_le hb)⟩ * r =
        r * QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (A₀_le hb)⟩

noncomputable def actorLiftData
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (P₀ : Subgroup P)
    (hTP : T ≤ P) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A) (hA2 : IsPGroup 2 A)
    (qd : QuotientExtractionData P T A P₀ hTP hAP a haA) :
    ActorLiftData P A hAP a haA qd.K := by
  classical
  let O : Subgroup P := pCore 2 P
  let qO : P →* P ⧸ O := QuotientGroup.mk' O
  let AP : Subgroup P := A.subgroupOf P
  let Abar : Subgroup (P ⧸ O) := AP.map qO
  let fA0 : A →* P ⧸ O := qO.comp (Subgroup.inclusion hAP)
  let fA : A →* Abar := fA0.codRestrict Abar (fun b => by
    exact Subgroup.mem_map_of_mem qO
      (show ⟨(b : G), hAP b.property⟩ ∈ AP from b.property))
  have hfA : Function.Surjective fA := by
    intro y
    rcases y.property with ⟨b, hb, hby⟩
    let bA : A := ⟨(b : G), hb⟩
    refine ⟨bA, ?_⟩
    apply Subtype.ext
    exact hby
  let A₀A : Subgroup A := qd.Y.comap fA
  let A₀ : Subgroup G := A₀A.map A.subtype
  have hA₀coat : IsCoatom A₀A :=
    Subgroup.isCoatom_comap_of_surjective hfA qd.Y_coatom
  let aA : A := ⟨a, haA⟩
  have haA₀ : aA ∉ A₀A := by
    intro ha
    have ha' : fA aA ∈ qd.Y := ha
    let abar : Abar := ⟨qO ⟨a, hAP haA⟩,
      Subgroup.mem_map_of_mem qO
        (show ⟨a, hAP haA⟩ ∈ AP from haA)⟩
    have heq : fA aA = abar := by apply Subtype.ext; rfl
    have habarY : abar ∈ qd.Y := heq ▸ ha'
    apply qd.reflection_not_Y
    simpa only [abar, Abar, AP, qO, O] using habarY
  have hfactorA : (Set.univ : Set A) =
      (Subgroup.zpowers aA : Set A) * (A₀A : Set A) :=
    coatom_factorization_by_outside_element' A₀A aA hA2
      hA₀coat haA₀
  have hA₀le : A₀ ≤ A := Subgroup.map_subtype_le A₀A
  have hA₀index : Nat.card A = 2 * Nat.card A₀ := by
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let _ : Fact (IsPGroup 2 A) := ⟨hA2⟩
    have hcardQ : Nat.card (A ⧸ A₀A) = 2 :=
      card_quotient_coatom_eq_prime (p := 2) hA₀coat
    have hcardMap : Nat.card A₀ = Nat.card A₀A :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [hcardMap]
    simpa [hcardQ] using Subgroup.card_eq_card_quotient_mul_card_subgroup A₀A
  have hfactorG : (A : Set G) =
      (Subgroup.zpowers a : Set G) * (A₀ : Set G) := by
    ext g
    constructor
    · intro hg
      let gA : A := ⟨g, hg⟩
      have hgfac : gA ∈ (Subgroup.zpowers aA : Set A) * (A₀A : Set A) := by
        rw [← hfactorA]
        exact Set.mem_univ gA
      rcases hgfac with ⟨u, hu, v, hv, huv⟩
      refine ⟨(u : G), ?_, (v : G), ?_, ?_⟩
      · change (u : G) ∈ Subgroup.zpowers a
        have hu' : (u : G) ∈ (Subgroup.zpowers aA).map A.subtype :=
          Subgroup.mem_map_of_mem A.subtype hu
        rw [MonoidHom.map_zpowers] at hu'
        change (u : G) ∈ Subgroup.zpowers a at hu'
        exact hu'
      · exact Subgroup.mem_map_of_mem A.subtype hv
      · exact congrArg Subtype.val huv
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact A.mul_mem
        ((Subgroup.zpowers_le.2 haA) hu)
        (hA₀le hv)
  refine
    { A₀ := A₀
      A₀_le := hA₀le
      A₀_index_two := hA₀index
      A_factor := hfactorG
      centralizes_K := ?_ }
  intro b hb r hr
  have hb₀ := hb
  rcases hb with ⟨bA, hbA, hbAb⟩
  let y : qd.Y := ⟨fA bA, hbA⟩
  have hyz := qd.Y_centralizes y
  have hbval : (bA : G) = b := hbAb
  have hbase :
      QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩ * qd.z =
        qd.z * QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩ := by
    have hconj :
        QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩ * qd.z *
          (QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩)⁻¹ = qd.z := by
      change qO (Subgroup.inclusion hAP bA) * qd.z *
        (qO (Subgroup.inclusion hAP bA))⁻¹ = qd.z at hyz
      have harg : Subgroup.inclusion hAP bA =
          (⟨b, hAP (hA₀le hb₀)⟩ : P) := by
        apply Subtype.ext
        exact hbval
      rw [harg] at hyz
      exact hyz
    calc
      QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩ * qd.z =
          (QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩ * qd.z *
            (QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩)⁻¹) *
              QuotientGroup.mk' (pCore 2 P) ⟨b, hAP (hA₀le hb₀)⟩ := by group
      _ = qd.z * QuotientGroup.mk' (pCore 2 P)
            ⟨b, hAP (hA₀le hb₀)⟩ := by rw [hconj]
  rw [qd.K_cyclic, Subgroup.mem_zpowers_iff] at hr
  obtain ⟨n, rfl⟩ := hr
  exact (Commute.zpow_right ((commute_iff_eq _ _).mpr hbase) n).eq

end Stellmacher.SectionThree

namespace Stellmacher.SectionThree

noncomputable def liftQuotientExtractionData
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (P₀ : Subgroup P)
    (hTP : T ≤ P) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A) (hA2 : IsPGroup 2 A)
    (qd : QuotientExtractionData P T A P₀ hTP hAP a haA) :
    PrimitiveDihedralExtractionData P T A hAP a haA := by
  classical
  let ld := liftedRotationData P T A P₀ hTP hAP a haA qd
  let ad := actorLiftData P T A P₀ hTP hAP a haA hA2 qd
  let _ : Fact qd.p.Prime := ⟨qd.prime_p⟩
  have hnData : Nonempty {n : ℕ //
      0 < n ∧ Nat.card qd.K = qd.p ^ n} := by
    obtain ⟨n, hncard⟩ := qd.K_pgroup.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      have hKcard : Nat.card qd.K = 1 := by simpa [hn0] using hncard
      have hKbot : qd.K = ⊥ := Subgroup.card_eq_one.mp hKcard
      apply qd.K_not_residual_frattini
      rw [hKbot]
      exact bot_le
    exact ⟨⟨n, hnpos, hncard⟩⟩
  let nd := Classical.choice hnData
  let n : ℕ := nd.1
  have hnpos : 0 < n := nd.2.1
  have hncard : Nat.card qd.K = qd.p ^ n := nd.2.2
  have hrotation :
      (ld.F₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) =
        Subgroup.zpowers (QuotientGroup.mk' (pCore 2 P) ld.x) := by
    rw [ld.rotation_eq, ld.x_image, ← qd.K_cyclic]
  refine
    { x := ld.x
      x_mem_generated := ld.x_mem_generated
      A₀ := ad.A₀
      F₀ := ld.F₀
      p := qd.p
      n := n
      prime_p := qd.prime_p
      odd_p := qd.odd_p
      n_pos := hnpos
      A₀_le := ad.A₀_le
      A₀_index_two := ad.A₀_index_two
      A_factor := ad.A_factor
      residual_generated := ld.residual_generated
      F₀_le_P := ld.F₀_le_P
      rotation_eq := hrotation
      rotation_le_residual := by
        rw [ld.rotation_eq, qd.K_cyclic]
        exact Subgroup.zpowers_le.mpr qd.z_mem_residual
      rotation_not_residual_frattini := by
        rw [ld.rotation_eq]
        exact qd.K_not_residual_frattini
      rotation_card := by rw [ld.rotation_eq]; exact hncard
      reflected := ?_
      reflection_involution := qd.reflection_involution
      A₀_centralizes_rotation := ?_
      residual_not_phi := ?_
      residual_commutator := ?_ }
  · intro r hr
    apply qd.reflected r
    rw [← ld.rotation_eq]
    exact hr
  · intro b hb r hr
    apply ad.centralizes_K b hb r
    rw [← ld.rotation_eq]
    exact hr
  · exact lifted_residual_not_phi P T A P₀ hTP hAP a haA qd
      ld.F₀ ld.F₀_le_P ld.rotation_eq
  · exact lifted_residual_le_commutator P T A P₀ hTP hAP a haA qd
      (A ⊔ A.conjBy (ld.x : G)) ld.F₀ ld.residual_generated
        ld.F₀_le_P ld.rotation_eq

end Stellmacher.SectionThree

namespace Stellmacher.SectionThree

public theorem sylow_le_of_mem_PSet
    {G : Type u} [Group G]
    {S P : Subgroup G}
    (hP : P ∈ PSet (⊤ : Subgroup G) S) : S ≤ P := by
  obtain ⟨SP, hSP⟩ := hP.1.2.1
  rw [← hSP]
  exact Subgroup.map_subtype_le (SP : Subgroup P)

public noncomputable def solvablePrimitive_dihedralExtraction
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (T : Subgroup G) (hT : T ≤ S ∧ (T.subgroupOf S).Normal)
    (A : Subgroup G) (hA : A ≤ S)
    (a : G) (haA : a ∈ A) (haCore : a ∉ twoCoreAmbient P)
    (hPhiA : frattiniAmbient A ≤ twoCoreAmbient P)
    (hsolv : Group.IsSolvable P)
    (hTcore : ¬ T ≤ twoCoreAmbient P) :
    PrimitiveDihedralExtractionData P T A
      (hA.trans (sylow_le_of_mem_PSet hP)) a haA := by
  classical
  let hSP : S ≤ P := sylow_le_of_mem_PSet hP
  have hBData : Nonempty {B : Subgroup P //
      IsCoatom B ∧ S.subgroupOf P ≤ B ∧
        ∀ B' : Subgroup P, IsCoatom B' →
          S.subgroupOf P ≤ B' → B' = B} := by
    rcases hP.2 with ⟨B, hBcoatom, hSB, hBuniq⟩
    have hSPB : S.subgroupOf P ≤ B := by
      intro x hx
      have hxmap : (x : G) ∈ B.map P.subtype := hSB hx
      rcases hxmap with ⟨b, hb, hbx⟩
      have hbeq : b = x := P.subtype_injective hbx
      simpa [hbeq] using hb
    have hBuniq' : ∀ B' : Subgroup P, IsCoatom B' →
        S.subgroupOf P ≤ B' → B' = B := by
      intro B' hB' hSPB'
      apply hBuniq B' hB'
      intro s hs
      let sP : P := ⟨s, hSP hs⟩
      have hsSP : sP ∈ S.subgroupOf P := hs
      exact Subgroup.mem_map_of_mem P.subtype (hSPB' hsSP)
    exact ⟨⟨B, hBcoatom, hSPB, hBuniq'⟩⟩
  let bd := Classical.choice hBData
  let B : Subgroup P := bd.1
  have hB : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' →
        S.subgroupOf P ≤ B' → B' = B := bd.2
  have hP₀ : B.normalCore ≤ B ∧ B.normalCore.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ B.normalCore := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro N hN hNB
    exact @Subgroup.normal_le_normalCore P _ B N hN |>.mpr hNB
  have hnoncentral := quotient_reflection_not_centralizes_residual
    S h P hP B B.normalCore hB hP₀ A hA hSP a haA haCore hsolv
  let hTP : T ≤ P := hT.1.trans hSP
  let hAP : A ≤ P := hA.trans hSP
  let qd := quotientExtractionData_of_not_central S h P hP hSP B hB
    T hT A hA a haA haCore hPhiA hsolv hTcore hnoncentral
  have hA2 : IsPGroup 2 A := IsPGroup.to_le h.nontrivial_two_subgroup.2 hA
  exact liftQuotientExtractionData P T A B.normalCore hTP hAP a haA hA2 qd

end Stellmacher.SectionThree

end
