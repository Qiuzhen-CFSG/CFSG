module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic

/-!
# Lifting local derived factors and their coordinates

The cardinal-preserving quotient restriction lifts order-three factors uniquely. Preimage cardinalities lift the order-two coordinate to order four, and normality lifts through the injective restriction.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

private noncomputable def restrictedMapEquivOfNatCardMapEq
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (K : Subgroup G) (f : G →* Q)
    (hcard : Nat.card (K.map f) = Nat.card K) : K ≃* K.map f :=
  MulEquiv.ofBijective (restrictedMap K f) ⟨
    restrictedMap_injective_of_natCard_map_eq K f hcard,
    by
      rintro ⟨y, x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      exact hxy⟩

private noncomputable def liftSubgroupOfNatCardMapEq
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (K : Subgroup G) (f : G →* Q)
    (hcard : Nat.card (K.map f) = Nat.card K)
    (D : Subgroup Q) (_hD : D ≤ K.map f) : Subgroup G :=
  ((D.subgroupOf (K.map f)).comap
    (restrictedMapEquivOfNatCardMapEq K f hcard).toMonoidHom).map K.subtype

private theorem liftSubgroupOfNatCardMapEq_le
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (K : Subgroup G) (f : G →* Q)
    (hcard : Nat.card (K.map f) = Nat.card K)
    (D : Subgroup Q) (hD : D ≤ K.map f) :
    liftSubgroupOfNatCardMapEq K f hcard D hD ≤ K :=
  Subgroup.map_subtype_le _

private theorem liftSubgroupOfNatCardMapEq_map
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (K : Subgroup G) (f : G →* Q)
    (hcard : Nat.card (K.map f) = Nat.card K)
    (D : Subgroup Q) (hD : D ≤ K.map f) :
    (liftSubgroupOfNatCardMapEq K f hcard D hD).map f = D := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hy
    have hy' : (⟨y, hD hy⟩ : K.map f) ∈ D.subgroupOf (K.map f) := hy
    let e := restrictedMapEquivOfNatCardMapEq K f hcard
    let z : K := e.symm ⟨y, hD hy⟩
    have hz : z ∈ (D.subgroupOf (K.map f)).comap e.toMonoidHom := by
      change e z ∈ D.subgroupOf (K.map f)
      simpa [z, e] using hy'
    refine ⟨(z : G), ⟨z, hz, rfl⟩, ?_⟩
    have hez : e z = ⟨y, hD hy⟩ := by simp [z]
    exact congrArg Subtype.val hez

private theorem liftSubgroupOfNatCardMapEq_card
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (K : Subgroup G) (f : G →* Q)
    (hcard : Nat.card (K.map f) = Nat.card K)
    (D : Subgroup Q) (hD : D ≤ K.map f) :
    Nat.card (liftSubgroupOfNatCardMapEq K f hcard D hD) = Nat.card D := by
  let L := liftSubgroupOfNatCardMapEq K f hcard D hD
  have hfL : Function.Injective (f.domRestrict L) := by
    intro x y hxy
    have hxK : (x : G) ∈ K := liftSubgroupOfNatCardMapEq_le K f hcard D hD x.property
    have hyK : (y : G) ∈ K := liftSubgroupOfNatCardMapEq_le K f hcard D hD y.property
    have hxy' : restrictedMap K f ⟨x, hxK⟩ = restrictedMap K f ⟨y, hyK⟩ :=
      Subtype.ext hxy
    have hKinj := restrictedMap_injective_of_natCard_map_eq K f hcard hxy'
    exact Subtype.ext (congrArg (fun z : K => (z : G)) hKinj)
  have hmap : L.map f = D :=
    liftSubgroupOfNatCardMapEq_map K f hcard D hD
  let φ : L →* D :=
    (f.domRestrict L).codRestrict D fun x => hmap ▸ ⟨x, x.property, rfl⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact hfL (congrArg Subtype.val hxy)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : Q) ∈ L.map f := hmap.symm ▸ y.property
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Nat.card_congr (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).toEquiv

/-- The order of the preimage of a subgroup contained in the range is the
order of that subgroup times the order of the kernel.  We use this with the
restriction of the local quotient map to `S`: a coordinate of order two has
an order-two kernel, hence its preimage has order four. -/
private theorem natCard_comap_eq_mul_natCard_ker_of_le_range
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (f : G →* Q) (K : Subgroup Q) (hK : K ≤ f.range) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  let L : Subgroup G := K.comap f
  let φ : L →* K :=
    (f.domRestrict L).codRestrict K fun x => x.property
  have hφsurj : Function.Surjective φ := by
    intro y
    rcases hK y.property with ⟨x, hx⟩
    let z : L := ⟨x, by
      change f x ∈ K
      rw [hx]
      exact y.property⟩
    refine ⟨z, Subtype.ext ?_⟩
    exact hx
  have hkerLe : f.ker ≤ L := Subgroup.ker_le_comap f K
  have hφker : φ.ker = f.ker.subgroupOf L := by
    ext x
    change φ x = 1 ↔ f (x : G) = 1
    constructor
    · intro hx
      have hx' := congrArg (fun y : K => (y : Q)) hx
      change f (x : G) = 1 at hx'
      exact hx'
    · intro hx
      apply Subtype.ext
      change f (x : G) = 1
      exact hx
  have hkerCard : Nat.card φ.ker = Nat.card f.ker := by
    rw [hφker, natCard_subgroupOf_eq f.ker L hkerLe]
  have hmul := φ.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφsurj,
    Subgroup.card_top, hkerCard] at hmul
  simpa [L, Nat.mul_comm] using hmul.symm

/-- Lift an order-two subgroup of the image of `S` through a quotient whose
kernel on `S` is the order-two subgroup `A`.  The resulting ambient subgroup
`Aᵢ` lies between `A` and `S`, has order four, and maps back to the chosen
coordinate. -/
public theorem exists_order_four_coordinate_lift
    {G : Type u} [Group G] [Finite G]
    (S A H : Subgroup G) (hAS : A ≤ S) (hSH : S ≤ H)
    [hAnormal : (A.subgroupOf H).Normal]
    (Q : Subgroup (H ⧸ A.subgroupOf H))
    (hQ : Q ≤ (S.subgroupOf H).map
      (QuotientGroup.mk' (A.subgroupOf H)))
    (hAcard : Nat.card A = 2) (hQcard : Nat.card Q = 2) :
    ∃ Aᵢ : Subgroup G,
      A ≤ Aᵢ ∧ Aᵢ ≤ S ∧ Nat.card Aᵢ = 4 ∧
      (Aᵢ.subgroupOf H).map (QuotientGroup.mk' (A.subgroupOf H)) = Q := by
  let SH : Subgroup H := S.subgroupOf H
  let q : H →* H ⧸ A.subgroupOf H := QuotientGroup.mk' (A.subgroupOf H)
  let f : SH →* H ⧸ A.subgroupOf H := q.domRestrict SH
  let L : Subgroup SH := Q.comap f
  let ι : SH →* G := H.subtype.comp SH.subtype
  let Aᵢ : Subgroup G := L.map ι
  have hQrange : Q ≤ f.range := by
    intro y hy
    rcases hQ hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    exact hxy
  have hkerLeSH : A.subgroupOf H ≤ SH := by
    intro a ha
    exact hAS ha
  have hfker : f.ker = (A.subgroupOf H).subgroupOf SH := by
    dsimp only [f, q]
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have hfkerCard : Nat.card f.ker = 2 := by
    rw [hfker,
      natCard_subgroupOf_eq (A.subgroupOf H) SH hkerLeSH,
      natCard_subgroupOf_eq A H (hAS.trans hSH), hAcard]
  have hLcard : Nat.card L = 4 := by
    rw [natCard_comap_eq_mul_natCard_ker_of_le_range f Q hQrange,
      hQcard, hfkerCard]
  have hιinj : Function.Injective ι :=
    H.subtype_injective.comp SH.subtype_injective
  have hAᵢcard : Nat.card Aᵢ = 4 := by
    change Nat.card (L.map ι) = 4
    rw [Subgroup.card_map_of_injective hιinj, hLcard]
  have hAᵢleS : Aᵢ ≤ S := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hAᵢleH : Aᵢ ≤ H := hAᵢleS.trans hSH
  have hAleAᵢ : A ≤ Aᵢ := by
    intro a ha
    let aH : H := ⟨a, hSH (hAS ha)⟩
    let aSH : SH := ⟨aH, hAS ha⟩
    have haL : aSH ∈ L := by
      change q aH ∈ Q
      rw [show q aH = 1 by
        apply (QuotientGroup.eq_one_iff (N := A.subgroupOf H) (x := aH)).mpr
        exact ha]
      exact Q.one_mem
    exact ⟨aSH, haL, rfl⟩
  have hLmap : L.map f = Q := by
    change (Q.comap f).map f = Q
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hQrange
  have hAᵢsub : Aᵢ.subgroupOf H = L.map SH.subtype := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hAᵢleH]
    change L.map ι = (L.map SH.subtype).map H.subtype
    dsimp only [ι]
    rw [Subgroup.map_map]
  refine ⟨Aᵢ, hAleAᵢ, hAᵢleS, hAᵢcard, ?_⟩
  rw [hAᵢsub, Subgroup.map_map]
  exact hLmap

/-- Exact form used after the recursive call: a subgroup of the cardinal-
preserving quotient image of `W` has a unique lift inside `W`, with its
cardinality unchanged. -/
private theorem exists_local_factor_lift
    {G : Type u} [Group G] [Finite G]
    (W S : Subgroup G) (A : Subgroup G)
    (_hA : A ≤ W ⊔ S)
    [hAnormal : (A.subgroupOf (W ⊔ S)).Normal]
    (D : Subgroup (↥(W ⊔ S) ⧸ A.subgroupOf (W ⊔ S)))
    (hD : D ≤ (W.subgroupOf (W ⊔ S)).map
      (QuotientGroup.mk' (A.subgroupOf (W ⊔ S))))
    (hcard : Nat.card ((W.subgroupOf (W ⊔ S)).map
        (QuotientGroup.mk' (A.subgroupOf (W ⊔ S)))) = Nat.card W) :
    ∃ F : Subgroup G,
      F ≤ W ∧
      (F.subgroupOf (W ⊔ S)).map
          (QuotientGroup.mk' (A.subgroupOf (W ⊔ S))) = D ∧
      Nat.card F = Nat.card D := by
  let H : Subgroup G := W ⊔ S
  let AH : Subgroup H := A.subgroupOf H
  let q : H →* H ⧸ AH := QuotientGroup.mk' AH
  let K : Subgroup H := W.subgroupOf H
  have hKcard : Nat.card (K.map q) = Nat.card K := by
    change Nat.card ((W.subgroupOf (W ⊔ S)).map
      (QuotientGroup.mk' (A.subgroupOf (W ⊔ S)))) =
        Nat.card (W.subgroupOf (W ⊔ S))
    rw [natCard_subgroupOf_eq W (W ⊔ S) le_sup_left]
    exact hcard
  let L : Subgroup H := liftSubgroupOfNatCardMapEq K q hKcard D hD
  let F : Subgroup G := L.map H.subtype
  have hLleK : L ≤ K :=
    liftSubgroupOfNatCardMapEq_le K q hKcard D hD
  have hFleW : F ≤ W := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hLleK hy
  have hFleH : F ≤ H := Subgroup.map_subtype_le L
  have hsubgroupOf : F.subgroupOf H = L := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype]
    change F ⊓ H = F
    exact inf_eq_left.mpr hFleH
  refine ⟨F, hFleW, ?_, ?_⟩
  · change (F.subgroupOf H).map q = D
    rw [hsubgroupOf]
    exact liftSubgroupOfNatCardMapEq_map K q hKcard D hD
  · calc
      Nat.card F = Nat.card L :=
        Subgroup.card_map_of_injective H.subtype_injective
      _ = Nat.card D :=
        liftSubgroupOfNatCardMapEq_card K q hKcard D hD

/-- In particular, the lift of a local derived `oneOmega` factor has order
three in the ambient group.  Its order-four action is still only known on the
fixed-point module in the quotient; deciding whether the ambient commutator
escapes that fixed-point module is precisely the exceptional/generic split in
the source. -/
public theorem exists_local_order_three_factor_lift
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    (W S A : Subgroup G)
    (_hA : A ≤ W ⊔ S)
    [hAnormal : (A.subgroupOf (W ⊔ S)).Normal]
    [MulDistribMulAction (↥(W ⊔ S) ⧸ A.subgroupOf (W ⊔ S)) V]
    (D : Subgroup (↥(W ⊔ S) ⧸ A.subgroupOf (W ⊔ S)))
    (hDomega : oneOmega
      (G := ↥(W ⊔ S) ⧸ A.subgroupOf (W ⊔ S)) (V := V) D)
    (hD : D ≤ (W.subgroupOf (W ⊔ S)).map
      (QuotientGroup.mk' (A.subgroupOf (W ⊔ S))))
    (hcard : Nat.card ((W.subgroupOf (W ⊔ S)).map
        (QuotientGroup.mk' (A.subgroupOf (W ⊔ S)))) = Nat.card W) :
    ∃ F : Subgroup G,
      F ≤ W ∧
      (F.subgroupOf (W ⊔ S)).map
          (QuotientGroup.mk' (A.subgroupOf (W ⊔ S))) = D ∧
      Nat.card F = 3 := by
  obtain ⟨F, hFW, hFmap, hFcard⟩ :=
    exists_local_factor_lift W S A _hA D hD hcard
  exact ⟨F, hFW, hFmap, hFcard.trans hDomega.2.1⟩

/-- The commutator subgroup used in the local quotient is normal in its
join with `S`.  This is a direct normalizer argument and does not require
commutativity of `S`. -/
public theorem local_commutator_normal_in_join
    {G : Type*} [Group G]
    (X S : Subgroup G) :
    let W := ⁅X, S⁆
    (W.subgroupOf (W ⊔ S)).Normal := by
  dsimp only
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer
    (Subgroup.normalizer_commutator_ge_right X S)

/-- A cardinal-preserving quotient lift of a normal quotient subgroup is
normal in the local join, provided the whole subgroup being lifted is
normal there. -/
public theorem local_factor_lift_normal
    {G : Type u} [Group G] [Finite G]
    (W S A F : Subgroup G)
    (hWA : W ≤ W ⊔ S)
    [hAnormal : (A.subgroupOf (W ⊔ S)).Normal]
    (hWnormal : (W.subgroupOf (W ⊔ S)).Normal)
    (hFW : F ≤ W)
    (hcard : Nat.card ((W.subgroupOf (W ⊔ S)).map
        (QuotientGroup.mk' (A.subgroupOf (W ⊔ S)))) = Nat.card W)
    (hmapNormal : ((F.subgroupOf (W ⊔ S)).map
        (QuotientGroup.mk' (A.subgroupOf (W ⊔ S)))).Normal) :
    (F.subgroupOf (W ⊔ S)).Normal := by
  let H : Subgroup G := W ⊔ S
  let AH : Subgroup H := A.subgroupOf H
  let q : H →* H ⧸ AH := QuotientGroup.mk' AH
  let K : Subgroup H := W.subgroupOf H
  let L : Subgroup H := F.subgroupOf H
  have hLK : L ≤ K := fun x hx => hFW hx
  have hKcard : Nat.card (K.map q) = Nat.card K := by
    change Nat.card ((W.subgroupOf (W ⊔ S)).map
      (QuotientGroup.mk' (A.subgroupOf (W ⊔ S)))) =
        Nat.card (W.subgroupOf (W ⊔ S))
    exact hcard.trans (natCard_subgroupOf_eq W (W ⊔ S) hWA).symm
  exact normal_of_map_normal_of_le_of_inf_ker_eq_bot K L q hWnormal hLK
    hmapNormal (inf_ker_eq_bot_of_natCard_map_eq K q hKcard)

/-- In an internal product which is the whole group, the derived subgroup
of every factor is normal in the ambient group. -/
public theorem derived_factor_normal_of_internalDirectProduct_eq_top
    {G : Type u} [Group G]
    (K T : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct (K ⊔ T) F)
    (htop : K ⊔ T = ⊤)
    (E : Subgroup G) (hE : E ∈ F) :
    ((commutator (↑E)).map E.subtype).Normal := by
  have hEtop := hprod.2.1 E hE
  rw [htop] at hEtop
  have htopSurj : Function.Surjective (⊤ : Subgroup G).subtype := by
    intro g
    exact ⟨⟨g, trivial⟩, rfl⟩
  have hEnormal : E.Normal := by
    have hn := hEtop.map (⊤ : Subgroup G).subtype htopSurj
    simpa only [Subgroup.map_subgroupOf_eq_of_le le_top] using hn
  let _ : E.Normal := hEnormal
  simpa only [Subgroup.map_subtype_commutator] using
    (inferInstance : (⁅E, E⁆ : Subgroup G).Normal)

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
