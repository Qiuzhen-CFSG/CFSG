module
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Descending a literal quotient action to an ambient subgroup image

Suppose F lies in P, a homomorphism f:P→K has kernel the restriction of
U, and F normalizes U. Any supplied literal conjugation action of F on
an abelian quotient U/Z descends to the subgroup image of F under f.
The descended map is onto the original action image, and the theorem
retains its formula on images of actual elements of F. The exact quotient
normality witness and action are parameters throughout.

The abelian quotient makes [U,U] lie in Z. Hence every F-element in U
acts trivially, by the existing quotient-conjugation kernel criterion.
The restricted f-map is onto its subgroup image and has kernel killed by
the given action, so the standard surjective-homomorphism lift supplies
the descended map and its compatibility. Surjectivity follows from the
original range-restriction map.

This source-neutral transport is used for the central Q_next/Qstar
action in Stellmacher (9.4), printed pp.51–52 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
universe u

public theorem quotient_conjugation_image_descent
    {G K : Type u} [Group G] [Group K]
    (P F U Z : Subgroup G) (hFP : F ≤ P)
    (hFU : F ≤ normalizer U)
    (f : P →* K) (hkernel : f.ker = U.subgroupOf P)
    (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∀ (_habelian : IsMulCommutative (U ⧸ Z.subgroupOf U))
      (action : F →* MulAut (U ⧸ Z.subgroupOf U)),
      (∀ g : F, ∀ u : U,
        action g (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(g : G)*(u : G)*(g : G)⁻¹,
              (mem_normalizer_iff.mp (hFU g.property) u).mp u.property⟩) →
      ∃ descended : ((F.subgroupOf P).map f) →* action.range,
        Function.Surjective descended ∧
        ∀ g : F,
          descended ⟨f ⟨g,hFP g.property⟩,
            mem_map.mpr ⟨⟨g,hFP g.property⟩,g.property,rfl⟩⟩ = action.rangeRestrict g := by
  let _ := hN
  dsimp only
  intro habelian action hact
  have hcommNative : _root_.commutator U ≤ Z.subgroupOf U :=
    Normal.quotient_commutative_iff_commutator_le.mp habelian
  have hcomm : ⁅U,U⁆ ≤ Z := by
    rw [← map_subtype_commutator U]
    rintro z ⟨u,hu,rfl⟩
    exact hcommNative hu
  have hkill : U.subgroupOf F ≤ action.ker :=
    quotient_conjugation_action_kills_commutator_layer F U Z U hN hFU hcomm action hact
  let q : F →* (F.subgroupOf P).map f :=
    { toFun := fun g => ⟨f ⟨g,hFP g.property⟩,
        mem_map.mpr ⟨⟨g,hFP g.property⟩,g.property,rfl⟩⟩
      map_one' := Subtype.ext (f.map_one)
      map_mul' := fun g h => Subtype.ext (f.map_mul ⟨g,hFP g.property⟩ ⟨h,hFP h.property⟩) }
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨g,hg,hgz⟩ := z.property
    exact ⟨⟨g,hg⟩,Subtype.ext hgz⟩
  have hker : q.ker ≤ action.rangeRestrict.ker := by
    intro g hg
    have hf : f ⟨g,hFP g.property⟩ = 1 := congrArg Subtype.val hg
    have hU : (g : G) ∈ U := by
      have hm : (⟨g,hFP g.property⟩ : P) ∈ f.ker := hf
      rwa [hkernel] at hm
    rw [MonoidHom.ker_rangeRestrict]
    exact hkill hU
  let descended := q.liftOfSurjective hq ⟨action.rangeRestrict,hker⟩
  have hcompat (g : F) : descended (q g) = action.rangeRestrict g :=
    MonoidHom.liftOfRightInverse_comp_apply q (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨action.rangeRestrict,hker⟩ g
  refine ⟨descended,?_,hcompat⟩
  intro z
  obtain ⟨g,rfl⟩ := action.rangeRestrict_surjective z
  exact ⟨q g,hcompat g⟩

end Subgroup
