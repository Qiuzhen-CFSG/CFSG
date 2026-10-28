module

public import Theory.AlgebraicGroup.Solvable.Nilpotent
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.DiagonalizableCentralizerSurjectivity
public import Theory.AlgebraicGroup.Tori.SubgroupZariskiClosureZpowersDiagonalizable
public import Theory.AlgebraicGroup.Tori.UnipotentIntersection

/-!
# Torus complements in connected solvable algebraic groups

This module proves the existence part of Borel, *Linear Algebraic Groups*,
Chapter III, Theorem 10.6(4): over an algebraically closed field, a connected
solvable algebraic group is the pointwise product of its connected unipotent
radical and a maximal subtorus, and the two factors have trivial intersection.
The exposed `IsTorusComplement` predicate packages the factorization and
intersection properties for the later conjugacy theorem.

The proof follows Borel's induction on dimension.  The nilpotent case is the
direct-product theorem from 10.6(3).  Otherwise, a noncentral semisimple point
has a proper centralizer.  The identity component of the centralizer of its
diagonalizable cyclic closure maps onto the diagonal torus quotient by the
formalized 9.6 surjectivity theorem.  Induction supplies a torus in that
identity component; its ambient image still covers the quotient.  The kernel
of the diagonal map is precisely the unipotent radical, which gives the
factorization, while semisimple-unipotent disjointness gives trivial
intersection and hence maximality.

The maximality notion used here is the low-level `IsMaximalTorus` definition
from `Tori.Basic`; this module deliberately remains below the later
`Tori.Maximal` development in the import graph.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A torus complement covers the ambient group together with the indicated
closed subgroup and meets that subgroup trivially. -/
@[expose]
public def IsTorusComplement
    {G : Variety k} [AlgebraicGroup G]
    (T U : ClosedSubgroup G) : Prop :=
  IsSubtorus T ∧
    (∀ x : Variety.Point G, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u) ∧
    T.toSubgroup ⊓ U.toSubgroup = ⊥

/-- A torus factor covering the ambient group with a unipotent subgroup is
maximal among all ambient subtori. -/
public lemma IsTorusComplement.isMaximalTorus_of_unipotent
    {G : Variety k} [AlgebraicGroup G]
    {T U : ClosedSubgroup G}
    (h : IsTorusComplement T U)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    IsMaximalTorus T := by
  refine ⟨h.1, ?_⟩
  intro S hS hTS
  apply SetLike.coe_injective
  apply Set.Subset.antisymm ?_ hTS
  intro x hxS
  obtain ⟨t, u, ht, hu, htu⟩ := h.2.1 x
  have htS : t ∈ S.toSubgroup := hTS ht
  have huS : u ∈ S.toSubgroup := by
    have hmul := S.toSubgroup.mul_mem (S.toSubgroup.inv_mem htS) hxS
    rw [htu] at hmul
    simpa [mul_assoc] using hmul
  have huOne : u = 1 := by
    have huInf : u ∈ S.toSubgroup ⊓ U.toSubgroup := ⟨huS, hu⟩
    rw [subtorus_inf_unipotent_eq_bot S U hS hU] at huInf
    exact Subgroup.mem_bot.mp huInf
  rw [htu, huOne, mul_one]
  exact ht

omit [IsAlgClosed k] in
private lemma closedSubgroup_carrier_isConnected_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace
      {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem exists_torusComplement_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ U : ClosedSubgroup G, IsUnipotentRadicalSubgroup U ∧
      Variety.IsConnected U.carrierVariety ∧
      ∃ T : ClosedSubgroup G, IsTorusComplement T U := by
  induction hdim : Cardinal.toNat (Variety.dimension G)
      using Nat.strong_induction_on generalizing G with
  | h d ih =>
      by_cases hnilpotent : Group.IsNilpotent (Variety.Point G)
      · obtain ⟨U, hU, hUconn, T, hT, -, hTU, hfactor⟩ :=
          exists_subtorus_complement_of_isNilpotent_of_solvable_connected
            hsolvable hconnected hnilpotent
        exact ⟨U, hU, hUconn, T, hT, hfactor, hTU⟩
      · obtain ⟨s, hsSemi, hsNoncentral⟩ :=
          exists_noncentral_semisimpleElement_of_not_nilpotent
            hsolvable hconnected hnilpotent
        let D : ClosedSubgroup G :=
          subgroupZariskiClosure G (Subgroup.zpowers s)
        have hDdiag : IsDiagonalizableClosedSubgroup D := by
          simpa [D] using
            subgroupZariskiClosure_zpowers_isDiagonalizable_of_semisimple s hsSemi
        have hsD : s ∈ D.toSubgroup := by
          change s ∈ closure (Subgroup.zpowers s : Set (Variety.Point G))
          exact subset_closure (Subgroup.mem_zpowers s)
        let C : ClosedSubgroup G := D.centralizer.identityComponentAmbient
        letI : AlgebraicGroup C.carrierVariety := C.carrierAlgebraicGroup
        have hCconnSet : _root_.IsConnected
            (C : Set (Variety.Point G)) := by
          simpa [C] using D.centralizer.identityComponentAmbient_isConnected
        have hCconn : Variety.IsConnected C.carrierVariety :=
          closedSubgroup_carrier_isConnected_local C hCconnSet
        have hCne : C ≠ ClosedSubgroup.top := by
          intro hCtop
          apply hsNoncentral
          rw [Subgroup.mem_center_iff]
          intro g
          have hgC : g ∈ C.toSubgroup := by
            rw [hCtop]
            trivial
          have hgCentralizer : g ∈ D.centralizer.toSubgroup :=
            D.centralizer.identityComponentAmbient_le hgC
          exact ((Subgroup.mem_centralizer_iff.mp hgCentralizer) s hsD).symm
        have hTopconn : _root_.IsConnected
            (ClosedSubgroup.top (G := G) : Set (Variety.Point G)) := by
          change _root_.IsConnected (Set.univ : Set (Variety.Point G))
          exact hconnected
        have hCdimlt : Variety.dimension C.carrierVariety <
            Variety.dimension G := by
          have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne
            C ClosedSubgroup.top (fun _ _ => trivial) hCne hCconnSet hTopconn
          have hTopdim : Variety.dimension
              (ClosedSubgroup.top : ClosedSubgroup G).carrierVariety =
              Variety.dimension G :=
            (closedSubgroup_dimension_eq_iff_contains_identityComponent G
              (ClosedSubgroup.top : ClosedSubgroup G)).2 (by
                intro x _
                trivial)
          rwa [hTopdim] at hlt
        have hCnatlt : Cardinal.toNat (Variety.dimension C.carrierVariety) < d := by
          rw [← hdim]
          exact Cardinal.toNat_lt_toNat hCdimlt
            (variety_dimension_lt_aleph0 G)
        letI : Group.IsSolvable (Variety.Point G) := hsolvable
        have hCsolvable : Group.IsSolvable (Variety.Point C.carrierVariety) :=
          Group.isSolvable_of_isSolvable_injective C.inclusion_injective
        obtain ⟨UC, hUC, hUCconn, TC, hTC⟩ :=
          ih _ hCnatlt hCsolvable hCconn rfl
        obtain ⟨n, hn, H, hIso⟩ :=
          exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
            hsolvable hconnected
        letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
        let P : TriangularPresentation G :=
          { n := n
            positive := hn
            subgroup := H
            iso := Classical.choice hIso }
        let U : ClosedSubgroup G := P.unipotentRadical
        letI : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
        have hU : IsUnipotentRadicalSubgroup U := by
          intro x
          exact P.mem_unipotentRadical_iff_characteristicFree x
        have hUconn : Variety.IsConnected U.carrierVariety :=
          hU.isConnected_of_solvable_connected hsolvable hconnected
        have hUunipotent : IsUnipotentAlgebraicGroup U.carrierVariety :=
          hU.isUnipotent_of_solvable_connected hsolvable hconnected
        let Q : Variety k := P.diagonalImage.carrierVariety
        letI : AlgebraicGroup Q := P.diagonalImage.carrierAlgebraicGroup
        let f : AlgebraicGroup.Morphism G Q := P.diagonalImageMorphism
        have hQ : IsTorus Q := P.diagonalImage_isTorus hconnected
        have hinc (x : Variety.Point G) :
            P.diagonalImage.inclusion.onPoints (f.onPoints x) =
              P.diagonalMorphism.onPoints x := by
          simpa only [f, Q, TriangularPresentation.diagonalImageMorphism] using
            (AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
              P.diagonalMorphism P.diagonalImage
              (fun z => by
                change P.diagonalMorphism.onPoints z ∈ P.diagonalMorphism.image
                exact ⟨z, rfl⟩) x)
        have hfSurj : Function.Surjective f.onPoints := by
          intro y
          have hy := (P.diagonalImage.pointEquiv y).property
          change (P.diagonalImage.pointEquiv y).val ∈
            P.diagonalMorphism.image at hy
          obtain ⟨x, hx⟩ := hy
          refine ⟨x, ?_⟩
          apply P.diagonalImage.inclusion_injective
          rw [hinc]
          exact hx
        have hfCsurj : Function.Surjective
            (f.comp C.inclusion).onPoints := by
          simpa [C] using
            f.diagonalizableCentralizer_identityComponent_surjective
              hfSurj hQ D hDdiag
        letI : AlgebraicGroup UC.carrierVariety := UC.carrierAlgebraicGroup
        letI : AlgebraicGroup TC.carrierVariety := TC.carrierAlgebraicGroup
        let tAmb : AlgebraicGroup.Morphism TC.carrierVariety G :=
          C.inclusion.comp TC.inclusion
        let T : ClosedSubgroup G := tAmb.imageClosedSubgroup
        have hT : IsSubtorus T := morphism_image_isTorus tAmb hTC.1
        have hfUCOne (u : Variety.Point C.carrierVariety)
            (hu : u ∈ UC.toSubgroup) :
            f.onPoints (C.inclusion.onPoints u) = 1 := by
          have huC : IsUnipotentElement C.carrierVariety u := (hUC u).mp hu
          have huG : IsUnipotentElement G (C.inclusion.onPoints u) :=
            morphism_preserves_unipotentElement C.inclusion u huC
          have huQ : IsUnipotentElement Q
              (f.onPoints (C.inclusion.onPoints u)) :=
            morphism_preserves_unipotentElement f _ huG
          exact semisimple_unipotent_eq_one _
            (hQ.all_semisimple _) huQ
        have hfactor : ∀ x : Variety.Point G, ∃ t u,
            t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u := by
          intro x
          obtain ⟨c, hc⟩ := hfCsurj (f.onPoints x)
          obtain ⟨t, u, ht, hu, hctu⟩ := hTC.2.1 c
          let tG : Variety.Point G := C.inclusion.onPoints t
          have htT : tG ∈ T.toSubgroup := by
            change tG ∈ tAmb.image
            let tTC : Variety.Point TC.carrierVariety :=
              TC.pointEquiv.symm ⟨t, ht⟩
            refine ⟨tTC, ?_⟩
            change C.inclusion.onPoints (TC.inclusion.onPoints tTC) =
              C.inclusion.onPoints t
            exact congrArg C.inclusion.onPoints (by
              change (TC.pointEquiv tTC).val = t
              simp [tTC])
          have hft : f.onPoints tG = f.onPoints x := by
            calc
              f.onPoints tG =
                  f.onPoints (C.inclusion.onPoints t) *
                    f.onPoints (C.inclusion.onPoints u) := by
                      rw [hfUCOne u hu, mul_one]
              _ = f.onPoints (C.inclusion.onPoints (t * u)) := by
                    rw [map_mul, map_mul]
              _ = f.onPoints (C.inclusion.onPoints c) := by rw [hctu]
              _ = f.onPoints x := hc
          let uG : Variety.Point G := tG⁻¹ * x
          have hfu : f.onPoints uG = 1 := by
            simp [uG, map_mul, map_inv, hft]
          have huU : uG ∈ U.toSubgroup := by
            change P.diagonalMorphism.onPoints uG = 1
            calc
              P.diagonalMorphism.onPoints uG =
                  P.diagonalImage.inclusion.onPoints (f.onPoints uG) :=
                    (hinc uG).symm
              _ = P.diagonalImage.inclusion.onPoints 1 := by rw [hfu]
              _ = 1 := P.diagonalImage.inclusion.map_one
          refine ⟨tG, uG, htT, huU, ?_⟩
          simp [uG]
        have hTU : T.toSubgroup ⊓ U.toSubgroup = ⊥ :=
          subtorus_inf_unipotent_eq_bot T U hT hUunipotent
        exact ⟨U, hU, hUconn, T, hT, hfactor, hTU⟩

/-- A connected solvable algebraic group has a maximal subtorus complement to
its connected unipotent radical. -/
public theorem exists_maximalTorus_complement_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ U : ClosedSubgroup G, IsUnipotentRadicalSubgroup U ∧
      Variety.IsConnected U.carrierVariety ∧
      ∃ T : ClosedSubgroup G,
        IsTorusComplement T U ∧ IsMaximalTorus T := by
  obtain ⟨U, hU, hUconn, T, hT⟩ :=
    exists_torusComplement_of_solvable_connected hsolvable hconnected
  have hUunipotent : IsUnipotentAlgebraicGroup U.carrierVariety :=
    hU.isUnipotent_of_solvable_connected hsolvable hconnected
  exact ⟨U, hU, hUconn, T, hT,
    hT.isMaximalTorus_of_unipotent hUunipotent⟩

end Theory.AlgebraicGroup
