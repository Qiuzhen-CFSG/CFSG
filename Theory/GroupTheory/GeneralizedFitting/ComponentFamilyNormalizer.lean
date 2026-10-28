module
public import Theory.GroupTheory.GeneralizedFitting.ComponentNormalizerDescent
public import Theory.GroupTheory.GeneralizedFitting.LayerSylowContainment

/-!
# Sylow normalizers of selected component products

A p-subgroup containing a Sylow subgroup of every selected component
contains a Sylow subgroup of their commuting product. If this selected
product is normal, each component of its Sylow-two normalizer centralizes
the normal Sylow subgroup. The two-Schreier fixed-Sylow theorem then makes
it centralize each selected component. It descends through the normal
centralizer to a component of the original group, distinct from every
selected component. Central intersections between factors are allowed.

Source: Aschbacher--Smith 2.5.3(4), printed pp.552--553, removal of the
Bender component subfamily, using GLS II B.5.16.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A p-subgroup meeting every selected component in a Sylow subgroup meets
their actual product in a Sylow subgroup. -/
theorem exists_component_family_sylow_eq_inf {p : ℕ} [Fact p.Prime]
    (F : Set (Subgroup G)) (hF : ∀ L ∈ F, IsComponent G L)
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hL : ∀ L ∈ F, ∃ P : Sylow p L, (P : Subgroup L).map L.subtype ≤ Q) :
    ∃ P : Sylow p ↥(sSup F : Subgroup G),
      (P : Subgroup ↥(sSup F : Subgroup G)).map (sSup F).subtype = sSup F ⊓ Q := by
  classical
  let I := {L : Subgroup G // L ∈ F}
  let C : I → Subgroup G := Subtype.val
  have he : (⨆ i, C i) = sSup F := (sSup_eq_iSup' _).symm
  have hc : Pairwise fun i j : I => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    have hh := (hF i.val i.property).commutator_eq_bot_of_ne (hF j.val j.property)
      (fun h => hij (Subtype.ext h))
    exact ((commutator_eq_bot_iff_le_centralizer.mp hh) hx y hy).symm
  choose P hP using fun i : I => hL i.val i.property
  obtain ⟨R, hR⟩ := exists_sylow_iSup_le_of_commuting C hc P Q hP
  let e := MulEquiv.subgroupCongr he
  let T := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : (T : Subgroup ↥(sSup F : Subgroup G)).map (sSup F).subtype ≤ Q := by
    change ((R : Subgroup (⨆ i, C i : Subgroup G)).map e.toMonoidHom).map _ ≤ Q
    rw [map_map]
    exact hR
  have hi : Q.subgroupOf (sSup F) = (T : Subgroup ↥(sSup F : Subgroup G)) :=
    T.is_maximal' hQ.comap_subtype (map_le_iff_le_comap.mp hT)
  refine ⟨T, ?_⟩
  rw [← hi, subgroupOf_map_subtype, inf_comm]

/-- Components in a normal selected-component product's Sylow normalizer
are actual original components and centralize every removed factor. -/
theorem components_descend_from_component_family_normalizer
    (hS : HasTwoSchreier G)
    (F : Set (Subgroup G)) (hF : ∀ D ∈ F, IsComponent G D)
    [(sSup F).Normal]
    (heven : ∀ D ∈ F, 2 ∣ Nat.card (D ⧸ center D))
    (P : Sylow 2 ↥(sSup F : Subgroup G)) :
    let Q := (P : Subgroup ↥(sSup F : Subgroup G)).map (sSup F).subtype
    let X := normalizer (Q : Set G)
    ∀ K : Subgroup X, IsComponent X K →
      IsComponent G (K.map X.subtype) ∧
      K.map X.subtype ≤ centralizer ((sSup F : Subgroup G) : Set G) ∧
      ∀ D ∈ F, K.map X.subtype ≠ D := by
  let E := sSup F
  let Q := (P : Subgroup E).map E.subtype
  let X := normalizer (Q : Set G)
  change ∀ K : Subgroup X, IsComponent X K → _
  intro K hK
  let A := K.map X.subtype
  let C := centralizer (E : Set G)
  let : IsQuasisimple K := hK.2
  let : Group.IsPerfect A := Group.IsPerfect.map X.subtype
  have hQp : IsPGroup 2 Q := P.isPGroup'.map E.subtype
  let : (Q.subgroupOf X).Normal := inferInstance
  let : Group.IsNilpotent (Q.subgroupOf X) := (hQp.comap_subtype (K := X)).isNilpotent
  have hKQ := hK.le_centralizer_normal_solvable (Q.subgroupOf X)
  have hAQ : A ≤ centralizer (Q : Set G) := by
    rintro a ⟨k, hk, rfl⟩ q hq
    exact congrArg Subtype.val (hKQ hk ⟨q, Q.le_normalizer hq⟩ hq)
  have hAC : A ≤ C := by
    apply le_centralizer_iff.mpr
    apply sSup_le
    intro D hd
    have hD := hF D hd
    obtain ⟨S, hS₀⟩ := P.exists_comap_subtype_eq
    obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
    have hTQ : (T : Subgroup D).map D.subtype ≤ Q := by
      rintro _ ⟨d, hdT, rfl⟩
      have hdS : (d : G) ∈ (S : Subgroup G) := by rwa [hT] at hdT
      have hdE : (d : G) ∈ E := (le_sSup hd) d.property
      refine ⟨⟨d, hdE⟩, ?_, rfl⟩
      rw [← hS₀]
      exact hdS
    have hAT : A ≤ centralizer ((T : Subgroup D).map D.subtype : Set G) :=
      hAQ.trans (centralizer_le hTQ)
    exact le_centralizer_iff.mp (perfect_centralizes_component_of_fixed_sylow hS hD T A
      (hAT.trans (hD.centralizer_sylow_le_normalizer T (heven D hd))) hAT)
  have hCX : C ≤ X := (centralizer_le (map_subtype_le _)).trans
    (Subgroup.centralizer_le_normalizer _)
  have hrel : IsComponentIn A X := by
    refine ⟨map_subtype_le _, ?_⟩
    change IsComponent X ((K.map X.subtype).comap X.subtype)
    rwa [comap_map_eq_self_of_injective X.subtype_injective]
  have hCrel := hrel.restrict hAC hCX
  refine ⟨⟨Subgroup.IsSubnormal.trans hAC hCrel.2.1
    (inferInstance : C.Normal).isSubnormal, hCrel.quasisimple⟩, hAC, ?_⟩
  intro D hd he
  let : IsQuasisimple D := (hF D hd).2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  change A = D at he
  have hDC : D ≤ C := he ▸ hAC
  have hDD : D ≤ centralizer (D : Set G) :=
    hDC.trans (centralizer_le (le_sSup hd))
  exact Group.IsPerfect.not_isMulCommutative D (le_centralizer_iff_isMulCommutative.mp hDD)

end Theory.GroupTheory
