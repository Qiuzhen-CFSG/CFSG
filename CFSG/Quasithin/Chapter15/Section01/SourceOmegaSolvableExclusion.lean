module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaQuotient
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaContradiction
/-!
# Excluding the original solvable full-Omega branch

The same quaternion core produced from the original H-star subgroup supplies
both point eights and the generated Omega quotient.  Restricting to the generated
subgroup preserves its literal embedding into G.  Pull back the two eights,
apply the binary orthogonal plane selector, and transport its conclusion back
along that embedding.  The source point-and-plane obstruction completes the
contradiction.  In particular, no quotient, coordinate, actor or splitting
premise remains in `source_fullOmega_solvable_false`.

Source: Aschbacher--Smith, the solvable branch of 15.1.11(1), printed p.1089.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The plane selector and source obstruction commute with the actual injective
embedding of the generated subgroup. -/
theorem source_two_point_eights_impossible_of_embedded_omega_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    (P V E F : Subgroup G) [IsElementaryAbelian 2 V]
    (hVcard : Nat.card V=16) (hST : P⊔V≤(T : Subgroup G))
    (hne : E≠F)
    (hEF : ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
      U≤P ∧ (T : Subgroup G)≤normalizer (U : Set G) ∧
      (P⊔V)⊓centralizer (U : Set G)=U ∧ Nonempty (ElementaryEightPointImage U))
    {K : Type*} [Group K] [Finite K] (i : K →* G) (hi : Function.Injective i)
    (hSi : P⊔V≤(i.range : Subgroup G))
    (q : K →* OrthogonalFourBinary.omega) (hq : Function.Surjective q)
    (hk : q.ker.map i=V) (e : q.ker ≃ OrthogonalFourBinary.Space)
    (hact : ∀ (g:K) (a:q.ker),e (MulAut.conjNormal g a)=q g • e a) : False := by
  let A := (P⊔V).comap i
  let U := E.comap i
  let W := F.comap i
  have hAmap : A.map i=P⊔V := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hSi
  have hlocal (D : Subgroup G) (hD : D∈({E,F} : Set (Subgroup G))) :
      (D.comap i).map i=D ∧ IsElementaryAbelian 2 (D.comap i) ∧
      Nat.card (D.comap i)=8 ∧ A≤normalizer (D.comap i : Set K) ∧
      A⊓centralizer (D.comap i : Set K)=D.comap i := by
    obtain ⟨he,hc,hP,hN,hcent,_⟩ := hEF D hD
    let := he
    have hDi : D≤(i.range : Subgroup G) := hP.trans (le_sup_left.trans hSi)
    have hmap : (D.comap i).map i=D := by
      rw [map_comap_eq]
      exact inf_eq_right.mpr hDi
    let ed : D.comap i ≃* D := ((D.comap i).equivMapOfInjective i hi).trans
      (MulEquiv.subgroupCongr hmap)
    refine ⟨hmap,IsElementaryAbelian.of_injective ed.toMonoidHom ed.injective,?_,?_,?_⟩
    · exact (Nat.card_congr ed.toEquiv).trans hc
    · exact (comap_mono (hST.trans hN)).trans (D.le_normalizer_comap i)
    · apply map_injective hi
      rw [←map_inf_centralizer_of_injective i hi,hAmap,hmap,hcent]
  obtain ⟨hUmap,hU,hUc,hUN,hUC⟩ := hlocal E (Or.inl rfl)
  obtain ⟨hWmap,hW,hWc,hWN,hWC⟩ := hlocal F (Or.inr rfl)
  have hUW : U≠W := by
    intro h
    apply hne
    exact hUmap.symm.trans ((congrArg (map i) h).trans hWmap)
  let ek : q.ker ≃* V := (q.ker.equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hk)
  have hker : IsElementaryAbelian 2 q.ker :=
    IsElementaryAbelian.of_injective ek.toMonoidHom ek.injective
  have hkcard : Nat.card q.ker=16 := (Nat.card_congr ek.toEquiv).trans hVcard
  have hkerA : q.ker≤A := by
    intro x hx
    have hV : i x ∈ V := hk ▸ mem_map_of_mem i hx
    exact mem_sup_right hV
  have hout := OrthogonalFourBinary.SylowGeometry.omega_two_elementaryEights_plane_image_map
    q hq e hact hker hkcard A U W hU hUc hW hWc hkerA hUN hWN hUC hWC hUW i hi
  change Nonempty (ElementaryEightPlaneImage ((E.comap i).map i)) ∨
    Nonempty (ElementaryEightPlaneImage ((F.comap i).map i)) at hout
  rw [hUmap,hWmap] at hout
  have finish (D : Subgroup G) (hD : D∈({E,F} : Set (Subgroup G)))
      (plane : Nonempty (ElementaryEightPlaneImage D)) : False := by
    obtain ⟨he,hc,hDP,hTN,_,point⟩ := hEF D hD
    let := he
    exact source_elementaryEight_plane_point_impossible hG T hempty D hc
      (hDP.trans (le_sup_left.trans hST)) hTN plane.some point.some
  exact hout.elim (finish E (Or.inl rfl)) (finish F (Or.inr rfl))

/-- Consume the exact quotient produced inside the chosen normalizer. -/
theorem source_two_point_eights_impossible_of_generated_omega_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    (P V E F : Subgroup G) [IsElementaryAbelian 2 V]
    (hVcard : Nat.card V=16) (hST : P⊔V≤(T : Subgroup G))
    (hne : E≠F)
    (hEF : ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
      U≤P ∧ (T : Subgroup G)≤normalizer (U : Set G) ∧
      (P⊔V)⊓centralizer (U : Set G)=U ∧ Nonempty (ElementaryEightPointImage U))
    {N : Subgroup G} {W Q : Subgroup N} [IsElementaryAbelian 2 W] [W.Normal]
    {c : ChosenOmegaCoordinates N W} {S : Sylow 2 OrthogonalFourBinary.omega}
    (d : OmegaGeneratedQuotient W c Q S)
    (hQ : Q.map N.subtype=P) (hW : W.map N.subtype=V) : False := by
  let L := Q⊔cubicCommutatorResidual Q
  let i : L →* G := N.subtype.comp L.subtype
  have hi : Function.Injective i := N.subtype_injective.comp L.subtype_injective
  have hSi : (P ⊔ V) ≤ MonoidHom.range i := by
    have hr : i.range=L.map N.subtype := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [hr,←hQ,←hW,←Subgroup.map_sup]
    exact map_mono (sup_le le_sup_left d.hWL)
  have hk : d.map.ker.map i=V := by
    change d.map.ker.map (N.subtype.comp L.subtype)=V
    rw [←map_map,d.map_ker,map_subgroupOf_eq_of_le d.hWL,hW]
  let _ : IsElementaryAbelian 2 (W.subgroupOf L) := IsElementaryAbelian.subgroupOf d.hWL
  let ek : d.map.ker ≃* W.subgroupOf L := MulEquiv.subgroupCongr d.map_ker
  let e : d.map.ker ≃ OrthogonalFourBinary.Space :=
    ek.toEquiv.trans (Additive.ofMul.trans d.coordinate.toEquiv)
  have hact (g:L) (a:d.map.ker) : e (MulAut.conjNormal g a)=d.map g • e a := by
    have hc := d.coordinate_apply g (Additive.ofMul (ek a))
    change d.coordinate (Additive.ofMul (ek (MulAut.conjNormal g a))) =
      (d.map g).val.val (d.coordinate (Additive.ofMul (ek a)))
    rw [←hc]
    apply congrArg d.coordinate
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  exact source_two_point_eights_impossible_of_embedded_omega_quotient hG T hempty
    P V E F hVcard hST hne hEF i hi hSi d.map d.map_surjective hk e hact

/-- The original solvable full-Omega branch is incompatible with the empty
faithful-local-component family. -/
theorem source_fullOmega_solvable_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable H) (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) → False := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  obtain ⟨P,hPT,_,_,hprod,hint,_,hX,E,F,hne,hEF⟩ :=
    source_fullOmega_solvable_two_point_eights hG T hM hJ hH hs hout ho
  let V := localModule T M
  let N := chosenNormalizer T M V
  have hTN : (T : Subgroup G) ≤ N :=
    sylow_le_chosenNormalizer T hM.1.2 (le_normalizer_conjugateSpanBy _ _)
  have hPN : P≤N := hPT.trans hTN
  have hVN : V≤N := module_le_chosenNormalizer T hM.1.2
    (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _)
  let a := source_15_1_1_qrcConfiguration hG T hM hH
  have hVT : V≤(T : Subgroup G) := a.module_le_core.trans (left_core_le_sylow a)
  have hVcard : Nat.card V=16 := by
    obtain ⟨x,_,_⟩ := ho.2.2.2.2
    calc
      Nat.card V=Nat.card (Additive V) := rfl
      _=Nat.card OrthogonalFourBinary.Space := Nat.card_congr x.toEquiv
      _=16 := by
        simp [OrthogonalFourBinary.Space,OrthogonalFourBinary.Plane,OrthogonalFourBinary.F]
  let hred := chosenNormalizer_reduced T hM.1.2 (localModule_le T hM.1.2)
    (le_normalizer_conjugateSpanBy _ _) (by
      have hZ : centralInvolutions T≤V := le_conjugateSpanBy _ _
      rw [inf_eq_left.mpr hZ]
      rfl)
  let _ := hred.normal
  let _ := hred.elementary
  let d := Classical.choice
    (source_fullOmega_solvable_omega_generated_quotient hG T hM hJ hH hs hout
      P hPT hprod hint ho hX)
  exact source_two_point_eights_impossible_of_generated_omega_quotient hG T hempty
    P V E F hVcard (sup_le hPT hVT) hne hEF d
    (map_subgroupOf_eq_of_le hPN) (map_subgroupOf_eq_of_le hVN)

/-- The solvable full-Omega case of the original core-containment assertion. -/
theorem source_fullOmega_solvable_module_le_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T=∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (hs : Group.IsSolvable H) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) → localModule T M ≤ H.pCoreIn 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  by_contra hout
  exact source_fullOmega_solvable_false hG T hempty hM hJ hH hs hout ho

end CFSG.Quasithin.Chapter15.Section01
