module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSolvableSelection
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.StrictAction.Geometry
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSolvableSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Original dihedral selection beyond solvable H-star groups

An order-two image of V in H/J gives the genuine lifted involution-pair
witness. The nonsolvable odd PSL2, PSL3 and PSU3 component rows give the
same witness from their actual full-core quotient models. The PSL3 case
restricts the original TI hypothesis before quotienting. Transport through
H's inclusion preserves the original V, internal conjugator, Sylow and
normal core; the selected parameter is one.

The final theorem applies the original component catalogue. It either
constructs this selected pair or supplies an actual generating C-component
whose normal branch has a binary model in the same H/J. The Chapter 12
consumer excludes the first alternative for every higher-field tensor and
retains the full field-four fixed-subgroup and residual data otherwise.
The remaining binary selection and field-four centralizer argument are
not asserted here.

The internal import reuses the checked dihedral inclusion transport without
changing the earlier module's public boundary.
Source: Aschbacher–Smith E.2.2, E.2.7–9 and 8.2.2–5,
printed pp.215–222,714–717 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]

/-- An actual normal component supplement in H, with its odd-characteristic
model marked through the full core of M intersect H. The exceptional PSL2
fields five and nine belong to the binary source rows and are excluded here. -/
@[expose] def OddNormalComponent (H T M : Subgroup G) : Prop :=
  ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧ K ⊔ T.subgroupOf H = ⊤ ∧
    ((∃ p d : ℕ, p.Prime ∧ Odd p ∧ 5 < p^d ∧ p^d ≠ 9 ∧
      ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (localCore M H))) 2 (p^d)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (localCore M H))) 3 p ∨
       ClassicalGroup.IsPSU (K.map (QuotientGroup.mk' (localCore M H))) 3 p)))

private theorem intrinsic_source_data
    {K : GroupClass} {H T M V : Subgroup G}
    (h : HypothesisE28 K H T M V)
    (R : Sylow 2 H) (hR : (R : Subgroup H) = T.subgroupOf H)
    (hP : ChapterB.IsMinimalParabolicOver R ⊤)
    (hM : M.subgroupOf H = ChapterB.minimalParabolicMax R hP) :
    V.subgroupOf H ≤ R ∧
    ((V.subgroupOf H).subgroupOf (R : Subgroup H)).Normal ∧
    V.subgroupOf H ≤ (ChapterB.minimalParabolicMax R hP).pCoreIn 2 ∧
    ¬ V.subgroupOf H ≤ ChapterB.minimalParabolicCore R hP := by
  have hVH := h.le_sylow.trans h.le_ambient
  have hVR : V.subgroupOf H ≤ R := by rw [hR]; exact comap_mono h.le_sylow
  refine ⟨hVR,?_,?_,?_⟩
  · apply (normal_subgroupOf_iff_le_normalizer hVR).mpr
    rw [hR,←subgroupOf_normalizer_eq hVH]
    exact comap_mono ((normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow)
  · rw [←hM]
    intro v hv
    obtain ⟨x,hx,he⟩ := h.le_local_core hv
    exact ⟨x,hx,Subtype.ext he⟩
  · intro hc
    apply h.outside_core
    have hh := map_mono (f := H.subtype) hc
    rw [map_subgroupOf_eq_of_le hVH] at hh
    simpa only [ChapterB.minimalParabolicCore,←hM] using hh

/-- An order-two image in the original star quotient supplies a dihedral
family even when H is nonsolvable. -/
theorem exists_dihedral_family_of_star_order_two
    {K : GroupClass} {H T M V : Subgroup G}
    (h : HypothesisE28 K H T M V)
    (hc : Nat.card (starImage M H V) = 2) :
    ∃ I : Subgroup G, Family H T M V I 1 ∧
      RankOneAlternative (Star M I) (starImage M I M) 1 := by
  let := h.elementary
  have hVH := h.le_sylow.trans h.le_ambient
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h.minimal
  obtain ⟨hVR,hn,hcore,_⟩ := intrinsic_source_data h R hR hP hM
  have hc' : Nat.card ((V.subgroupOf H).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))) = 2 := by
    change Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (M.subgroupOf H).normalCore)) = 2 at hc
    rw [hM] at hc
    exact hc
  obtain ⟨w⟩ := Witnesses.Involution.source_star_order_two R hP (V.subgroupOf H) hVR hn hcore hc'
  rw [←hM] at w
  have hne : V ≠ ⊥ := by intro he; exact h.outside_core (he ▸ bot_le)
  exact family_of_dihedral_witness hVH h.elementary hne h.le_sylow R hR w

/-- Every original odd normal-component row supplies its actual dihedral
family. TI is restricted before quotienting in the odd PSL3 case. -/
theorem exists_dihedral_family_of_odd_normal_component
    {H T M V : Subgroup G}
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (ho : OddNormalComponent H T M)
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V) :
    ∃ I : Subgroup G, Family H T M V I 1 ∧
      RankOneAlternative (Star M I) (starImage M I M) 1 := by
  let := h.elementary
  have hVH := h.le_sylow.trans h.le_ambient
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h.minimal
  obtain ⟨hVR,hn,hcore,hout⟩ := intrinsic_source_data h R hR hP hM
  obtain ⟨K,hK,hN,hgen,hm⟩ := ho
  let := hN
  rw [←hR] at hgen
  have hs : ¬ Group.IsSolvable H := by
    intro hsol
    let := hsol
    exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective K.subtype_injective)
  have ht : ∀ x ∈ ChapterB.minimalParabolicMax R hP,
      V.subgroupOf H ⊓ (V.subgroupOf H).map (MulAut.conj x).toMonoidHom = ⊥ ∨
      (V.subgroupOf H).map (MulAut.conj x).toMonoidHom = V.subgroupOf H := by
    rw [←hM]
    exact Witnesses.BenderPlacement.restrict_TI hVH hTI
  have hw : Nonempty (Witnesses.Solvable.Witness R (ChapterB.minimalParabolicMax R hP)
      (V.subgroupOf H)) := by
    rcases hm with ⟨p,d,hp,hodd,hlarge,hnine,hm⟩ | ⟨p,hp,hodd,hm | hm⟩
    · apply Witnesses.OddLinearTwo.source_original ChapterA.Section02.theoremA_knownSimple
        h.sqtk R hP hs K hK hgen hp hodd hlarge hnine _ (V.subgroupOf H) hVR hn hcore hout
      exact (congrArg (fun N : Subgroup H => ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' N.normalCore)) 2 (p^d)) hM).mp hm
    · apply Witnesses.OddDegreeThree.linear_source_original_of_ti
        R hP hs K hK hgen hp hodd _ (V.subgroupOf H) hVR hn hcore hout ht
      exact (congrArg (fun N : Subgroup H => ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' N.normalCore)) 3 p) hM).mp hm
    · apply Witnesses.OddDegreeThree.unitary_source_original
        R hP hs K hK hgen hp hodd _ (V.subgroupOf H) hVR hn hcore hout
      exact (congrArg (fun N : Subgroup H => ClassicalGroup.IsPSU
        (K.map (QuotientGroup.mk' N.normalCore)) 3 p) hM).mp hm
  obtain ⟨w⟩ := hw
  rw [←hM] at w
  have hne : V ≠ ⊥ := by intro he; exact h.outside_core (he ▸ bot_le)
  exact family_of_dihedral_witness hVH h.elementary hne h.le_sylow R hR w

/-- Actual parameter-one selection for both involution-image and odd
normal-component sources, without solvability or positive weak closure. -/
theorem exists_selected_one_of_dihedral_source
    {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hchar : generalizedFitting H = pCore 2 H)
    (hc : Nat.card (starImage M H V) = 2 ∨ OddNormalComponent H T M)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I), Selected H T M V I 1 i S := by
  have hf : ∃ I : Subgroup G, Family H T M V I 1 ∧
      RankOneAlternative (Star M I) (starImage M I M) 1 := by
    rcases hc with hc | hc
    · exact exists_dihedral_family_of_star_order_two h hc
    · exact exists_dihedral_family_of_odd_normal_component h hc hTI
  obtain ⟨I,f,hr⟩ := hf
  obtain ⟨i,S,s⟩ := exists_selected_of_rank_one_family h hchar f hr hq hTI hNV
  exact ⟨I,i,S,s⟩

/-- Apply the original component catalogue and construct the selected pair
in every solvable or normal odd row. The remaining component is an actual
subgroup of H, with the original core quotient and Sylow supplement. -/
theorem exists_selected_one_or_remaining_component
    {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hchar : generalizedFitting H = pCore 2 H)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    (∃ (I : Subgroup G) (i : I) (S : Sylow 2 I), Selected H T M V I 1 i S) ∨
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ T.subgroupOf H = ⊤ ∧
      (K.Normal →
        let X := K.map (QuotientGroup.mk' (localCore M H))
        ClassificationModels.IsBenderModel X ∨
        (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL X 3 (2^f)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp X 2 (2^f)) ∨
        Nonempty (X ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  classical
  by_cases hsel : ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I), Selected H T M V I 1 i S
  · exact Or.inl hsel
  right
  have hs : ¬ Group.IsSolvable H := fun hsol =>
    hsel (exists_selected_of_solvable h hsol hchar hq hTI hNV)
  obtain ⟨R,hR,hP,hM⟩ := h.minimal
  obtain ⟨K,hK,hquasi,hgen,_⟩ := Structure.source_original_component h.sqtk R hP hs
  refine ⟨K,hK,hquasi,by rwa [←hR],?_⟩
  intro hN
  let := hN
  have hcases := Section06.FixedPointBounds.ParabolicCartan.MarkedModels.source_normal_geometric_cases
    ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) h.sqtk R hP hs K hK hgen
  have hout : ¬ OddNormalComponent H T M := fun ho =>
    hsel (exists_selected_one_of_dihedral_source h hchar (Or.inr ho) hq hTI hNV)
  have hoddFalse :
      ((∃ p d : ℕ, p.Prime ∧ Odd p ∧ 5 < p^d ∧ p^d ≠ 9 ∧
        ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))) 2 (p^d)) ∨
       (∃ p : ℕ, p.Prime ∧ Odd p ∧
         (ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))) 3 p ∨
          ClassicalGroup.IsPSU (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))) 3 p))) → False := by
    intro hm
    apply hout
    refine ⟨K,hK,hN,by rwa [←hR],?_⟩
    have he := congrArg (fun N : Subgroup H =>
      ((∃ p d : ℕ, p.Prime ∧ Odd p ∧ 5 < p^d ∧ p^d ≠ 9 ∧
        ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' N.normalCore)) 2 (p^d)) ∨
       (∃ p : ℕ, p.Prime ∧ Odd p ∧
         (ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' N.normalCore)) 3 p ∨
          ClassicalGroup.IsPSU (K.map (QuotientGroup.mk' N.normalCore)) 3 p)))) hM
    exact he.mpr hm
  have hb :
      let X := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))
      ClassificationModels.IsBenderModel X ∨
      (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL X 3 (2^f)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp X 2 (2^f)) ∨
      Nonempty (X ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
    rcases hcases with h2 | h3 | hb
    · obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hcard,e,_⟩ := h2
      have hlarge : 5 < p^d := by
        rcases (show d=1 ∨ d=2 by omega) with hd | hd
        · subst d; simp only [pow_one] at hmod ⊢; omega
        · subst d; nlinarith
      have hnine : p^d ≠ 9 := by
        intro he
        rcases (show d=1 ∨ d=2 by omega) with hd | hd
        · subst d; simp only [pow_one] at he
          rw [he] at hp
          norm_num at hp
        · subst d; nlinarith
      exact (hoddFalse (Or.inl ⟨p,d,hp,hp.odd_of_ne_two (by omega),hlarge,hnine,
        F,hF,hfin,hcard,⟨e⟩⟩)).elim
    · obtain ⟨p,hp,ho,_,huni | hlin⟩ := h3
      · exact (hoddFalse (Or.inr ⟨p,hp,ho,Or.inr huni.2⟩)).elim
      · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
        exact (hoddFalse (Or.inr ⟨p,hp,ho,Or.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩⟩)).elim
    · exact hb
  have he := congrArg (fun N : Subgroup H =>
    let X := K.map (QuotientGroup.mk' N.normalCore)
    ClassificationModels.IsBenderModel X ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL X 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp X 2 (2^f)) ∨
    Nonempty (X ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) hM
  exact he.mpr hb

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
