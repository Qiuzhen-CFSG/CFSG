module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeFamily
public import CFSG.Quasithin.Chapter13.Section07.CoreImage
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SourceLifting
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry

/-!
# The point and plane residues of the original binary-three system

The literal LT action on its natural four-space simultaneously marks the
source line and plane. Their stabilizers pull back to the original
normalizers, proving the point residue and the exact chamber intersection T.

For the H residue, the full source quotient is PSL₃(2). The two actual
Sylow overgroups are proper and are not two-groups: the point residue
controls L₁T, and the source quotient of K₀T is S₃. The binary Bruhat
classification then proves their maximality and exhaustiveness. Canonical
subgroup inclusions give both residue fields of the actual three-vertex
family (LT, K₀L₂T, H), with no additional parabolic premise.

Source: Aschbacher--Smith, 13.7.6(1), printed p.940; the rank-two lattices
and definition of a C₃ system are in I.5, printed pp.419--420.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeResidues
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open Quasithin.I5
open scoped IsMulCommutative

private theorem standard_flag_parabolics :
    RankTwoParabolics S (H1 ⊓ H2) H1 H2 := by
  have h : RankTwoParabolics S borel duadStabilizer synthemeStabilizer :=
    ⟨duadStabilizer_isCoatom,synthemeStabilizer_isCoatom,parabolics_ne,rfl,
      fun U hB hU => (coatoms_over_borel U).mp ⟨hU,hB⟩⟩
  have hh := h.map (MulAut.conj flagRelabel).toMonoidHom
    (MulAut.conj flagRelabel).surjective (by
      rw [(MulAut.conj flagRelabel).toMonoidHom.ker_eq_bot (MulAut.conj flagRelabel).injective]; exact bot_le)
  simpa only [Theory.SpecificGroups.SymmetricSix.borel,
    map_inf _ _ (MulAut.conj flagRelabel).toMonoidHom (MulAut.conj flagRelabel).injective,
    flagRelabel_duad,show synthemeStabilizer = H2 from rfl,flagRelabel_syntheme] using hh

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

include d
theorem source_flag_parabolics
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    RankTwoParabolics ↥(L ⊔ (T : Subgroup G))
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))
      ((normalizer (V₂ : Set G)).subgroupOf (L ⊔ (T : Subgroup G)))
      ((normalizer (V₁ : Set G)).subgroupOf (L ⊔ (T : Subgroup G))) := by
  let A := L ⊔ (T : Subgroup G)
  let f := permutation d
  have hf : Function.Surjective f := nonabelian_permutation_surjective d h hU hV
  let P := (T.subtype (show (T : Subgroup G) ≤ A from le_sup_right)).mapSurjective hf
  have hP : (P : Subgroup S) = ((T : Subgroup G).subgroupOf A).map f := by
    rw [Sylow.coe_mapSurjective,Sylow.coe_subtype]
  obtain ⟨g,hg,hflag⟩ := sylow_flag P
  have hline : image d V₁ = move g canonicalLine := by
    apply (hflag (image d V₁) ?_).1
    · exact image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card
    · intro x hx
      exact (mem_stabilizer_iff_map _ _).mp (image_stable d V₁ d.line_stable (hP ▸ hx))
  have hplane : image d V₂ = move g canonicalPlane := by
    apply (hflag (image d V₂) ?_).2
    · exact image_dim d V₂ (d.plane_le_seed.trans d.seed_le) 2 d.plane_card
    · intro x hx
      exact (mem_stabilizer_iff_map _ _).mp (image_stable d V₂ d.plane_stable (hP ▸ hx))
  have hm := standard_flag_parabolics.map (MulAut.conj g).toMonoidHom
    (MulAut.conj g).surjective (by
      rw [(MulAut.conj g).toMonoidHom.ker_eq_bot (MulAut.conj g).injective]; exact bot_le)
  rw [hg,←flagStabilizer_line,←flagStabilizer_plane,
    ←flagStabilizer_move,←flagStabilizer_move,←hline,←hplane] at hm
  have hc := hm.symm.comap_surjective f hf
  have hb : (P : Subgroup S).comap f = (T : Subgroup G).subgroupOf A := by
    rw [hP,comap_map_eq_self]
    rw [nonabelian_permutation_kernel d h hU hV]
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right)
  have hn (W : Subgroup G) (hW : W ≤ V) :
      (flagStabilizer (image d W)).comap f = (normalizer (W : Set G)).subgroupOf A := by
    ext x
    exact permutation_stabilizes_iff d W hW x
  rw [hb,hn V₂ (d.plane_le_seed.trans d.seed_le),
    hn V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))] at hc
  exact hc

private theorem one_sup_sylow_eq_normalizer :
    sourceOne L T V₁ ⊔ (T : Subgroup G) =
      (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G) := by
  let P := (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)
  have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right d.line_stable
  have hs := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTP))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP,
    ← MonoidHom.range_eq_map,range_subtype] at hs
  exact hs

theorem source_point_parabolics
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    RankTwoParabolics ↥(L ⊔ (T : Subgroup G))
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))
      ((LinearThreeC3Local.middle T L K V₂).subgroupOf (L ⊔ (T : Subgroup G)))
      (H.subgroupOf (L ⊔ (T : Subgroup G))) := by
  have hJ := (LinearThreeC3Local.middle_inf_local (K := K) d).trans
    (LinearThreeC3Local.planeActor_sup_sylow d)
  have hI := (ModelExclusions.original_local_intersection_eq_one_sup_sylow d hH).trans
    (one_sup_sylow_eq_normalizer d)
  have heJ : (LinearThreeC3Local.middle T L K V₂).subgroupOf (L ⊔ (T : Subgroup G)) =
      (normalizer (V₂ : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
    ext x
    exact ⟨fun hx => (hJ.le ⟨hx,x.property⟩).2,
      fun hx => (hJ.ge ⟨x.property,hx⟩).1⟩
  have heH : H.subgroupOf (L ⊔ (T : Subgroup G)) =
      (normalizer (V₁ : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
    ext x
    exact ⟨fun hx => (hI.le ⟨hx,x.property⟩).2,
      fun hx => (hI.ge ⟨x.property,hx⟩).1⟩
  rw [heJ,heH]
  exact source_flag_parabolics d h hU hV

theorem source_chamber_eq_sylow
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    (L ⊔ (T : Subgroup G)) ⊓ LinearThreeC3Local.middle T L K V₂ ⊓ H = (T : Subgroup G) := by
  have hi := (source_point_parabolics (K := K) d hH h hU hV).borel_eq
  apply le_antisymm
  · intro x hx
    exact hi.le (show (⟨x,hx.1.1⟩ : ↥(L ⊔ (T : Subgroup G))) ∈
      (LinearThreeC3Local.middle T L K V₂).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
        H.subgroupOf (L ⊔ (T : Subgroup G)) from ⟨hx.1.2,hx.2⟩)
  · exact le_inf (le_inf le_sup_right LinearThreeC3Local.sylow_le_middle) h.T_le_H

variable [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open Representation

set_option linter.unusedSectionVars false in
theorem source_plane_parabolics
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    RankTwoParabolics H ((T : Subgroup G).subgroupOf H)
      ((L ⊔ (T : Subgroup G)).subgroupOf H)
      ((LinearThreeC3Local.middle T L K V₂).subgroupOf H) := by
  let A := L ⊔ (T : Subgroup G)
  let J := LinearThreeC3Local.middle T L K V₂
  let P := A.subgroupOf H
  let R := J.subgroupOf H
  let S : Sylow 2 H := T.subtype (show (T : Subgroup G) ≤ H from h.T_le_H)
  have hpt := source_point_parabolics (K := K) d hH h hU hV
  have hch := source_chamber_eq_sylow (K := K) d hH h hU hV
  have hmeet : P ⊓ R = (S : Subgroup H) := by
    ext x
    exact ⟨fun hx => hch.le ⟨⟨hx.1,hx.2⟩,x.property⟩,
      fun hx => ⟨(hch.ge hx).1.1,(hch.ge hx).1.2⟩⟩
  have hnLeft : ¬ IsPGroup 2 (H.subgroupOf A) := by
    intro hn
    have he := (T.subtype (show (T : Subgroup G) ≤ A from le_sup_right)).is_maximal'
      hn (by
        change (T : Subgroup G).subgroupOf A ≤ H.subgroupOf A
        rw [←hpt.borel_eq]
        exact inf_le_right)
    have hle : H.subgroupOf A ≤ J.subgroupOf A := by
      rw [he]
      change (T : Subgroup G).subgroupOf A ≤ J.subgroupOf A
      rw [←hpt.borel_eq]
      exact inf_le_left
    have he' : H.subgroupOf A = J.subgroupOf A := by
      by_contra hne
      exact hpt.left_maximal.1 (hpt.right_maximal.2 _ (lt_of_le_of_ne hle hne))
    exact hpt.distinct he'.symm
  have hnP : ¬ IsPGroup 2 P := by
    intro hn
    have hp := (hn.map H.subtype).comap_subtype (K := A)
    have he : (P.map H.subtype).subgroupOf A = H.subgroupOf A := by
      rw [subgroupOf_map_subtype]
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
    exact hnLeft (he ▸ hp)
  have hnR : ¬ IsPGroup 2 R := by
    intro hn
    have he := LinearThreeC3Local.middle_inf_H d hH h hKH hK hL₁K ρ hρ eK hs
    have hC : IsPGroup 2 ↥(LinearThreeC3Local.pointResidual K V₂ ⊔ (T : Subgroup G)) := by
      have hh := hn.map H.subtype
      rw [subgroupOf_map_subtype,he] at hh
      exact hh
    obtain ⟨eC⟩ := (LinearThreeC3Local.point_parabolic d hH h hKH hK hL₁K ρ hρ eK hs).2
    have hh := (hC.to_quotient (pCore 2 _)).of_equiv eC
    obtain ⟨n,hn⟩ := hh.exists_card_eq
    have hd : 3 ∣ 2 ^ n := by
      rw [←hn,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      decide
    have hb := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at hb
  have hP : P ≠ ⊤ := by
    intro he
    apply hH.2.2
    intro x hx
    have hxA : x ∈ A := (show (⟨x,hx⟩ : H) ∈ P from he.symm ▸ mem_top _)
    rw [d.local_normalizer]
    exact (sup_le L.le_normalizer d.normalizes_L) hxA
  have hR : R ≠ ⊤ := by
    intro he
    have hPS : P = (S : Subgroup H) := by simpa only [he,inf_top_eq] using hmeet
    exact hnP (hPS ▸ S.isPGroup')
  obtain ⟨eH,eV,heK,heV⟩ := ModelExclusions.linear_three_full_action_of_one_le
    d hH h hKH hK hL₁K ρ hρ eK hs
  let e := eH.trans ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm.trans Matrix.PSL3Two.equiv)
  exact RankTwoParabolics.of_psl_two_quotient (pCore 2 H) pCore_isPGroup e S P R
    hP hR hnP hnR hmeet

omit [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)] in
theorem source_family_chamber
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    chamberSubgroup (LinearThreeFamily.family (L ⊔ (T : Subgroup G))
      (LinearThreeC3Local.middle T L K V₂) H) =
        (T : Subgroup G).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H) := by
  have hc := source_chamber_eq_sylow (K := K) d hH h hU hV
  ext x
  simp only [chamberSubgroup,mem_iInf]
  constructor
  · intro hx
    exact hc.le ⟨⟨hx 0,hx 1⟩,hx 2⟩
  · intro hx i
    fin_cases i
    · exact (hc.ge hx).1.1
    · exact (hc.ge hx).1.2
    · exact (hc.ge hx).2

omit [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)] in
theorem source_family_point_parabolics
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    let F := LinearThreeFamily.family (L ⊔ (T : Subgroup G))
      (LinearThreeC3Local.middle T L K V₂) H
    RankTwoParabolics (F 0) ((chamberSubgroup F).subgroupOf (F 0))
      (localParabolic F 0 1) (localParabolic F 0 2) := by
  dsimp only
  rw [source_family_chamber d hH h hU hV]
  let e : ((L ⊔ (T : Subgroup G)).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)) ≃*
      ↥(L ⊔ (T : Subgroup G)) := subgroupOfEquivOfLe le_sup_left
  exact (source_point_parabolics d hH h hU hV).comap_surjective e.toMonoidHom e.surjective

set_option linter.unusedSectionVars false in
theorem source_family_plane_parabolics
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    let F := LinearThreeFamily.family (L ⊔ (T : Subgroup G))
      (LinearThreeC3Local.middle T L K V₂) H
    RankTwoParabolics (F 2) ((chamberSubgroup F).subgroupOf (F 2))
      (localParabolic F 2 0) (localParabolic F 2 1) := by
  dsimp only
  rw [source_family_chamber d hH h hU hV]
  let e : (H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)) ≃* H :=
    subgroupOfEquivOfLe le_sup_right
  exact (source_plane_parabolics d hH h hU hV hKH hK hL₁K ρ hρ eK hs).comap_surjective
    e.toMonoidHom e.surjective

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeResidues
