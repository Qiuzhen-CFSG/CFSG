module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddCatalogue
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddRecognition
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.EvenDegree
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.DerivedModel

/-!
# The original block embedding and complete terminal construction

The original half-Sylow normalizes either original factor. This survives
the literal full central quotient, allowing the complete containing-model
sieve to select rank two. The checked natural-block recognition recovers
PSL₃ over the original field. Actual local placement then supplies A.3.12's
maximal parabolic and full solvable residual, as well as unique containment.

The earlier central-cover lift now proves that the whole center and actual
two-core vanish. Even degrees were already excluded, so this completes
`NaturalTerminalAt` from its exact natural-marking and Hall-placement inputs.
The moving-Hall owner retains those two inputs and final source assembly.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 10.2.3(4), p.747.
-/

public section
open Subgroup Theory.GroupTheory


namespace CFSG.Quasithin.Chapter10.MovingHall
open ChapterC ChapterA.Section03 Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem original_factor_normalized
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (c.original : Set G) := by
  rcases c.original_factor with he | ⟨t,ht,_,he⟩
  · rw [he]
    exact inf_le_right
  rw [he]
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hRT : (R.subgroupOf (T : Subgroup G)).Normal := by
    have he : R.subgroupOf (T : Subgroup G) = (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact normal_of_index_eq_two
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp hRT
  have he : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hTR ht)
  change R ≤ _
  rw [←he,←map_normalizer_eq_of_bijective L (MulAut.conj t).bijective]
  exact map_mono (show R ≤ normalizer (L : Set G) from inf_le_right)

/-- The original half-Sylow normalizes the marked block after passage through
its literal full central quotient. -/
theorem CommonOvercomponent.center_quotient_normalized_block
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) :
    let Q := c.overcomponent ⧸ center c.overcomponent
    let J := (c.original.subgroupOf c.overcomponent).map
      (QuotientGroup.mk' (center c.overcomponent))
    ∃ S : Sylow 2 Q, J ∈ localCComponents S ∧
      (S : Subgroup Q) ≤ normalizer (J : Set Q) := by
  let C := c.overcomponent
  let q := QuotientGroup.mk' (center C)
  obtain ⟨P,hP,hl,_⟩ := c.local_family
  have hnP : (P : Subgroup C) ≤ normalizer (c.original.subgroupOf C : Set C) := by
    rw [hP,←subgroupOf_normalizer_eq c.original_lt.le]
    exact comap_mono (original_factor_normalized D hn c)
  let : Group.IsSolvable q.ker := by
    rw [show q.ker = center C from QuotientGroup.ker_mk' _]
    exact Group.isSolvable_of_comm (fun a b =>
      Subtype.ext (mem_center_iff.mp a.property b).symm)
  exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective _),
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl q,
    (map_mono hnP).trans (le_normalizer_map q)⟩

private theorem rank_two_top {Q : Type*} [Group Q] (h : RankTwoTheoremC Q) :
    RankTwoTheoremC (⊤ : Subgroup Q) := by
  cases h with
  | linear f hf iso => exact .linear f hf (iso.of_mulEquiv topEquiv)
  | symplectic f hf iso => exact .symplectic f hf (iso.of_mulEquiv topEquiv)
  | g2 f hf iso => exact .g2 f hf (iso.of_mulEquiv topEquiv)
  | triality f hf iso => exact .triality f hf (iso.of_mulEquiv topEquiv)
  | ree m hm iso =>
    obtain ⟨d,⟨e⟩⟩ := iso
    exact .ree m hm ⟨d,⟨topEquiv.trans e⟩⟩
  | symplectic_derived iso => exact .symplectic_derived (iso.map fun e => topEquiv.trans e)
  | g2_derived iso => exact .g2_derived (iso.map fun e => topEquiv.trans e)
  | tits iso => exact .tits (iso.map fun e => topEquiv.trans e)

/-- The source catalogue and the original normalized natural block recognize
PSL₃ over the original field, with no A.3.12 embedding premise. -/
theorem CommonOvercomponent.center_quotient_recognition
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) :
    ClassicalGroup.IsPSL (c.overcomponent ⧸ center c.overcomponent) 3 (2^n) := by
  let C := c.overcomponent
  let Q := C ⧸ center C
  let : IsQuasisimple C := c.quasisimple hi
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center C))
  let : IsQuasisimple Q :=
    Chapter1.RadicalNormalizers.Embedding.Alternatives.quasisimple_of_perfect_simple
  have ht : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  obtain ⟨hJ,hz,hc,_,_,_,_,hp,_,_⟩ := c.center_quotient_pair hi
  obtain ⟨S,hl,hnS⟩ := c.center_quotient_normalized_block D hn
  have hr := NaturalEmbedding.rank_two S hl hp hnS hJ hc hz ho
    (c.center_quotient_catalogue hi).2
  exact ChapterC.Section05.NormalizerControl.EmbeddingSelection.NaturalRankTwo.recognize
    S _ ht hl hp hJ hc hz ho (rank_two_top hr)

end CFSG.Quasithin.Chapter10.MovingHall

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.NaturalEmbedding
open ChapterA.Section03 Chapter1.Section02 Matrix.PSL3 Matrix.PSL3.LinearThree

private theorem residual_map {X Y : Type*} [Group X] [Finite X] [Group Y]
    (P : Subgroup X) (e : X ≃* Y) :
    ((solvableResidual P).map P.subtype).map e.toMonoidHom =
      (solvableResidual (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype := by
  let a : P ≃* P.map e.toMonoidHom := e.subgroupMap P
  have he : (solvableResidual P).map a.toMonoidHom =
      solvableResidual (P.map e.toMonoidHom) :=
    map_solvableResidual_eq a.toMonoidHom a.surjective
  rw [←he]
  simp only [map_map]
  rfl

private theorem parabolic_map {X Y : Type*} [Group X] [Finite X] [Group Y]
    {P : Subgroup X} (hP : LieParabolicTwo P) (e : X ≃* Y) :
    LieParabolicTwo (P.map e.toMonoidHom) := by
  obtain ⟨S,hS⟩ := hP
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change normalizer (↑((S : Subgroup X).map e.toMonoidHom) : Set Y) ≤ _
  rw [←map_equiv_normalizer_eq]
  exact map_mono hS

private theorem marked_residual_transport {X Y : Type*}
    [Group X] [Finite X] [Group Y] (e : X ≃* Y) (J P : Subgroup X)
    (hp : LieParabolicTwo P) (hm : IsCoatom P)
    (hr : (solvableResidual P).map P.subtype = J) :
    ∃ R : Subgroup Y, LieParabolicTwo R ∧ IsCoatom R ∧
      (solvableResidual R).map R.subtype = J.map e.toMonoidHom := by
  exact ⟨P.map e.toMonoidHom,parabolic_map hp e,(e.mapSubgroup.isCoatom_iff P).mpr hm,
    (residual_map P e).symm.trans (congrArg (map e.toMonoidHom) hr)⟩

private theorem line_coatom {F : Type*} [Field F] [Finite F] :
    IsCoatom (Matrix.PSL3.LinearThree.lineParabolic F) := by
  open Matrix.PSL3.LinearThree in
  have h := lineParabolicSL_isCoatom F
  rw [←lineParabolic_comap F] at h
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_,?_⟩
  · intro he
    exact h.1 (by rw [he,comap_top])
  · intro P hP hle
    have hp : P.comap (projection F) ≠ ⊤ := by
      intro he
      apply hP
      apply comap_injective (projection_surjective F)
      rw [he,comap_top]
    exact (comap_le_comap_of_surjective (projection_surjective F)).mp
      ((isCoatom_iff_ge_of_le.mp h).2 _ hp (comap_mono hle))

/-- A proper local component in the actual PSL₃ model is the full solvable
residual of a maximal parabolic containing a Sylow normalizer. -/
theorem linear_three_parabolic_residual {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (J : Subgroup X) (hl : J ∈ localCComponents S)
    (hp : J ≠ ⊤) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL X 3 (2^n)) : IsParabolicResidual J ⊤ true := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom
  have hp' : J.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hp
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact he
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.linear_three_local_placement hF hn
    (S.mapSurjective e.surjective) (J.map e.toMonoidHom) hl' hp'
  let a := e.trans (MulAut.conj g)
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 2 ≤ n)
  open Matrix.PSL3.LinearThree in
  have hex : ∃ P : Subgroup PSL(3,F), LieParabolicTwo P ∧ IsCoatom P ∧
      (solvableResidual P).map P.subtype = J.map a.toMonoidHom := by
    have hU : normalizer (unipotent F : Set PSL(3,F)) = borel F :=
      normalizer_unipotent F (by omega) hF
    rcases hg with hg | hg
    · refine ⟨pointParabolic F,⟨unipotentSylow F (by omega) hF,?_⟩,
        pointParabolic_isCoatom F,?_⟩
      · change normalizer (unipotent F : Set PSL(3,F)) ≤ _
        rw [hU,←projective_parabolics_inf F]
        exact inf_le_left
      · rw [ParabolicResiduals.pointParabolic_residual F hlarge]
        rw [show a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl]
        simpa only [map_map] using hg.symm
    · refine ⟨lineParabolic F,⟨unipotentSylow F (by omega) hF,?_⟩,
        line_coatom,?_⟩
      · change normalizer (unipotent F : Set PSL(3,F)) ≤ _
        rw [hU,←projective_parabolics_inf F]
        exact inf_le_right
      · rw [ParabolicResiduals.lineParabolic_residual F hlarge]
        rw [show a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl]
        simpa only [map_map] using hg.symm
  obtain ⟨P,hP,hmax,hres⟩ := hex
  obtain ⟨R,hR,hmaxR,hresR⟩ := marked_residual_transport a.symm
    (J.map a.toMonoidHom) P hP hmax hres
  have hJ : (J.map a.toMonoidHom).map a.symm.toMonoidHom = J := by
    rw [map_map,show a.symm.toMonoidHom.comp a.toMonoidHom = MonoidHom.id X from
      MonoidHom.ext (fun x => a.symm_apply_apply x),map_id]
  rw [hJ] at hresR
  obtain ⟨R',hR',hmaxR',hresR'⟩ := marked_residual_transport
    (topEquiv (G := X)).symm J R hR hmaxR hresR
  refine ⟨R',hR',fun _ => hmaxR',?_⟩
  rw [←map_map,hresR',map_map]
  change J.map ((topEquiv (G := X)).toMonoidHom.comp
    (topEquiv (G := X)).symm.toMonoidHom) = J
  rw [show (topEquiv (G := X)).toMonoidHom.comp
    (topEquiv (G := X)).symm.toMonoidHom = MonoidHom.id X from
      MonoidHom.ext (fun x => rfl),map_id]

end CFSG.Quasithin.Chapter10.MovingHall.NaturalEmbedding

namespace CFSG.Quasithin.Chapter10.MovingHall
open Subgroup Theory.GroupTheory ChapterC ChapterA.Section03 Chapter1.Section02
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original normalized block has the genuine A.3.12 embedding in the
literal full central quotient, including unique containment and its maximal
parabolic's solvable residual. -/
theorem CommonOvercomponent.center_quotient_embedding
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) :
    A312Conclusion ((c.original.subgroupOf c.overcomponent).map
      (QuotientGroup.mk' (center c.overcomponent))) := by
  let C := c.overcomponent
  let Q := C ⧸ center C
  let J := (c.original.subgroupOf C).map (QuotientGroup.mk' (center C))
  let : IsQuasisimple C := c.quasisimple hi
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : IsSimpleGroup (⊤ : Subgroup Q) := (topEquiv (G := Q)).isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup Q) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := Q)).symm.toMonoidHom) (topEquiv (G := Q)).symm.surjective
  have ht : (⊤ : Subgroup Q).IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect .top
  obtain ⟨hJ,hz,hc,_,_,_,_,hp,S,hl,_⟩ := c.center_quotient_pair hi
  have hm := c.center_quotient_recognition D hn ho hi
  refine ⟨⊤,ht,le_top,?_,?_⟩
  · intro K hK hJK
    exact hK.eq_of_le ht le_top
  · exact A312Embedding.two n (by have := hJ.1; omega)
      hJ.2.2.choose_spec.choose_spec.choose_spec.2.1
      (.linear n (by have := hJ.1; omega) (hm.of_mulEquiv topEquiv))
      (NaturalEmbedding.linear_three_parabolic_residual S J hl hp hJ.1 hm)

/-- Complete the terminal geometry for the original blocks: no model or
embedding premise remains. The full center and actual two-core both vanish. -/
theorem CommonOvercomponent.terminal_of_odd_degree
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnorm : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) (hn : 1 < n) (ho : Odd n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) :
    center c.overcomponent = ⊥ ∧ pCore 2 c.overcomponent = ⊥ ∧
      Nonempty (TerminalConfiguration T L (B.map H.subtype) n) :=
  c.terminal_of_odd_embedding hn ho hi (c.center_quotient_embedding D hnorm ho hi)

/-- Original 10.2.3's terminal construction, from its original natural
marking and original Hall placement. Every overcomponent premise is proved. -/
theorem source_natural_terminal : NaturalTerminalAt T := by
  intro L D H B ctx n hn F _ _ _ hF e mark hBB
  obtain ⟨c,hi,_,_⟩ := ctx.common_overcomponent_faithful D n hn hF e mark hBB
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => c.false_of_even_degree he hi)
  exact (c.terminal_of_odd_degree D ctx.nonnormal hn ho hi).2.2

end CFSG.Quasithin.Chapter10.MovingHall

