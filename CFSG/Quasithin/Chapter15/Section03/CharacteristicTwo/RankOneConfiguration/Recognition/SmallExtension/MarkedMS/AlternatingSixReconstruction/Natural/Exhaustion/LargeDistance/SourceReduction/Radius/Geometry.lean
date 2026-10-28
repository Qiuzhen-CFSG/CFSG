module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius

/-!
# Midpoint fixedness for the derived A₆ image

An escaping normal subgroup maps onto the actual simple A₆ quotient.
At a critical midpoint, the centralizer of the normal endpoint commutator
contains the initial kernel, which escapes the midpoint kernel. Consequently
the midpoint residual centralizes the commutator. This retains relative
normality, the literal replacement and both possible central moved covers.

Source: MS93 (3.8), printed pp.877--878. The geometric argument is adapted
from the binary Exclusion.Geometry proof, with the actual A₆ quotient in
place of its SL₃(2) source.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h in
/-- A literal embedding of the replacement at every original-group vertex,
including both its core and its residual. -/
theorem local_embedding (a : Vertex d.radical) (ha : color d.radical a = false) :
    ∃ f : d.overgroup →* FreeAmalgam d.radical, Function.Injective f ∧
      f.range = stabilizer d.radical a ∧
      (pCore 2 d.overgroup).map f = Q d.radical a ∧
      (pResidual 2 d.overgroup).map f = Ltilde d.radical a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical),
    (MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical), ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex d.radical g).symm
  · rw [← Subgroup.map_map,← Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    have hh := Q_act d.radical g (alpha d.radical)
    simpa only [alpha,act_mVertex,one_mul] using hh.symm
  · rw [← Subgroup.map_map,← Ltilde_alpha]
    have hh := Ltilde_act d.radical g (alpha d.radical)
    simpa only [alpha,act_mVertex,one_mul] using hh.symm

include h in
/-- The actual local kernels have equal order. -/
theorem Q_card (a : Vertex d.radical) (ha : color d.radical a = false) :
    Nat.card (Q d.radical a) = Nat.card (pCore 2 d.overgroup) := by
  obtain ⟨f,hf,_,hQ,_⟩ := local_embedding h d a ha
  rw [← hQ]
  exact (Nat.card_congr ((pCore 2 d.overgroup).equivMapOfInjective f hf).toEquiv).symm

/-- In the derived-image branch the residual and the core generate the
literal vertex stabilizer. -/
theorem local_generation
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) :
    Ltilde d.radical a ⊔ Q d.radical a = stabilizer d.radical a := by
  have hKQ : pResidual 2 d.overgroup ⊔ pCore 2 d.overgroup = ⊤ := by
    rw [replacement_residual h d]
    apply top_unique
    intro x _
    have hx : projection h e hz hn d x ∈
        (replacementComponent d).map (projection h e hz hn d) := by
      rw [component_image,← himage]
      exact ⟨x,rfl⟩
    have hh : x ∈ ((replacementComponent d).map (projection h e hz hn d)).comap
        (projection h e hz hn d) := hx
    rwa [comap_map_eq,projection_kernel] at hh
  obtain ⟨f,_,hf,hQ,hK⟩ := local_embedding h d a ha
  rw [← hK,← hQ,← Subgroup.map_sup,hKQ,← MonoidHom.range_eq_map,hf]

/-- An escaping normal subgroup contains the residual, using the actual
A₆ image and the original two-core kernel. -/
theorem residual_le_of_normal_not_le
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false)
    (N : Subgroup (FreeAmalgam d.radical)) (hN : N ≤ stabilizer d.radical a)
    (hNorm : (N.subgroupOf (stabilizer d.radical a)).Normal)
    (hout : ¬ N ≤ Q d.radical a) : Ltilde d.radical a ≤ N := by
  obtain ⟨f,hf,hr,hQ,hK⟩ := local_embedding h d a ha
  let A := N.comap f
  let : A.Normal := by
    constructor
    intro x hx g
    change f (g*x*g⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact le_normalizer_iff.mp ((normal_subgroupOf_iff_le_normalizer hN).mp hNorm)
      (f g) (hr ▸ ⟨g,rfl⟩) (f x) hx
  let q : d.overgroup →* alternatingGroup (Fin 6) :=
    (projection h e hz hn d).codRestrict _ (fun m => himage ▸ ⟨m,rfl⟩)
  have hq : Function.Surjective q := by
    intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ (projection h e hz hn d).range := by
      rw [himage]
      exact y.property
    obtain ⟨m,hm⟩ := hy
    exact ⟨m,Subtype.ext hm⟩
  have hk : q.ker = pCore 2 d.overgroup := by
    rw [← projection_kernel h e hz hn d]
    ext m
    exact Subtype.ext_iff
  have hAm : A.map f = N := map_comap_eq_self (hN.trans_eq hr.symm)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : (A.map q).Normal := Normal.map inferInstance q hq
  have htop : A.map q = ⊤ := by
    rcases (inferInstance : (A.map q).Normal).eq_bot_or_eq_top with hzA | ht
    · have hA : A ≤ pCore 2 d.overgroup := by
        rw [← hk]
        exact (Subgroup.map_eq_bot_iff A).mp hzA
      exact False.elim (hout (by
        have hh := map_mono (f := f) hA
        rwa [hAm,hQ] at hh))
    · exact ht
  have hAQ : A ⊔ pCore 2 d.overgroup = ⊤ := by
    have hh := congrArg (Subgroup.comap q) htop
    simpa only [comap_map_eq,hk,comap_top] using hh
  have hres : pResidual 2 d.overgroup ≤ A :=
    le_normal_of_isPPerfect_of_le_sup_pGroup (pResidual 2 d.overgroup) A
      (pCore 2 d.overgroup) (isPPerfect_pResidual 2) pCore_isPGroup (hAQ ▸ le_top)
  have hh := map_mono (f := f) hres
  rwa [hK,hAm] at hh

/-- The initial kernel cannot lie in a critical midpoint kernel. -/
theorem critical_kernel_not_le_midpoint
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h d)
    (a : Vertex d.radical) (ha : color d.radical a = false) (a' : Vertex d.radical)
    (hc : CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha))
    (c : Vertex d.radical) (hcColor : color d.radical c = false)
    (hca' : (cosetGraph d.radical).dist c a' = 2) : ¬ Q d.radical a ≤ Q d.radical c := by
  intro hle
  let := finite_stabilizer d.radical c
  let : Finite (Q d.radical c) := Finite.of_injective
    (inclusion (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1))
      (inclusion_injective _)
  have heq : Q d.radical a = Q d.radical c := eq_of_le_of_card_ge hle (by
    rw [Q_card h d a ha,Q_card h d c hcColor])
  have hZX : Z d.radical a ≤ X d.radical a := (replacementGeometry h d).omega_bound a ha (by
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d)
  have hX : X d.radical a = X d.radical c := congrArg omegaCenter heq
  have hcQ := X_le_Q_of_dist_lt d.radical (replacementGeometry h d)
    (edgeCentralizerCondition h e hz hn d himage) c hcColor a' (by
      rw [(replacementGeometry h d).distance_constant c hcColor,hca']
      change 2 < replacementDistance h d
      rw [fg.distance]
      decide)
  exact hc.2 (hZX.trans (hX.le.trans hcQ))

/-- The normal critical commutator is fixed by the midpoint residual. -/
theorem critical_commutator_le_fixed_midpoint
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h d)
    (a : Vertex d.radical) (ha : color d.radical a = false) (a' : Vertex d.radical)
    (hc : CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha))
    (c : Vertex d.radical) (hcColor : color d.radical c = false)
    (hac : (cosetGraph d.radical).dist a c = 2)
    (hca' : (cosetGraph d.radical).dist c a' = 2) :
    ⁅X d.radical a,X d.radical a'⁆ ≤ fixedCore d.radical c := by
  let A := ⁅X d.radical a,X d.radical a'⁆
  let S := stabilizer d.radical c
  obtain ⟨hAS,hAn⟩ := fg.midpoint a ha a' hc c hac hca'
  have hAX : A ≤ X d.radical a :=
    (Estimates.critical_X_commutator h d e hz hn himage a ha a' hc).1.trans inf_le_left
  have hAQ : A ≤ Q d.radical c := hAX.trans
    (X_le_Q_of_dist_lt d.radical (replacementGeometry h d)
      (edgeCentralizerCondition h e hz hn d himage) a ha c (by
        rw [(replacementGeometry h d).distance_constant a ha,hac]
        change 2 < replacementDistance h d
        rw [fg.distance]
        decide))
  let C := S ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  have hCn : (C.subgroupOf S).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hg),
      mem_normalizer_iff_map_conj_eq.mp
        ((((normal_subgroupOf_iff_le_normalizer hAS).mp hAn).trans
          (normalizer_le_normalizer_centralizer A)) hg)]
  have hQC : Q d.radical a ≤ C := le_inf
    (Q_le_stabilizer_of_dist_le_two a c ha hcColor hac.le)
    ((Q_le_centralizer_X d.radical a).trans (centralizer_le hAX))
  have hLC := residual_le_of_normal_not_le h e hz hn d himage c hcColor C inf_le_left hCn
    (fun hle => critical_kernel_not_le_midpoint h e hz hn d himage fg a ha a' hc c hcColor hca'
      (hQC.trans hle))
  exact le_inf hAQ (le_centralizer_iff.mp (hLC.trans inf_le_right))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
