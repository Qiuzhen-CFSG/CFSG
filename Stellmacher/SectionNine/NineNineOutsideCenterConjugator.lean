module
public import Stellmacher.SectionNine.NineThreeCenterIrreducible
public import Stellmacher.SectionNine.NineThreeCoreOmega
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration
public import Theory.GroupTheory.CentralIndexTwoComplementTransitive

/-!
# Correcting a terminal neighbor mover outside the center plane

Let I be an elementary subgroup of order eight in the penultimate core,
containing the penultimate center and normalized by its stabilizer. Any
order-two subgroup R of I outside that center is centralized by an element
of the penultimate stabilizer carrying the terminal vertex to the preterminal
vertex.

The exact omega-center theorem identifies the core-fixed subgroup of I with
the four-element center plane. Its irreducibility and index two in I make
the core transitive by conjugation on the complement, by the general central
index-two translation theorem. Choose a generator of R outside the plane,
move the terminal neighbor to the preterminal neighbor, and correct that
mover by a core element restoring the generator. The correction fixes all
neighbors and the order-two subgroup is therefore centralized pointwise.

This proves the outside-center case of the centralizing-conjugator assertion
following Stellmacher (9.9)(3), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. All subgroups and conjugators remain in
the actual ambient group; no alternate module action is introduced.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_outside_center_centralizing_conjugator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (I : Subgroup G) (hIcard : Nat.card I = 8) (hIelem : IsElementaryAbelian 2 I)
    (hZI : ZAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ I)
    (hIQ : I ≤ QAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hPI : GAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
        Subgroup.normalizer (I : Set G))
    (R : Subgroup G) (hRcard : Nat.card R = 2) (hRI : R ≤ I)
    (hRnot : ¬ R ≤ ZAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :
    ∃ y : G,
      y ∈ GAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ∧
      y ∈ Subgroup.centralizer (R : Set G) ∧
      ctx.Γ.act y ctx.criticalPath.a' = ctx.criticalPath.path
        ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ penultimate
  let Q := QAt Γ penultimate
  let Z := ZAt Γ penultimate
  let _ := hIelem
  have hpath : IsCriticalPathOffset Γ cp (cp.length-2) preterminal :=
    ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreAdj := Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hb preterminal hpath)
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment,halign⟩
  have hZcard : Nat.card Z = 4 := (lemma_nine_three_ambient ctx hb penultimate hpenOrbit).2
  have homega : omegaOneCenter Q = Z :=
    nine_three_core_omega_eq_center ctx hb penultimate hpenOrbit
  have hQP : Q ≤ P := by
    rw [show Q = QAt Γ penultimate from rfl,QAt,q,Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := stabilizer_le_normalizer_q Γ penultimate
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ penultimate
  have hZcentral : Z ≤ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    have hzomega : z∈omegaOneCenter Q := by rwa [homega]
    exact Subgroup.mem_centralizer_iff.mpr
      ((mem_omegaOneCenterAmbient_iff Q z).mp hzomega).2.2
  have hfixed : I ⊓ Subgroup.centralizer (Q : Set G) = Z := by
    apply le_antisymm
    · intro z hz
      rw [← homega]
      apply (mem_omegaOneCenterAmbient_iff Q z).mpr
      exact ⟨hIQ hz.1,elemPow_eq_one_of_isElementaryAbelian z hz.1,
        Subgroup.mem_centralizer_iff.mp hz.2⟩
    · exact le_inf hZI hZcentral
  have hindex : Z.relIndex I = 2 := by
    have hh := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hIcard] at hh
    change Z.relIndex I*4=8 at hh
    omega
  obtain ⟨r,hrR,hrZ⟩ := SetLike.not_le_iff_exists.mp hRnot
  have hrI := hRI hrR
  have hrOne : r ≠ 1 := fun heq => hrZ (heq ▸ Z.one_mem)
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity penultimate
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj)
    ((mem_neighborhood_iff_adjacent Γ).mpr hpreAdj)
  let r' := (mover:G)*r*(mover:G)⁻¹
  have hr'I : r'∈I := (Subgroup.mem_normalizer_iff.mp (hPI mover.property) r).mp hrI
  have hr'Z : r'∉Z := fun hh => hrZ
    ((Subgroup.mem_normalizer_iff.mp (hPZ mover.property) r).mpr hh)
  obtain ⟨correction,hcorrection,hcorrect⟩ :=
    Subgroup.conjugation_transitive_complement_of_central_index_two P Q I Z
      hQP hIQ hZI hindex hPQ hPI hPZ hZcentral hfixed
      (nine_three_center_irreducible ctx hb penultimate hpenOrbit)
      r' r hr'I hr'Z hrI hrZ
  let y := correction*(mover:G)
  have hyP : y∈P := P.mul_mem (hQP hcorrection) mover.property
  have hyfix : y*r*y⁻¹=r := by
    change (correction*(mover:G))*r*(correction*(mover:G))⁻¹=r
    calc
      _ = correction*r'*correction⁻¹ := by dsimp only [r']; group
      _ = r := hcorrect
  have hycomm : y*r=r*y := by
    calc
      y*r = (y*r*y⁻¹)*y := by group
      _ = r*y := by rw [hyfix]
  have hycentral : y∈Subgroup.centralizer (R : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    by_cases hzOne : z=1
    · simp only [hzOne,mul_one,one_mul]
    obtain ⟨unique,hunique,huniqueEq⟩ := (Nat.card_eq_two_iff' (1:R)).mp hRcard
    have hzr : (⟨z,hz⟩:R)=⟨r,hrR⟩ :=
      (huniqueEq _ (fun hh => hzOne (congrArg Subtype.val hh))).trans
        (huniqueEq _ (fun hh => hrOne (congrArg Subtype.val hh))).symm
    have hzreq : z=r := congrArg Subtype.val hzr
    rw [hzreq]
    exact hycomm.symm
  have hQterminal : Q ≤ GAt Γ cp.a' :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj) default).2.2
  have hcorrectionFix : Γ.act correction cp.a'=cp.a' :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.a') correction).mp (hQterminal hcorrection)
  refine ⟨y,hyP,hycentral,?_⟩
  change Γ.act (correction*(mover:G)) cp.a'=preterminal
  rw [Γ.act_mul,hcorrectionFix]
  exact hmove

end Stellmacher.SectionNine
