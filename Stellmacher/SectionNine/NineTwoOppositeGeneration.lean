module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionThree.NormalSylowUniqueMaximal

/-!
# Opposite generation at the normalized first edge

A solvable local group has a unique maximal subgroup above its distinguished
Sylow subgroup. The normal-core transfer for a subgroup normalized by that
Sylow subgroup reverses generation by its conjugate and a Sylow overgroup.
Restricting to the local group and mapping back proves the transfer in the
graph ambient group.

Local transitivity then transports the initial core and full edge stabilizer
to the chosen neighbor. No conjugator is assumed to interchange the neighbors,
and the edge stabilizer is not identified with the Sylow subgroup. Hypothesis
Two stays on H. The index and noncontainment assumptions are retained in the
public interface, although this generation argument does not need them.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (9.2), printed
p.48 / PDF p.38 of refs/files/stellmacher-n-group.pdf. The normal-core
prerequisite uses the solvable primitive quotient of (3.3); neither (6.4)
nor (9.2) nor any commutator-center or rank-one conclusion is used here.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem opposite_generation_of_core_transfer
    {Q : Type*} [Group Q] [Finite Q]
    (T M D U : Subgroup Q)
    (hM : IsCoatom M)
    (hunique : ∀ K : Subgroup Q, T ≤ K → K ≠ ⊤ → K ≤ M)
    (hTD : T ≤ D) (hUM : U ≤ M)
    (transfer : ∀ actor : Q, U ≤ M.conjBy actor →
      U ≤ M.normalCore ∨ M.conjBy actor = M)
    (actor : Q) (hgenerate : U.conjBy actor ⊔ D = ⊤) :
    U ⊔ D.conjBy actor = ⊤ := by
  by_cases hDtop : D = ⊤
  · simp only [hDtop, Subgroup.conjBy,
      Subgroup.map_top_of_surjective (MulAut.conj actor).toMonoidHom
        (MulAut.conj actor).surjective, sup_top_eq]
  have hDM := hunique D hTD hDtop
  by_contra hproper
  let K := U.conjBy actor⁻¹ ⊔ D
  have hKconj : K.conjBy actor = U ⊔ D.conjBy actor := by
    change (U.conjBy actor⁻¹ ⊔ D).map (MulAut.conj actor).toMonoidHom = _
    rw [Subgroup.map_sup]
    change (U.conjBy actor⁻¹).conjBy actor ⊔ D.conjBy actor = _
    rw [Subgroup.conjBy_inv']
  have hKproper : K ≠ ⊤ := by
    intro hK
    apply hproper
    rw [← hKconj, hK]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj actor).surjective
  have hKM := hunique K (hTD.trans le_sup_right) hKproper
  have hUconj : U ≤ M.conjBy actor := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
      (show U.conjBy actor⁻¹ ≤ M from le_sup_left.trans hKM)
    change (U.conjBy actor⁻¹).conjBy actor ≤ M.conjBy actor at hmap
    rwa [Subgroup.conjBy_inv'] at hmap
  have hconjUM : U.conjBy actor ≤ M := by
    rcases transfer actor hUconj with hcore | hequal
    · rintro element ⟨member, hmember, rfl⟩
      apply M.normalCore_le
      exact (inferInstance : M.normalCore.Normal).conj_mem member (hcore hmember) actor
    · have hmap := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom) hUM
      change U.conjBy actor ≤ M.conjBy actor at hmap
      rwa [hequal] at hmap
  apply hM.ne_top
  apply top_le_iff.mp
  rw [← hgenerate]
  exact sup_le hconjUM hDM

private theorem map_conjugate
    {G R : Type*} [Group G] [Group R]
    (hom : G →* R) (U : Subgroup G) (actor : G) :
    (U.conjBy actor).map hom = (U.map hom).conjBy (hom actor) := by
  simp only [Subgroup.conjBy, Subgroup.map_map]
  congr 1
  ext element
  simp [MulAut.conj_apply]

private theorem opposite_generation_local
    {G : Type u} [Group G] [Finite G]
    (W P D U : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) W)
    (hsolv : Group.IsSolvable P) (hWD : W ≤ D) (hDP : D ≤ P)
    (hUW : U ≤ W) (hnormal : W ≤ Subgroup.normalizer U)
    (actor : G) (hactor : actor ∈ P)
    (hgenerate : conjugateBy U actor ⊔ D = P) :
    U ⊔ conjugateBy D actor = P := by
  have hWP : W ≤ P := hWD.trans hDP
  have hUP : U ≤ P := hUW.trans hWP
  obtain ⟨sylow, hsylow⟩ := hP.1.2.1
  have hSylow : (sylow : Subgroup P) = W.subgroupOf P := by
    rw [← hsylow, subgroupOf_map_subtype_eq]
  obtain ⟨M, hM, hWM, hunique⟩ := hP.2
  have hTM : (sylow : Subgroup P) ≤ M := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    simpa only [hsylow] using hWM
  have huniq : ∀ M' : Subgroup P, IsCoatom M' →
      (sylow : Subgroup P) ≤ M' → M' = M := by
    intro M' hM' hTM'
    apply hunique M' hM'
    simpa only [hsylow] using Subgroup.map_mono (f := P.subtype) hTM'
  have hbound : ∀ K : Subgroup P, (sylow : Subgroup P) ≤ K → K ≠ ⊤ → K ≤ M := by
    intro K hTK hK
    obtain ⟨M', hM', hKM'⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
    rwa [huniq M' hM' (hTK.trans hKM')] at hKM'
  have hUT : U.subgroupOf P ≤ (sylow : Subgroup P) := by
    rw [hSylow]
    exact Subgroup.subgroupOf_mono P hUW
  have hTD : (sylow : Subgroup P) ≤ D.subgroupOf P := by
    rw [hSylow]
    exact Subgroup.subgroupOf_mono P hWD
  have hTnorm : (sylow : Subgroup P) ≤ Subgroup.normalizer (U.subgroupOf P) := by
    rw [hSylow, ← Subgroup.subgroupOf_normalizer_eq hUP]
    exact Subgroup.subgroupOf_mono P hnormal
  let localActor : P := ⟨actor, hactor⟩
  have hlocalgen : (U.subgroupOf P).conjBy localActor ⊔ D.subgroupOf P = ⊤ := by
    apply Subgroup.map_injective_of_ker_le P.subtype (by simp) (by simp)
    rw [Subgroup.map_sup, map_conjugate, Subgroup.map_subgroupOf_eq_of_le hUP,
      Subgroup.map_subgroupOf_eq_of_le hDP, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hgenerate
  have hresult := opposite_generation_of_core_transfer
    (sylow : Subgroup P) M (D.subgroupOf P) (U.subgroupOf P)
    hM hbound hTD (hUT.trans hTM)
    (SectionThree.normal_sylow_subgroup_le_conjugate_unique_maximal
      hsolv sylow M (U.subgroupOf P) hM hTM huniq hUT hTnorm)
    localActor hlocalgen
  have hmapped := congrArg (fun K : Subgroup P => K.map P.subtype) hresult
  rw [Subgroup.map_sup, map_conjugate, Subgroup.map_subgroupOf_eq_of_le hUP,
    Subgroup.map_subgroupOf_eq_of_le hDP, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmapped
  exact hmapped

public theorem nine_two_opposite_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (m : ctx.Γ.Vertex)
    (hm : m ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (_hindex : QuotientCardEq (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (_hnot : ¬ QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m ≤
      QAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.a ⊔
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ m) =
      GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).2 (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.firstStep ha hm
  have hfix : Γ.act (actor : G) cp.firstStep = cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) (actor : G)).mp actor.property
  have hcore : conjugateBy (q Γ cp.a) ((actor : G)⁻¹) = q Γ m := by
    unfold conjugateBy
    rw [← q_act, hactor]
  have hedge : conjugateBy (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep)
      ((actor : G)⁻¹) = stabilizer Γ cp.firstStep ⊓ stabilizer Γ m := by
    unfold conjugateBy
    rw [Subgroup.map_inf _ _ _ (MulAut.conj ((actor : G)⁻¹)).injective]
    change conjugateBy (stabilizer Γ cp.a) ((actor : G)⁻¹) ⊓
      conjugateBy (stabilizer Γ cp.firstStep) ((actor : G)⁻¹) = _
    rw [← SectionsFiveToSeven.stabilizer_act, ← SectionsFiveToSeven.stabilizer_act,
      hactor, hfix, inf_comm]
  have hlocal := (edge_local_data ctx.sectionSeven Γ cp).2
  have hresult := opposite_generation_local T (stabilizer Γ cp.firstStep)
    (stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep) (q Γ cp.a)
    ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2 cp.S_le_edge_stabilizers
    inf_le_right (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
    (cp.S_le_edge_stabilizers.trans inf_le_left |>.trans
      (stabilizer_le_normalizer_q Γ cp.a))
    ((actor : G)⁻¹) ((stabilizer Γ cp.firstStep).inv_mem actor.property)
    (by simpa only [hcore] using hgenerate)
  simpa only [hedge] using hresult


end Stellmacher.SectionNine
